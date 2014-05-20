Require Import floyd.proofauto.
Require Import MirrorShard.Expr.
Require Import types.
Require Import functions.
Require Import msl.Axioms.

Import ListNotations.

Ltac transl := autorewrite with translate in *; try reflexivity.

Definition funcs funcs' := (our_functions nil) ++ funcs'.


Fixpoint ident_to_expr (i: ident) :=
match i with 
  | xI p' => Func functions.xIp_f [ident_to_expr p']
  | xO p' => Func functions.xOp_f [ident_to_expr p']
  | xH => Func functions.xHp_f []
end. 

Lemma ident_to_expr_correct :
forall i funcs' uenv,
exprD (funcs funcs') uenv [] (ident_to_expr i) ident_tv = Some i.
Proof.
induction i; intros; try reflexivity; simpl in *; rewrite IHi; auto.
Qed.

Hint Rewrite ident_to_expr_correct : translate.

Fixpoint pos_to_expr (p: positive) :=
match p with
  | xI p' => Func functions.xI_f [pos_to_expr p']
  | xO p' => Func functions.xO_f [pos_to_expr p']
  | xH => Func functions.xH_f []
end.

Lemma pos_to_expr_correct :
forall p funcs' uenv,
exprD (funcs funcs') uenv [] (pos_to_expr p) positive_tv = Some p.
Proof.
induction p; intros; try reflexivity; simpl in *; rewrite IHp; auto.
Qed.

Hint Rewrite pos_to_expr_correct : translate.

Definition Z_to_expr (z : Z) :=
match z with
| Zpos p => Func functions.Zpos_f [pos_to_expr p]
| Zneg p => Func functions.Zneg_f [pos_to_expr p]
| Z0 => Func functions.Z0_f []
end.

Lemma Z_to_expr_correct :
forall i funcs' uenv,
exprD (funcs funcs') uenv [] (Z_to_expr i) Z_tv = Some i.
intros.
destruct i; try reflexivity;
simpl in *; rewrite pos_to_expr_correct; auto.
Qed.

Hint Rewrite Z_to_expr_correct : translate.

Definition int32_to_expr (i : int) :=
Func int_repr_f [Z_to_expr (Int.intval i)].

Lemma int_eq_Z : forall z1 z2 p1 p2,
let i1 := Int.mkint z1 p1 in
let i2 := Int.mkint z2 p2 in
Int.intval i1 = Int.intval i2 ->
i1 = i2.
intros. destruct i1, i2; simpl in *. 
destruct H.
assert (intrange = intrange0).
apply proof_irr. destruct H. auto.
Qed.


Lemma range_z_mod : forall intval, -1 < intval < Int.modulus ->
Int.Z_mod_modulus intval = intval.
intros. rewrite Int.Z_mod_modulus_eq.
apply Zmod_small. omega.
Qed.

Lemma  repr_intval : forall i, (Int.repr (Int.intval i)) = i.
Proof.
intros. destruct i. simpl in *.
 unfold Int.repr. 
assert (Int.Z_mod_modulus intval = intval).
apply range_z_mod. auto.
apply int_eq_Z. auto.
Qed.

Hint Rewrite repr_intval : translate.


Lemma int32_to_expr_correct:
forall i funcs' uenv,
exprD (funcs funcs') uenv [] (Func int_repr_f [Z_to_expr (Int.intval i)]) int_tv = Some i.
Proof.
intros.
simpl. autorewrite with translate. auto using repr_intval.
Qed.

Hint Rewrite int32_to_expr_correct : translate.

Definition int64_to_expr (i : int64) :=
Func int_64_repr_f [Z_to_expr (Int64.intval i)].

Lemma int64_eq_Z : forall z1 z2 p1 p2,
let i1 := Int64.mkint z1 p1 in
let i2 := Int64.mkint z2 p2 in
Int64.intval i1 = Int64.intval i2 ->
i1 = i2.
intros. destruct i1, i2; simpl in *. 
destruct H.
assert (intrange = intrange0).
apply proof_irr. destruct H. auto.
Qed.


Lemma range_z_mod64 : forall intval, -1 < intval < Int64.modulus ->
Int64.Z_mod_modulus intval = intval.
intros. rewrite Int64.Z_mod_modulus_eq.
apply Zmod_small. omega.
Qed.

Lemma  repr_intval64 : forall i, (Int64.repr (Int64.intval i)) = i.
Proof.
intros. destruct i. simpl in *.
Transparent Int64.repr.
 unfold Int64.repr. 
assert (Int64.Z_mod_modulus intval = intval).
apply range_z_mod64. auto.
apply int64_eq_Z. auto.
Opaque Int64.repr.
Qed.

Hint Rewrite repr_intval64 : translate.

Lemma int64_to_expr_correct :
forall i funcs' uenv,
exprD (funcs funcs') uenv [] (Func int_64_repr_f [Z_to_expr (Int64.intval i)]) int64_tv = Some i.
Proof. intros.
simpl. autorewrite with translate. auto using repr_intval64.
Qed.

Hint Rewrite int64_to_expr_correct : translate.

Definition optN_to_expr (on : option N) :=
match on with
    Some N0 => Func Some_N_f [Func N0_f []]
  | Some (Npos p) => Func Some_N_f [Func Npos_f [pos_to_expr p]]
  | None => Func None_N_f []
end.

Lemma optN_to_expr_correct :
forall on funcs' uenv, 
exprD (funcs  funcs') uenv [] (optN_to_expr on) option_N_tv = Some on.
Proof.
intros.
destruct on; [ induction n | auto]; simpl; transl.
Qed.

Hint Rewrite optN_to_expr_correct : translate.

Definition bool_to_expr (b: bool) :=
match b with
| true => Func true_f []
| false => Func false_f []
end.

Lemma bool_to_expr_correct :
forall a funcs' uenv,
exprD (funcs funcs') uenv [] (bool_to_expr a) bool_tv = Some a.
Proof.
destruct a; auto. 
Qed.

Hint Rewrite bool_to_expr_correct : translate.

Definition attr_to_expr (a : attr) :=
match a with
{| attr_volatile := b; attr_alignas := a |} =>
Func mk_attr_f [bool_to_expr b; optN_to_expr a]
end.

Lemma attr_to_expr_correct :
forall a funcs' uenv,
exprD (funcs funcs') uenv [] (attr_to_expr a) attr_tv = Some a.
Proof.
intros.  destruct a; simpl; transl.
Qed.

Hint Rewrite attr_to_expr_correct : translate.

Definition intsize_to_expr (sz : intsize) :=
match sz with
I8 => Func I8_f []
| I16 => Func I16_f []
| I32 => Func I32_f [] 
| IBool => Func IBool_f []
end.

Lemma intsize_to_expr_correct :
forall i funcs' uenv,
exprD (funcs funcs') uenv [] (intsize_to_expr i) intsize_tv = Some i.
induction i; auto.
Qed.

Hint Rewrite intsize_to_expr_correct : translate.

Definition floatsize_to_expr (sz: floatsize) :=
match sz with
F32 => Func F32_f []
| F64 => Func F64_f []
end.

Lemma floatsize_to_expr_correct :
forall i funcs' uenv,
exprD (funcs funcs') uenv [] (floatsize_to_expr i) floatsize_tv = Some i.
induction i; auto.
Qed.

Hint Rewrite floatsize_to_expr_correct : translate.

Definition signedness_to_expr (s: signedness) :=
match s with
  Signed => Func signed_f [] 
| Unsigned => Func unsigned_f []
end.

Lemma sign_to_expr_correct :
forall s funcs' uenv,
exprD (funcs funcs') uenv [] (signedness_to_expr s) signedness_tv = Some s.
destruct s; auto.
Qed.

Hint Rewrite sign_to_expr_correct : translate.


Fixpoint type_to_expr (ty : Ctypes.type) :=
match ty with
  | Tvoid => Func functions.Tvoid_f []
  | Tint sz sn attr => Func functions.Tint_f [intsize_to_expr sz; signedness_to_expr sn; attr_to_expr attr]
  | Tlong sg attr => Func functions.Tlong_f [signedness_to_expr sg; attr_to_expr attr]
  | Tfloat fs attr => Func functions.Tfloat_f [floatsize_to_expr fs; attr_to_expr attr] 
  | Tpointer t attr => Func functions.Tpointer_f [type_to_expr t; attr_to_expr attr] 
  | Tarray t z attr => Func functions.Tarray_f [type_to_expr t; Z_to_expr z; attr_to_expr attr] 
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

Lemma type_to_expr_correct :
forall ty funcs' uenv,
exprD (funcs  funcs') uenv [] (type_to_expr ty ) c_type_tv = Some ty
with
typelist_to_expr_correct :
forall tl funcs' uenv, 
exprD (funcs funcs') uenv [] (typelist_to_expr tl) typelist_tv = Some tl
with
fieldlist_to_expr_correct :
forall fl funcs' uenv, 
exprD (funcs funcs') uenv [] (fieldlist_to_expr fl) fieldlist_tv = Some fl.
intros.
destruct ty; try solve [repeat (transl; simpl); try rewrite type_to_expr_correct; auto].
simpl. rewrite typelist_to_expr_correct; auto. rewrite type_to_expr_correct; auto.
simpl; transl. rewrite fieldlist_to_expr_correct; auto.
simpl; transl. rewrite fieldlist_to_expr_correct; auto.
intros.
destruct tl; repeat (simpl; transl). rewrite type_to_expr_correct; auto.
rewrite typelist_to_expr_correct; auto.
intros.
destruct fl; repeat (simpl; transl).
rewrite type_to_expr_correct; auto.
rewrite fieldlist_to_expr_correct; auto.
Qed.

Hint Rewrite type_to_expr_correct : translate.
Hint Rewrite typelist_to_expr_correct : translate.
Hint Rewrite fieldlist_to_expr_correct : translate.

Definition unop_to_expr o :=
match o with
    Onotbool => Func Onotbool_f []
  | Onotint => Func Onotint_f []
  | Oneg => Func Oneg_f []
end.

Lemma unop_to_expr_correct :
forall o funcs' uenv,
exprD (funcs funcs') uenv [] (unop_to_expr o) unary_operation_tv = Some o.
destruct o; auto.
Qed.

Hint Rewrite unop_to_expr_correct : translate.

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

Lemma binop_to_expr_correct :
forall o funcs' uenv,
exprD (funcs funcs') uenv [] (binop_to_expr o) binary_operation_tv = Some o.
destruct o; auto.
Qed.

Hint Rewrite binop_to_expr_correct : translate.
Definition float_to_expr (f:float) := Func functions.O_f []. (*Placeholder, deal with floats later*)

