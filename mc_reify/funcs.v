Require Import MirrorCore.syms.SymEnv.
Require Import MirrorCore.Lambda.ExprCore.
Require Import floyd.proofauto.
Require Import ExtLib.Core.RelDec.
Require Import MirrorCore.TypesI.
Require Import ExtLib.Tactics.
Require Import ExtLib.Data.Fun.
Require Import progs.list_dt.
Require Import types.

Inductive const :=
| N : nat -> const
| Z : Z -> const
| Pos : positive -> const
| Ctype : type -> const
| Cexpr : expr -> const
| Comparison : comparison -> const.

Definition typeof_const (c : const) : typ :=
 match c with
| N _ => tynat
| Z _ => tyZ
| Pos _ => typositive
| Ctype _ => tyc_type
| Cexpr _ => tyc_expr
| Comparison _ => tycomparison
end.

Definition constD (c : const)
: typD (typeof_const c) :=
match c with
| N c | Z c | Pos c | Ctype c | Cexpr c | Comparison c
                                          => c
end.

Require Import ExtLib.Data.Positive.
Require Import ExtLib.Data.Z.

(*Instance RelDec_type_eq : RelDec (@eq type) :=
{ rel_dec := eqb_type }.

Instance RelDec_const_eq : RelDec (@eq const) :=
{ rel_dec := fun (a b : const) =>
               match a , b with
| N c1,  N c2 | Z c1,  Z c2 | Pos c1,  Pos c2 | Ctype c1,  Ctype c2
| Cexpr c1,  Cexpr c2 | Comparison c1,  Comparison c2 => c1 ?[ eq ] c2
| _, _ => false
end}. Set Printing All.*)



Inductive z_op :=
| fZ_lt
| fZ_le
| fZ_gt
| fZ_ge
| fZ_add
| fZ_sub
| fZ_mul
| fZ_div
| fZ_mod
| fZ_max
| fZ_opp.

Definition typeof_z_op z : typ :=
match z with
| fZ_lt
| fZ_le
| fZ_gt
| fZ_ge => (tyArr tyZ (tyArr tyZ typrop))
| fZ_add
| fZ_sub
| fZ_mul
| fZ_div
| fZ_mod
| fZ_max => (tyArr tyZ (tyArr tyZ tyZ))
| fZ_opp => (tyArr tyZ tyZ)
end.

Definition z_opD (z : z_op) : typD  (typeof_z_op z) :=
match z with
| fZ_lt => Z.lt
| fZ_le => Z.le
| fZ_gt => Z.gt
| fZ_ge => Z.ge
| fZ_add => Z.add
| fZ_sub => Z.sub
| fZ_mul => Z.mul
| fZ_div => Z.div
| fZ_mod => Zmod
| fZ_max => Z.max
| fZ_opp => Z.opp
end.

(*Instance RelDec_func_eq : RelDec (@eq func) :=
{ rel_dec := fun (a b : func) =>
               match a , b with
                 | Plus , Plus => true*)

Inductive int_op :=
| fint_add
| fint_lt
| fint_ltu
| fint_mul
| fint_neg
| fint_sub
| fint_cmp
| fint_cmpu
| fint_repr
| fint_signed
| fint_unsigned
| fint_max_unsigned
| fint64_repr.

Definition typeof_int_op i : typ :=
match i with
| fint_lt
| fint_ltu => tyArr tyint (tyArr tyint tybool)
| fint_mul
| fint_sub
| fint_add => tyArr tyint (tyArr tyint tyint)
| fint_neg => tyArr tyint tyint
| fint_cmp
| fint_cmpu => tyArr tycomparison (tyArr tyint (tyArr tyint tybool))
| fint_repr => tyArr tyZ tyint
| fint_signed
| fint_unsigned  => tyArr tyint tyZ
| fint_max_unsigned => tyZ
| fint64_repr => tyArr tyZ tyint64
end.

Definition int_opD (i : int_op): typD  (typeof_int_op i) :=
match i with
| fint_add => Int.add
| fint_lt => Int.lt
| fint_ltu => Int.ltu
| fint_mul => Int.mul
| fint_neg => Int.neg
| fint_sub => Int.sub
| fint_cmp => Int.cmp
| fint_cmpu => Int.cmpu
| fint_repr => Int.repr
| fint_signed => Int.signed
| fint_unsigned => Int.unsigned
| fint_max_unsigned => Int.max_unsigned
| fint64_repr => Int64.repr
end.


Inductive values :=
| fVint
| fVfloat
| fVlong
| fVptr
| fVundef.

Definition typeof_value (v : values) :=
match v with
| fVint => tyArr tyint tyval
| fVfloat => tyArr tyfloat tyval
| fVlong => tyArr tyint64 tyval
| fVptr => tyArr typositive (tyArr tyint tyval)
| fVundef => tyval
end.

Definition valueD  (v : values): typD  (typeof_value v) :=
match v with
| fVint => Vint
| fVfloat => Vfloat
| fVlong => Vlong
| fVptr => Vptr
| fVundef => Vundef
end.


Inductive eval :=
| feval_cast
| fderef_noload
| feval_field
| feval_binop
| feval_unop
| feval_id.

Definition typeof_eval (e : eval) :=
 match e with
| feval_cast => tyArr tyc_type (tyArr tyc_type (tyArr tyval tyval))
| fderef_noload => tyArr tyc_type (tyArr tyval tyval)
| feval_field => tyArr tyc_type (tyArr tyident (tyArr tyval tyval))
| feval_binop => tyArr tybinary_operation (tyArr tyc_type (tyArr tyc_type (tyArr tyval (tyArr tyval tyval))))
| feval_unop => tyArr tyunary_operation (tyArr tyc_type (tyArr tyval tyval))
| feval_id => tyArr tyident (tyArr tyenviron tyval)
end.

Definition evalD  (e : eval) : typD  (typeof_eval e) :=
match e with
| feval_id => eval_id
| feval_cast => eval_cast
| fderef_noload => deref_noload
| feval_field => eval_field
| feval_binop => eval_binop
| feval_unop => eval_unop
end.


(*TODO: classify these better*)
Inductive other :=
| ftwo_power_nat
| fforce_ptr
| fand
| falign
| ftyped_true
| feq : typ -> other
.

Definition typeof_other (o : other) :=
match o with
| ftwo_power_nat => tyArr tynat tyZ
| fforce_ptr  => tyArr tyval tyval
| fand => tyArr typrop (tyArr typrop typrop)
| falign => tyArr tyZ (tyArr tyZ tyZ)
| ftyped_true => tyArr tyc_type (tyArr tyval typrop)
| feq t => tyArr t (tyArr t typrop) 
end.

Definition otherD  (o : other) : typD  (typeof_other o) :=
match o with
| ftwo_power_nat => (two_power_nat : typD (typeof_other ftwo_power_nat))
| fforce_ptr => force_ptr
| fand => and
| falign => align
| ftyped_true => typed_true
| feq t => @eq (typD t) 
end.

Inductive lst :=
| fnil : typ -> lst
| fmap : typ -> typ -> lst
| ffold_right : typ -> typ -> lst
| ffold_left : typ -> typ -> lst
| fcons : typ -> lst
| fappend : typ -> lst.

Definition typeof_lst (l : lst) :=
match l with
| fmap a b => tyArr (tyArr a b) (tyArr (tylist a) (tylist b))
| fnil a => (tylist a)
| ffold_right a b => tyArr (tyArr b (tyArr a a)) (tyArr a (tyArr (tylist b) a))
| ffold_left a b => tyArr (tyArr a (tyArr b a)) (tyArr (tylist b) (tyArr a a))
| fcons a => tyArr a (tyArr (tylist a) (tylist a))
| fappend a => tyArr (tylist a) (tyArr (tylist a) (tylist a))
end.

Definition lstD (l : lst) : typD (typeof_lst l) :=
match l with
| fmap t1 t2 => @map (typD  t1) (typD  t2)
| fnil t => (@nil (typD t) : typD (typeof_lst (fnil t)))
| ffold_right a b => @fold_right (typD a) (typD b)
| ffold_left a b => @fold_left (typD a) (typD b)
| fcons a => @cons (typD a)
| fappend a => @app (typD a)
end.

Inductive sep :=
| fstar
| fandp
| forp
| flocal
| fprop
| fderives
| femp
| fdata_at : type -> sep
| ffield_at : type -> list ident -> sep
| flseg : forall (t: type) (i : ident), listspec t i -> sep
| ftt
| fff
| fexp : typ -> sep
| fallp : typ -> sep
. 


Fixpoint reptyp (ty: type) : typ :=
  match ty with
  | Tvoid => tyunit
  | Tint _ _ _ => tyval
  | Tlong _ _ => tyval
  | Tfloat _ _ => tyval
  | Tpointer t1 a => tyval
  | Tarray t1 sz a => tylist (reptyp t1)
  | Tfunction t1 t2 _ => tyunit
  | Tstruct id fld a => reptyp_structlist fld
  | Tunion id fld a => reptyp_unionlist fld
  | Tcomp_ptr id a => tyval
  end
with reptyp_structlist (fld: fieldlist) : typ :=
  match fld with
  | Fnil => tyunit
  | Fcons id ty fld' => 
    if is_Fnil fld' 
      then reptyp ty
      else typrod (reptyp ty) (reptyp_structlist fld')
  end
with reptyp_unionlist (fld: fieldlist) : typ :=
  match fld with
  | Fnil => tyunit
  | Fcons id ty fld' => 
    if is_Fnil fld' 
      then reptyp ty
      else tysum (reptyp ty) (reptyp_unionlist fld')
  end.

 
Definition typeof_sep (s : sep) : typ :=
match s with
| fdata_at t => tyArr tyshare (tyArr (reptyp t) (tyArr tyval tympred))
| ffield_at t ids => tyArr tyshare (tyArr (reptyp (nested_field_type2 t ids)) (tyArr tyval tympred))
| flseg t i l => tyArr tyshare (tyArr (tylist (reptyp_structlist (@all_but_link i (list_fields)))) 
                                      (tyArr tyval (tyArr tyval tympred)))
| fstar 
| fandp
| forp => tyArr tympred (tyArr tympred tympred)
| flocal => tyArr (tyArr tyenviron typrop) (tyArr tyenviron tympred) 
| fprop => tyArr typrop tympred
| fderives => tyArr tympred (tyArr tympred typrop)
| femp | ftt | fff => tympred
| fexp t => tyArr (tyArr t tympred) tympred 
| fallp t => tyArr (tyArr t tympred) tympred
end.

Fixpoint reptyp_reptype  ty {struct ty} : typD  (reptyp ty) -> reptype ty :=
  match ty as ty0 return (typD  (reptyp ty0) -> reptype ty0) with
    | Tvoid => fun x : unit => x
    | Tint i s a => fun x : val => x
    | Tlong s a => fun x : val => x
    | Tfloat f a => fun x : val => x
    | Tpointer t a => fun x : val => x
    | Tarray t z a => map (reptyp_reptype  t)
    | Tfunction t t0 c => fun x : unit => x
    | Tstruct i f a => reptyp_structlist_reptype  f
    | Tunion i f a => reptyp_unionlist_reptype  f
    | Tcomp_ptr i a => fun x : val => x
  end
with reptyp_structlist_reptype  fl {struct fl} : typD  (reptyp_structlist fl) -> reptype_structlist fl :=
  match
    fl as fl0
    return (typD  (reptyp_structlist fl0) -> reptype_structlist fl0)
  with
    | Fnil => fun x : typD  (reptyp_structlist Fnil) => x
    | Fcons i t fl0 =>
      let b := is_Fnil fl0 in
      if b as b0
         return
         (typD 
               (if b0
                then reptyp t
                else typrod (reptyp t) (reptyp_structlist fl0)) ->
          if b0
          then reptype t
          else (reptype t * reptype_structlist fl0)%type)
      then reptyp_reptype  t
      else
        fun x : typD  (reptyp t) * typD  (reptyp_structlist fl0) =>
          (reptyp_reptype  t (fst x),
           reptyp_structlist_reptype  fl0 (snd x))
  end
with reptyp_unionlist_reptype  fl {struct fl} : typD  (reptyp_unionlist fl) -> reptype_unionlist fl :=
match
     fl as fl0
     return (typD  (reptyp_unionlist fl0) -> reptype_unionlist fl0)
   with
   | Fnil => fun x : typD  (reptyp_unionlist Fnil) => x
   | Fcons i t fl0 =>
       let b := is_Fnil fl0 in
       if b as b0
        return
          (typD 
             (if b0
              then reptyp t
              else tysum (reptyp t) (reptyp_unionlist fl0)) ->
           if b0 then reptype t else (reptype t + reptype_unionlist fl0)%type)
       then reptyp_reptype  t
       else
        fun x : typD  (reptyp t) + typD  (reptyp_unionlist fl0) =>
        match x with
        | inl y => inl (reptyp_reptype  t y)
        | inr y => inr (reptyp_unionlist_reptype  fl0 y)
        end
   end.

Definition sepD  (s : sep) : typD  (typeof_sep s).
refine
match s with
| fstar => sepcon
| fandp => andp
| forp => orp
| flocal => local
| fprop => prop
| fderives => derives
| femp => emp
| ftt => TT
| fff => FF
| fexp t => (@exp mpred Nveric (typD t))
| fallp t => (@allp mpred Nveric (typD t))
| fdata_at ty => _ (* fun sh (t : reptype ty) v => data_at sh ty t v *)
| ffield_at t ids => _
| flseg t id ls => _
end. 
{ simpl. intros sh rt v.
  exact (data_at sh ty (reptyp_reptype  _ rt) v). }
{ simpl. intros sh ty v.
  exact (field_at sh t ids (reptyp_reptype  _ ty) v). }
{ simpl.
  intros sh lf v1 v2.
  exact (@lseg t id ls sh (List.map (reptyp_structlist_reptype  _) lf) v1 v2). }
Defined.


Inductive triple :=
| fsemax
| fstatement : statement -> triple
| fretassert : ret_assert -> triple
| ftycontext : tycontext -> triple
| fPROPx
| fLOCALx
| fSEPx
.

Check PROPx.
Check LOCALx.
Check SEPx.

Definition typeof_triple (t : triple) :=
match t with
| fsemax => tyArr tyOracleKind (tyArr tytycontext (tyArr (tyArr tyenviron tympred) (tyArr tystatement (tyArr tyret_assert typrop))))
| fstatement s => tystatement
| fretassert r => tyret_assert
| ftycontext d => tytycontext
| fPROPx => tyArr (tylist typrop) (tyArr (tyArr tyenviron tympred) (tyArr tyenviron tympred))
| fLOCALx => tyArr (tylist (tyArr tyenviron typrop)) (tyArr (tyArr tyenviron tympred) (tyArr tyenviron tympred))
| fSEPx => tyArr (tylist (tyArr tyenviron tympred)) (tyArr tyenviron tympred)
end.

Definition tripleD (t : triple) : typD (typeof_triple t) :=
match t with
| fsemax => (@semax : typD (typeof_triple fsemax))
| fstatement s | fretassert s | ftycontext s => s
| fPROPx => PROPx
| fLOCALx => LOCALx
| FSEPx => SEPx
end.

Inductive func' :=
| Const : const -> func'
| Zop : z_op -> func'
| Intop : int_op -> func'
| Value : values -> func'
| Eval_f : eval -> func'
| Other : other -> func'
| Sep : sep -> func'
| Lst : lst -> func'
| Triple : triple -> func'.

Definition func := sum SymEnv.func func'.

Definition typeof_func (f: func') : typ :=
match f with
| Const c => typeof_const c
| Zop z => typeof_z_op z
| Intop i => typeof_int_op i
| Value v => typeof_value v
| Eval_f e => typeof_eval e
| Other o => typeof_other o
| Sep s => typeof_sep s
| Lst l => typeof_lst l
| Triple t => typeof_triple t
end.


Definition funcD  (f : func') : typD  (typeof_func f) :=
match f with
| Const c => constD  c
| Zop z => z_opD  z
| Intop i => int_opD  i
| Value v => valueD  v
| Eval_f e => evalD  e
| Other o => otherD  o
| Sep s => sepD  s
| Lst l => lstD l
| Triple t => tripleD t
end.