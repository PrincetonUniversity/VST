Require Import MirrorCore.syms.SymEnv.
Require Import MirrorCore.Lambda.ExprCore.
Require Import ExtLib.Core.RelDec.
Require Import MirrorCore.TypesI.
Require Import ExtLib.Tactics.
Require Import ExtLib.Data.Fun.
(*Require Import VST.progs.list_dt.*)
Require Import VST.floyd_funcs.
Require Import mc_reify.types.
Require Import mc_reify.bool_funcs.
Require Import MirrorCharge.ModularFunc.ILogicFunc.
Require Import MirrorCharge.ModularFunc.BILogicFunc.
Require Import VST.floyd.local2ptree.
Require Import mc_reify.local2list.


Inductive const :=
| fN : nat -> const
| fZ : Z -> const
| fint : int -> const
| fint64 : int64 -> const
| fPos : positive -> const
| fident : ident -> const
| fCtype : type -> const
| fCexpr : expr -> const
| fComparison : comparison -> const
| fbool : bool -> const
| ffloat : float -> const
| ffloat32 : float32 -> const
| fenv : type_id_env -> const
| fllrr : LLRR -> const
.

Definition typeof_const (c : const) : typ :=
 match c with
| fN _ => tynat
| fZ _ => tyZ
| fPos _ => typositive
| fident _ => tyident
| fCtype _ => tyc_type
| fCexpr _ => tyc_expr
| fComparison _ => tycomparison
| fbool _ => tybool
| fint _ => tyint
| fint64 _ => tyint64
| ffloat _ => tyfloat
| ffloat32 _ => tyfloat32
| fenv _ => tytype_id_env
| fllrr _ => tyllrr
end.

Definition constD (c : const)
: typD (typeof_const c) :=
match c with
| fN c | fZ c | fPos c | fident c | fCtype c | fCexpr c | fComparison c | fbool c | fint c
| fint64 c | ffloat c | ffloat32 c | fenv c | fllrr c
                                          => c
end.

(*
Instance RelDec_type_eq : RelDec (@eq type) :=
{ rel_dec := eqb_type }.

Instance RelDec_const_eq : RelDec (@eq const) :=
{ rel_dec := fun (a b : const) =>
               match a , b with
| N c1,  N c2 | Z c1,  Z c2 | Pos c1,  Pos c2 | Ctype c1,  Ctype c2
| Cexpr c1,  Cexpr c2 | Comparison c1,  Comparison c2 => c1 ?[ eq ] c2
| _, _ => false
end}.*)



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
| fZ_land
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
| fZ_land
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
| fZ_land => Z.land
| fZ_max => Z.max
| fZ_opp => Z.opp
end.

(*Instance RelDec_func_eq : RelDec (@eq func) :=
{ rel_dec := fun (a b : func) =>
               match a , b with
                 | Plus , Plus => true*)

Inductive int_op :=
| fint_add
| fint_and
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
| fint_and => tyArr tyint (tyArr tyint tyint)
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
| fint_and => Int.and
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
| fVundef
| fVsingle.

Definition typeof_value (v : values) :=
match v with
| fVint => tyArr tyint tyval
| fVfloat => tyArr tyfloat tyval
| fVlong => tyArr tyint64 tyval
| fVptr => tyArr typositive (tyArr tyint tyval)
| fVsingle => tyArr tyfloat32 tyval
| fVundef => tyval
end.

Definition valueD  (v : values): typD  (typeof_value v) :=
match v with
| fVint => Vint
| fVfloat => Vfloat
| fVlong => Vlong
| fVptr => Vptr
| fVsingle => Vsingle
| fVundef => Vundef
end.

Inductive eval :=
| feval_cast : type -> type -> eval
| fderef_noload : type -> eval
| feval_field : type -> ident -> eval
| feval_binop : binary_operation -> type -> type -> eval
| feval_unop : unary_operation -> type -> eval
| feval_id : ident -> eval.

Definition typeof_eval (e : eval) :=
 match e with
| feval_cast _ _ => (tyArr tyval tyval)
| fderef_noload _ => (tyArr tyval tyval)
| feval_field _ _ => (tyArr tyval tyval)
| feval_binop _ _ _=> (tyArr tyval (tyArr tyval tyval))
| feval_unop _ _ => (tyArr tyval tyval)
| feval_id _  => (tyArr tyenviron tyval)
end.

Definition evalD  (e : eval) : typD  (typeof_eval e) :=
match e with
| feval_id id => eval_id id
| feval_cast t1 t2 => eval_cast t1 t2
| fderef_noload t => deref_noload t
| feval_field t id => eval_field t id
| feval_binop op t1 t2 => eval_binop op t1 t2
| feval_unop op t => eval_unop op t
end.


(*TODO: classify these better*)
Inductive other :=
| ftwo_power_nat
| fforce_ptr
| fand
| falign
| ftyped_true
| feq : typ -> other
| fnone : typ -> other
| fsome : typ -> other
| ftypeof
| fTrue
| fFalse
.

Definition typeof_other (o : other) :=
match o with
| ftwo_power_nat => tyArr tynat tyZ
| fforce_ptr  => tyArr tyval tyval
| fand => tyArr typrop (tyArr typrop typrop)
| falign => tyArr tyZ (tyArr tyZ tyZ)
| ftyped_true => tyArr tyc_type (tyArr tyval typrop)
| feq t => tyArr t (tyArr t typrop)
| fnone t => tyoption t
| fsome t => tyArr t (tyoption t)
| ftypeof => tyArr tyc_expr tyc_type
| fTrue | fFalse => typrop
end.

Definition otherD  (o : other) : typD  (typeof_other o) :=
match o with
| ftwo_power_nat => (two_power_nat : typD (typeof_other ftwo_power_nat))
| fforce_ptr => force_ptr
| fand => and
| falign => align
| ftyped_true => typed_true
| feq t => @eq (typD t)
| fsome t => @Some (typD t)
| fnone t => @None (typD t)
| ftypeof => typeof
| fTrue => True
| fFalse => False
end.

Inductive data :=
| fnil : typ -> data
| fmap : typ -> typ -> data
| ffold_right : typ -> typ -> data
| ffold_left : typ -> typ -> data
| fcons : typ -> data
| fappend : typ -> data
| fnth_error : typ -> nat -> data
| freplace_nth : typ -> nat -> data
| fpair : typ -> typ -> data
| fget : typ -> positive -> data
| fset : typ -> positive -> data
| fleaf : typ -> data
| fnode : typ -> data
| fempty : typ -> data
.

Definition typeof_data (l : data) :=
match l with
| fmap a b => tyArr (tyArr a b) (tyArr (tylist a) (tylist b))
| fnil a => (tylist a)
| ffold_right a b => tyArr (tyArr b (tyArr a a)) (tyArr a (tyArr (tylist b) a))
| ffold_left a b => tyArr (tyArr a (tyArr b a)) (tyArr (tylist b) (tyArr a a))
| fcons a => tyArr a (tyArr (tylist a) (tylist a))
| fappend a => tyArr (tylist a) (tyArr (tylist a) (tylist a))
| fnth_error a _ => tyArr (tylist a) (tyoption a)
| freplace_nth a _ => tyArr (tylist a) (tyArr a (tylist a))
| fpair t1 t2 => tyArr t1 (tyArr t2 (typrod t1 t2))
| fleaf t => typtree t
| fnode t => tyArr (typtree t) (tyArr (tyoption t) (tyArr (typtree t) (typtree t)))
| fset t _ => tyArr t (tyArr (typtree t) (typtree t))
| fget t _ => (tyArr (typtree t) (tyoption t))
| fempty t => typtree t
end.

Definition dataD (l : data) : typD (typeof_data l) :=
match l with
| fmap t1 t2 => @map (typD  t1) (typD  t2)
| fnil t => (@nil (typD t) : typD (typeof_data (fnil t)))
| ffold_right a b => @fold_right (typD a) (typD b)
| ffold_left a b => @fold_left (typD a) (typD b)
| fcons a => @cons (typD a)
| fappend a => @app (typD a)
| fnth_error a n => fun l => @nth_error (typD a) l n
| freplace_nth a n => @canon.replace_nth (typD a) n
| fpair a b => ((@pair (typD a) (typD b)) : typD (typeof_data (fpair a b)))
| fleaf t => @PTree.Leaf (typD t)
| fnode t => @PTree.Node (typD t)
| fset t p => @PTree.set (typD t) p
| fget t p => @PTree.get (typD t) p
| fempty t => @PTree.empty (typD t)
end.

Inductive sep :=
| flocal
| fprop
| fdata_at : type -> sep
| ffield_at : type -> list gfield -> sep
| fproj_val : type -> sep
| fupd_val : type -> sep
(*| flseg : forall (t: type) (i : ident), listspec t i -> sep*)
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
| ffield_at t gfs => tyArr tyshare (tyArr (reptyp (nested_field_type2 t gfs)) (tyArr tyval tympred))
(*| flseg t i l => tyArr tyshare (tyArr (tylist (reptyp_structlist (@all_but_link i (list_fields))))
                                      (tyArr tyval (tyArr tyval tympred)))*)
| flocal => tyArr (tyArr tyenviron typrop) (tyArr tyenviron tympred)
| fprop => tyArr typrop tympred
| fproj_val t => tyArr (tylist tygfield)
                 (tyArr (reptyp t) tyval)
| fupd_val t => tyArr (tylist tygfield)
                 (tyArr (reptyp t)
                  (tyArr tyval (reptyp t)))
end.

Definition proj1T {A} {B} (x: A /\ B) :=
  match x with
  | conj y z => y
  end.

Definition proj2T {A} {B} (x: A /\ B) :=
  match x with
  | conj y z => z
  end.

Definition typD_reptyp_reptype: forall t, typD  (reptyp t) = reptype t.
Proof.
  intros.
  apply (type_mut (fun t => typD (reptyp t) = reptype t)
                  (fun tl => True)
                  (fun fld => typD (reptyp_structlist fld) = reptype_structlist fld /\
                              typD (reptyp_unionlist fld) = reptype_unionlist fld));
  try reflexivity; intros.
  + simpl.
    rewrite H.
    reflexivity.
  + simpl.
    apply (proj1T H).
  + simpl.
    apply (proj2T H).
  + split; reflexivity.
  + split; simpl.
    - destruct (is_Fnil f); simpl; rewrite H; try rewrite (proj1T H0); reflexivity.
    - destruct (is_Fnil f); simpl; rewrite H; try rewrite (proj2T H0); reflexivity.
Defined.

Definition reptyp_reptype ty (v: typD  (reptyp ty)): reptype ty :=
  eq_rect_r (fun x => x) v (eq_sym (typD_reptyp_reptype ty)).

Definition reptype_reptyp ty (v: reptype ty): typD  (reptyp ty) :=
  eq_rect_r (fun x => x) v (typD_reptyp_reptype ty).

Lemma reptyp_reptype_reptype_reptyp: forall t v, reptyp_reptype t (reptype_reptyp t v) = v.
Proof.
  intros.
  unfold reptyp_reptype, reptype_reptyp.
  unfold eq_rect_r.
  generalize (typD_reptyp_reptype t).
  revert v.
  rewrite (typD_reptyp_reptype t).
  intros.
  rewrite <- !eq_rect_eq.
  reflexivity.
Qed.

(*
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

Fixpoint reptype_reptyp ty {struct ty} : reptype ty -> typD (reptyp ty) :=
  match ty as ty0 return (reptype ty0 -> typD  (reptyp ty0)) with
    | Tvoid => fun x : unit => x
    | Tint i s a => fun x : val => x
    | Tlong s a => fun x : val => x
    | Tfloat f a => fun x : val => x
    | Tpointer t a => fun x : val => x
    | Tarray t z a => map (reptype_reptyp  t)
    | Tfunction t t0 c => fun x : unit => x
    | Tstruct i f a => reptype_structlist_reptyp  f
    | Tunion i f a => reptype_unionlist_reptyp  f
    | Tcomp_ptr i a => fun x : val => x
  end
with reptype_structlist_reptyp fl {struct fl} : reptype_structlist fl -> typD (reptyp_structlist fl) :=
  match
    fl as fl0
    return (reptype_structlist fl0 -> typD  (reptyp_structlist fl0))
  with
    | Fnil => fun x : reptype_structlist Fnil => x
    | Fcons i t fl0 =>
      let b := is_Fnil fl0 in
      if b as b0
         return
         ((if b0
          then reptype t
          else (reptype t * reptype_structlist fl0)%type) ->
          typD
               (if b0
                then reptyp t
                else typrod (reptyp t) (reptyp_structlist fl0)))
      then reptype_reptyp t
      else
        fun x : (reptype t * reptype_structlist fl0)%type =>
          (reptype_reptyp t (fst x),
           reptype_structlist_reptyp fl0 (snd x))
  end
with reptype_unionlist_reptyp  fl {struct fl} : reptype_unionlist fl -> typD  (reptyp_unionlist fl) :=
match
     fl as fl0
     return (reptype_unionlist fl0 -> typD  (reptyp_unionlist fl0))
   with
   | Fnil => fun x : reptype_unionlist Fnil => x
   | Fcons i t fl0 =>
       let b := is_Fnil fl0 in
       if b as b0
        return
          ((if b0 then reptype t else (reptype t + reptype_unionlist fl0)%type) ->
           typD
             (if b0
              then reptyp t
              else tysum (reptyp t) (reptyp_unionlist fl0)))
       then reptype_reptyp t
       else
        fun x : (reptype t + reptype_unionlist fl0)%type =>
        match x with
        | inl y => inl (reptype_reptyp t y)
        | inr y => inr (reptype_unionlist_reptyp fl0 y)
        end
   end.

Lemma reptyp_reptype_reptype_reptyp: forall t v, reptyp_reptype t (reptype_reptyp t v) = v.
Proof.
  intros.
  eapply (type_mut
    (fun t => forall v, reptyp_reptype t (reptype_reptyp t v) = v)
    (fun tl => True)
    (fun fld => (forall v, reptyp_structlist_reptype fld (reptype_structlist_reptyp fld v) = v) /\
                (forall v, reptyp_unionlist_reptype fld (reptype_unionlist_reptyp fld v) = v)));
  intros; simpl; auto.
  + rewrite map_map.
    induction v0; simpl; auto.
    rewrite H, IHv0.
    reflexivity.
  + apply (proj1 H).
  + apply (proj2 H).
  + split.
    - if_tac; [apply H |].
      intros.
      unfold fst, snd.
      rewrite H, (proj1 H0).
      destruct v0; reflexivity.
    - if_tac; [apply H |].
      intros.
      destruct v0; [rewrite H; auto |].
      rewrite (proj2 H0).
      reflexivity.
Qed.
*)
Definition sepD  (s : sep) : typD  (typeof_sep s).
refine
match s with
| flocal => (local : typD (typeof_sep flocal))
| fprop => prop
| fdata_at ty =>  _ (*fun sh (t : reptype ty) v => data_at sh ty t v *)
| ffield_at t ids => _
| fproj_val ty => _
| fupd_val ty => _
(*| flseg t id ls => _*)
end.
{ simpl. intros sh rt v.
  exact (data_at sh ty (reptyp_reptype  _ rt) v). }
{ simpl. intros sh ty v.
  exact (field_at sh t ids (reptyp_reptype  _ ty) v). }
{ simpl. intros gfs v.
  exact (proj_val ty gfs (reptyp_reptype  _ v)). }
{ simpl. intros gfs v v0.
  exact (reptype_reptyp _ (upd_val ty gfs (reptyp_reptype _ v) v0)). }
(*{ simpl.
  intros sh lf v1 v2.
  exact (@lseg t id ls sh (List.map (reptyp_structlist_reptype  _) lf) v1 v2). }*)
Defined.

Inductive smx :=
| fenviron : environ -> smx
| fsemax
| fstatement : statement -> smx
| fretassert : ret_assert -> smx
| ftycontext : PTree.t (type * bool) -> PTree.t type -> type -> PTree.t type ->  smx
| fupdate_tycon
(*| fPROPx
| fLOCALx
| fSEPx *)
| fnormal_ret_assert
(*| flocalD : PTree.t val -> PTree.t (type * val) -> list (environ -> Prop) -> smx *)
| fassertD
| flocalD
| fvaltree : PTree.t val -> smx
| fdenote_tc_assert_b_norho
| ftc_expr_b_norho
| ftc_temp_id_b_norho : positive -> type ->  smx
(*| fmsubst_eval_expr_norho*)
(*| fmsubst_eval_lvalue_norho*)
| flater
| flater_lift
| fnested_field_type2
| fis_neutral_cast
| fmsubst_efield_denote : list efield -> smx
| flegal_nested_efield : list type -> smx
| fmsubst_eval_LR
| ftc_LR_b_norho
| ftc_environ
| ftc_efield_b_norho : list efield -> smx
| fnested_efield
| ftypeof_temp
| ftc_val
| flegal_nested_field
| fstruct_field
| funion_field
| farray_subsc
| fwritable_share
| fTsh
| fEws
| ftype_is_by_value
.

Definition typeof_smx (t : smx) :=
match t with
| fsemax => tyArr tyOracleKind (tyArr tytycontext (tyArr (tyArr tyenviron tympred) (tyArr tystatement (tyArr tyret_assert typrop))))
| fstatement s => tystatement
| fretassert r => tyret_assert
| ftycontext _ _ _ _ => tyArr (typtree tyfunspec) tytycontext
(*| fPROPx => tyArr (tylist typrop) (tyArr (tyArr tyenviron tympred) (tyArr tyenviron tympred))
| fLOCALx => tyArr (tylist (tyArr tyenviron typrop)) (tyArr (tyArr tyenviron tympred) (tyArr tyenviron tympred))
| fSEPx => tyArr (tylist (tyArr tyenviron tympred)) (tyArr tyenviron tympred)*)
| fnormal_ret_assert => tyArr (tyArr tyenviron tympred) (tyret_assert)
| fenviron e => tyenviron
| flocalD  => tyArr (typtree tyval)
                    (tyArr (typtree (typrod tyc_type tyval)) (tylist (tyArr tyenviron typrop)))
| fupdate_tycon => tyArr tytycontext (tyArr tystatement tytycontext)
| fvaltree t => typtree tyval
| fassertD => tyArr  (tylist typrop) (tyArr (tylist (tyArr tyenviron typrop)) (tyArr (tylist tympred) (tyArr tyenviron tympred)))
| fdenote_tc_assert_b_norho => tyArr tytc_assert tybool
| ftc_expr_b_norho => tyArr tytycontext (tyArr tyc_expr tybool)
| ftc_temp_id_b_norho _ _  => tyArr tytycontext (tyArr tyc_expr tybool)
(*| fmsubst_eval_expr_norho => tyArr (typtree tyval) (tyArr (typtree (typrod tyc_type tyval)) (tyArr tyc_expr (tyoption tyval)))*)
(*| fmsubst_eval_lvalue_norho =>  tyArr (typtree tyval) (tyArr (typtree (typrod tyc_type tyval)) (tyArr tyc_expr (tyoption tyval)))*)
| flater => tyArr tympred tympred
| flater_lift => tyArr (tyArr tyenviron tympred) (tyArr tyenviron tympred)
| fnested_field_type2 => tyArr tyc_type (tyArr (tylist tygfield) tyc_type)
| fis_neutral_cast => tyArr tyc_type (tyArr tyc_type tybool)
| fmsubst_efield_denote _ => tyArr (typtree tyval)
                           (tyArr (typtree (typrod tyc_type tyval))
                                 (tyoption (tylist tygfield)))
| flegal_nested_efield _ => tyArr tytype_id_env
                          (tyArr tyc_type
                           (tyArr tyc_expr
                            (tyArr (tylist tygfield)
                              (tyArr tyllrr tybool))))
| fmsubst_eval_LR => tyArr (typtree tyval)
                     (tyArr (typtree (typrod tyc_type tyval))
                      (tyArr tyc_expr
                       (tyArr tyllrr (tyoption tyval))))
| ftc_LR_b_norho => tyArr tytycontext (tyArr tyc_expr (tyArr tyllrr tybool))
| ftc_environ => tyArr tytycontext (tyArr tyenviron typrop)
| ftc_efield_b_norho efs => tyArr tytycontext tybool
| fnested_efield => tyArr tyc_expr
                    (tyArr (tylist tyefield)
                     (tyArr (tylist tyc_type) tyc_expr))
| ftypeof_temp => tyArr tytycontext (tyArr tyident (tyoption tyc_type))
| ftc_val => tyArr tyc_type (tyArr tyval typrop)
| flegal_nested_field => tyArr tyc_type (tyArr (tylist tygfield) typrop)
| fstruct_field => tyArr tyident tygfield
| funion_field => tyArr tyident tygfield
| farray_subsc => tyArr tyZ tygfield
| fwritable_share => tyArr tyshare typrop
| fTsh => tyshare
| fEws => tyshare
| ftype_is_by_value => tyArr tyc_type tybool
end.

Definition smxD (t : smx) : typD (typeof_smx t) :=
match t with
| fsemax => (@semax : typD (typeof_smx fsemax))
| fstatement s | fretassert s  => s
| ftycontext t v r gt => fun gf => mk_tycontext t v r gt gf
(*| fPROPx => PROPx
| fLOCALx => LOCALx
| fSEPx => SEPx*)
| fnormal_ret_assert => normal_ret_assert
| fenviron e => (e : typD (typeof_smx (fenviron e)))
| flocalD => localD
| fupdate_tycon => update_tycon
| fvaltree t => t
| fassertD => assertD
| fdenote_tc_assert_b_norho => (denote_tc_assert_b_norho : typD (typeof_smx fdenote_tc_assert_b_norho))
| ftc_expr_b_norho => tc_expr_b_norho
| ftc_temp_id_b_norho id ty  => tc_temp_id_b_norho id ty
(*| fmsubst_eval_expr_norho => msubst_eval_expr*)
(*| fmsubst_eval_lvalue_norho => msubst_eval_lvalue*)
| flater => later
| flater_lift => later
| fnested_field_type2 => nested_field_type2
| fis_neutral_cast => is_neutral_cast
| fmsubst_efield_denote efs => (fun T1 T2 => msubst_efield_denote T1 T2 efs)
| flegal_nested_efield tts => (fun e t_root e1 gfs => legal_nested_efield e t_root e1 gfs tts)
| fmsubst_eval_LR => msubst_eval_LR
| ftc_LR_b_norho => tc_LR_b_norho
| ftc_environ => tc_environ
| ftc_efield_b_norho efs => (fun tycon => tc_efield_b_norho tycon efs)
| fnested_efield => nested_efield
| ftypeof_temp => typeof_temp
| ftc_val => tc_val
| flegal_nested_field => legal_nested_field
| fstruct_field => StructField
| funion_field => UnionField
| farray_subsc => ArraySubsc
| fwritable_share => writable_share
| fTsh => SeparationLogic.Tsh
| fEws => assert_lemmas.Ews
| ftype_is_by_value => client_lemmas.type_is_by_value
end.

Inductive func' :=
| Const : const -> func'
| Zop : z_op -> func'
| Intop : int_op -> func'
| Value : values -> func'
| Eval_f : eval -> func'
| Other : other -> func'
| Sep : sep -> func'
| Data : data -> func'
| Smx : smx -> func'.

Definition func := (SymEnv.func + @ilfunc typ + @bilfunc typ + func')%type.

Definition typeof_func (f: func') : typ :=
match f with
| Const c => typeof_const c
| Zop z => typeof_z_op z
| Intop i => typeof_int_op i
| Value v => typeof_value v
| Eval_f e => typeof_eval e
| Other o => typeof_other o
| Sep s => typeof_sep s
| Data l => typeof_data l
| Smx t => typeof_smx t
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
| Data l => dataD l
| Smx t => smxD t
end.

