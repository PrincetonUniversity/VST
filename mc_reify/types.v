Require Import MirrorCore.Lambda.ExprCore.
Require Import floyd.proofauto.
Require Import ExtLib.Core.RelDec.
Require Import MirrorCore.TypesI.
Require Import ExtLib.Tactics.
Require Import ExtLib.Data.Fun.
Require Import progs.list_dt. 
Require Import Coq.FSets.FMapPositive.




Inductive typ :=
| tyArr : typ -> typ -> typ
| tytycontext
| tyc_expr
| tyc_type
| tyenviron
| tyval
| tyshare
| tyident
| tylist : typ -> typ
| tyint
| tyZ
| tynat
| typositive
| tybool
| tycomparison
| tytc_assert
| tyint64
| tyfloat
| tyfloat32
| tyattr
| tysignedness
| tyintsize
| tyfloatsize
| tytypelist
| tyfieldlist
| tybinary_operation
| tyunary_operation
| tyN
| tyoption : typ -> typ
| typrop
| tympred
| tysum : typ -> typ -> typ
| typrod : typ -> typ -> typ
| tyunit
| tylistspec : type -> ident -> typ
| tyOracleKind
| tystatement
| tyret_assert
| tyexitkind
| typtree : typ -> typ
| tygfield
| tyfunspec
(*| tyother : positive -> typ*)
.

Fixpoint typD (t : typ) (*(m : PositiveMap.t Type)*): Type :=
    match t with
        | tyArr a b => typD a  -> typD b 
        | tytycontext => tycontext
        | tyc_expr => expr
        | tyc_type => type
        | tyenviron => environ
        | tyval => val
        | tyshare => share
        | tyident => ident
        | tylist t => list (typD t )
        | tyint => int
        | tyZ => Z
        | tynat => nat
        | typositive => positive
        | tybool => bool
        | tycomparison => comparison
        | tytc_assert => tc_assert
        | tyint64 => int64
        | tyfloat => float
        | tyfloat32 => float32
        | tyattr => attr
        | tysignedness => signedness
        | tyintsize => intsize
        | tyfloatsize  => floatsize
        | tytypelist => typelist
        | tyfieldlist => fieldlist
        | tybinary_operation => Cop.binary_operation
        | tyunary_operation => Cop.unary_operation
        | tyN => N
        | tyoption t => option (typD t )
        | typrop => Prop
        | tympred => mpred
        | tysum t1 t2 => sum (typD  t1 ) (typD  t2 )
        | typrod t1 t2 => prod (typD  t1 ) (typD  t2 )
        | tyunit => unit
        | tylistspec t i => listspec t i 
        | tyOracleKind => OracleKind
        | tystatement => statement
        | tyret_assert => ret_assert
(*        | tyother p => PositiveMap.find p m *)
        | tyexitkind => exitkind
        | typtree t => PTree.t (typD t)
        | tygfield => gfield
        | tyfunspec => funspec
    end.
(*
Lemma listspec_ext : forall t i (a b: listspec t i), a = b.
intros. destruct a,b.
subst. inversion list_struct_eq0.
subst. f_equal.
apply proof_irr.
apply proof_irr.
apply proof_irr.
Qed.
*)

Fixpoint typ_eq a b : Option (a = b) :=
match a, b with
| tyArr t11 t21, tyArr t12 t22 => andb (typ_eq t11 t12) (typ_eq t21 t22)
| tytycontext, tytycontext => true
| tyc_expr, tyc_expr => true
| tyc_type, tyc_type => true
| tyenviron, tyenviron => true
| tyval, tyval => true
| tyshare, tyshare => true
| tyident, tyident => true
| tylist t1, tylist t2 => typ_eq t1 t2
| tyint, tyint => true
| tyZ, tyZ => true
| tynat, tynat => true
| typositive, typositive => true
| tybool, tybool => true
| tycomparison, tycomparison => true
| tytc_assert, tytc_assert => true
| tyint64, tyint64 => true
| tyfloat, tyfloat => true
| tyfloat32, tyfloat32 => true
| tyattr, tyattr => true
| tysignedness, tysignedness => true
| tyintsize, tyintsize => true
| tyfloatsize, tyfloatsize => true
| tytypelist, tytypelist => true
| tyfieldlist, tyfieldlist => true
| tybinary_operation, tybinary_operation => true
| tyunary_operation, tyunary_operation => true
| tyN, tyN => true
| tyoption t1, tyoption t2 => typ_eq t1 t2
| typrop, typrop => true
| tympred, tympred => true
| tysum t11 t21, tysum t12 t22 => andb (typ_eq t11 t12) (typ_eq t21 t22)
| typrod t11 t21, typrod t12 t22 => andb (typ_eq t11 t12) (typ_eq t21 t22)
| tyunit, tyunit => true
| tylistspec t1 id1, tylistspec t2 id2 => andb (eqb_type t1 t2) (Peqb id1 id2)
| tyOracleKind, tyOracleKind => true
| tystatement, tystatement => true
| tyret_assert, tyret_assert => true
| tyexitkind, tyexitkind => true
| typtree t1, typtree t2 => typ_eq t1 t2
| tygfield, tygfield => true
| tyfunspec, tyfunspec => true
| _, _ => false
end.


Instance RelDec_eq_typ : RelDec (@eq typ) :=
{ rel_dec := typ_eq
                }.

Instance RelDec_Correct_eq_typ : RelDec_Correct RelDec_eq_typ.
Proof.
  constructor.
  intros.
  unfold rel_dec; simpl.
  split; intros.
    + generalize dependent y. induction x; intros; destruct y; simpl in *; try congruence; auto;
                            try solve [
          rewrite andb_true_iff in *;
          destruct H; apply IHx1 in H;
          apply IHx2 in H0; subst;  auto |
          
          apply IHx in H; subst; auto] .
      rewrite andb_true_iff in *. destruct H.
      apply eqb_type_true in H. subst.
      apply Peqb_true_eq in H0. subst. auto.
    + generalize dependent y. induction x; intros; destruct y; simpl in *; try congruence; auto;
        try solve[
           inversion H; subst; auto; try rewrite andb_true_iff; auto].
      inversion H; subst; clear H.
      rewrite andb_true_iff. split. apply eqb_type_spec. auto.
      apply Pos.eqb_eq. auto.
Qed.

Inductive tyAcc' : typ -> typ -> Prop :=
| tyArrL : forall a b, tyAcc' a (tyArr a b)
| tyArrR : forall a b, tyAcc' b (tyArr a b).
Print RType.
Instance RType_typ : RType typ :=
{ typD := typD
; tyAcc := tyAcc'
; type_cast := fun a b => Some (typ_eq a b) with
                              | true => Some pf
                              | _ => None
                            end
}.

Instance RTypeOk_typ : @RTypeOk typ _.
Proof.
  eapply makeRTypeOk.
  { red.
    induction a; constructor; inversion 1.
    subst; auto.
    subst; auto. }
  { unfold type_cast; simpl.
    intros. destruct (typ_eq_dec x x).
    f_equal. compute.
    uip_all. reflexivity. congruence. }
  { unfold type_cast; simpl.
    intros. destruct (typ_eq_dec x y); try congruence. }
Qed.

Instance Typ2_tyArr : Typ2 _ Fun :=
{ typ2 := tyArr
; typ2_cast := fun  _ _ => eq_refl
; typ2_match :=
    fun T  t tr =>
      match t as t return T (TypesI.typD  t) -> T (TypesI.typD  t) with
        | tyArr a b => fun _ => tr a b
        | _ => fun fa => fa
      end
}.

Instance Typ2Ok_tyArr : Typ2Ok Typ2_tyArr.
Proof.
  constructor.
  { reflexivity. }
  { apply tyArrL. }
  { intros; apply tyArrR. }
  { inversion 1; subst; unfold Rty; auto. }
  { destruct x; simpl; eauto.
    left; do 2 eexists; exists eq_refl. reflexivity. }
  { destruct pf. reflexivity. }
Qed.

Instance Typ0_tyProp : Typ0 _ Prop :=
{| typ0 := typrop
 ; typ0_cast :=  eq_refl
 ; typ0_match := fun T  t =>
                   match t as t
                         return T Prop -> T (TypesI.typD  t) -> T (TypesI.typD  t)
                   with
                     | typrop => fun tr _ => tr
                     | _ => fun _ fa => fa
                   end
 |}.


