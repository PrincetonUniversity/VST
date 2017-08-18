Require Import MirrorCore.Lambda.ExprCore.

Require Import VST.floyd_funcs.

Require Import ExtLib.Core.RelDec.
Require Import MirrorCore.TypesI.
Require Import ExtLib.Tactics.
Require Import ExtLib.Data.Fun.
(*Require Import VST.progs.list_dt. *)
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
(*| tylistspec : type -> ident -> typ*)
| tyOracleKind
| tystatement
| tyret_assert
| tyexitkind
| typtree : typ -> typ
| tygfield
| tyfunspec
| tyefield
| tytype_id_env
| tyllrr
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
        (*| tylistspec t i => listspec t i *)
        | tyOracleKind => OracleKind
        | tystatement => statement
        | tyret_assert => ret_assert
(*        | tyother p => PositiveMap.find p m *)
        | tyexitkind => exitkind
        | typtree t => PTree.t (typD t)
        | tygfield => gfield
        | tyfunspec => funspec
        | tyefield => efield
        | tytype_id_env => type_id_env
        | tyllrr => LLRR
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

Definition typ_eq_dec : forall a b : typ, {a = b} + {a <> b}.
  decide equality.
Defined.
(*
  consider (eqb_ident i i0); intros;
  try rewrite eqb_ident_spec in H. auto.
  destruct (eqb_ident_spec i i0). right. intro. intuition. subst.
  congruence.
  consider (eqb_type t t0); intros.
  rewrite eqb_type_spec in H. auto.
  destruct (eqb_type_spec t t0).
  right; intuition; subst; congruence.
 Defined.
*)

Instance RelDec_eq_typ : RelDec (@eq typ) :=
{ rel_dec := fun a b =>
               match typ_eq_dec a b with
                 | left _ => true
                 | right _ => false
               end }.

Instance RelDec_Correct_eq_typ : RelDec_Correct RelDec_eq_typ.
Proof.
  constructor.
  intros.
  unfold rel_dec; simpl.
  destruct (typ_eq_dec x y); intuition.
Qed.

Inductive tyAcc' : typ -> typ -> Prop :=
| tyArrL : forall a b, tyAcc' a (tyArr a b)
| tyArrR : forall a b, tyAcc' b (tyArr a b).

Instance RType_typ : RType typ :=
{ typD := typD
; tyAcc := tyAcc'
; type_cast := fun a b => match typ_eq_dec a b with
                              | left pf => Some pf
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

