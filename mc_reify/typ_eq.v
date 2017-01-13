Require Import types.
Import Coq.Bool.Bool.

Fixpoint typ_beq a b :=
match a, b with
| tytycontext, tytycontext
| tyc_expr, tyc_expr
| tyc_type, tyc_type
| tyenviron, tyenviron
| tyval, tyval
| tyshare, tyshare
| tyident, tyident
| tyint, tyint
| tyZ, tyZ
| tynat, tynat
| typositive, typositive
| tybool, tybool
| tycomparison, tycomparison
| tytc_assert, tytc_assert
| tyint64, tyint64
| tyfloat, tyfloat
| tyattr, tyattr
| tysignedness, tysignedness
| tyintsize, tyintsize
| tyfloatsize, tyfloatsize
| tytypelist, tytypelist
| tyfieldlist, tyfieldlist
| tybinary_operation, tybinary_operation
| tyunary_operation, tyunary_operation
| tyN, tyN
| typrop, typrop
| tympred, tympred
| tyunit, tyunit
| tyOracleKind, tyOracleKind
| tystatement, tystatement
| tygfield, tygfield
| tyfunspec, tyfunspec
| tyret_assert, tyret_assert => true
(*| tylistspec ty1 id1, tylistspec ty2 id2 => andb (expr.eqb_type ty1 ty2) (BinPos.Pos.eqb id1 id2)*)
| tysum tl1 tr1, tysum tl2 tr2
| typrod tl1 tr1, typrod tl2 tr2
| tyArr tl1 tr1, tyArr tl2 tr2 => andb (typ_beq tl1 tl2) (typ_beq tr1 tr2)
| tyoption t1, tyoption t2 => typ_beq t1 t2
| tylist t1, tylist t2 => typ_beq t1 t2
| _, _ => false
end.

SearchAbout BinPos.Pos.eqb.
Hint Resolve expr.eqb_type_true : beq_sound.
Hint Resolve BinPos.Peqb_true_eq : beq_sound.

Ltac prove_beq_sound :=
try solve [try reflexivity; inversion H];
repeat
match goal with
 | [H : typ_beq _ _ = true |- _ ] => simpl in H; rewrite andb_true_iff in H; destruct H
 | [ |- _ _ _ = _ _ _ ] => try f_equal
 | [ |- _ _  = _ _  ] => try f_equal
 | [H : forall x, _ -> ?a = x |- ?a = _ ] => apply H
end;
auto with beq_sound.

Lemma typ_beq_sound : forall a b, typ_beq a b = true -> a = b.
Proof.
intro a.
induction a; intros;  destruct b; prove_beq_sound.
Qed.
