Require Import clight_expr_eq.
Require Import Clight.
Require Import ExtLib.Data.List.
Require Import ExtLib.Core.RelDec.
Require Import Coq.Bool.Bool.
Require Import ExtLib.Tactics.

Hint Resolve expr_beq_sound : expr_beq.

Instance RelDec_expr_beq : RelDec (@eq expr) :=
{ rel_dec := expr_beq }.

Instance RelDec_Correct_expr_beq : RelDec_Correct RelDec_expr_beq.
Proof.
  constructor.
  unfold rel_dec; simpl.
  exact expr_beq_spec.
Qed.

Fixpoint statement_beq s1 s2 :=
  match s1, s2 with
  | Sskip, Sskip
  | Sbreak, Sbreak
  | Scontinue, Scontinue => true
  | Sset id1 e1, Sset id2 e2 => andb (BinPos.Pos.eqb id1 id2) (expr_beq e1 e2)
  | Sassign e11 e21, Sassign e12 e22 =>  andb (expr_beq e11 e12) (expr_beq e21 e22)
  | Scall id1 e1 l1, Scall id2 e2 l2 => andb (andb (expr.eqb_option BinPos.Pos.eqb id1 id2) (expr_beq e1 e2)) (List.list_eqb _ l1 l2)
  | Sbuiltin _ _ _ _, Sbuiltin _ _ _ _ => false (*TODO*)
  | Ssequence st1 st2, Ssequence st3 st4
  | Sloop st1 st2, Sloop st3 st4 => andb (statement_beq st1 st3) (statement_beq st2 st4)
  | Sifthenelse e1 st1 st2, Sifthenelse e2 st3 st4 => andb (andb (statement_beq st1 st3) (statement_beq st2 st4)) (expr_beq e1 e2)
  | Sreturn e1, Sreturn e2 => expr.eqb_option expr_beq e1 e2
  | Slabel l1 s1, Slabel l2 s2 => andb (BinPos.Pos.eqb l1 l2) (statement_beq s1 s2)
  | Sgoto l1, Sgoto l2 => BinPos.Pos.eqb l1 l2
  | Sswitch e1 l1, Sswitch e2 l2 => andb (expr_beq e1 e2) (labeled_statements_beq l1 l2)
  | _ , _ => false
end
with labeled_statements_beq a b :=
match a, b with
| LSnil, LSnil => true
| LScons z1 s1 t1, LScons z2 s2 t2 => andb (andb (expr.eqb_option Zbool.Zeq_bool z1 z2) (statement_beq s1 s2)) (labeled_statements_beq t1 t2)
| _, _ => false
end.

Ltac destruct_ands :=
repeat rewrite andb_true_iff in *;
repeat
match goal with
| [ H: _ /\ _ |- _] => destruct H
end.

Lemma eqb_option_sound : forall T f a b,  (forall (x y : T), f x y = true -> x = y) -> expr.eqb_option f a b = true -> a = b.
Proof.
intros.
destruct a, b; auto; inversion H0.
Qed.

Hint Resolve eqb_option_sound : expr_beq.

Lemma statement_beq_sound : forall s1 s2, statement_beq s1 s2 = true -> s1 = s2
with labeled_statements_beq_sound : forall ls1 ls2, labeled_statements_beq ls1 ls2 = true -> ls1 = ls2.
Proof.
+ intro. destruct s1; intros; match goal with [ |- _ = ?s2] => destruct s2 end; try solve [repeat
  try reflexivity; try solve [inversion H]; try (simpl in H; try rewrite andb_true_iff in H; destruct_ands); f_equal; try apply eqb_option_sound in H; auto with expr_beq].
  - simpl in H. destruct_ands. apply eqb_option_sound in H; auto with expr_beq. f_equal;
                                                                                auto with expr_beq.
    consider (list_eqb RelDec_expr_beq l l0); auto.
+ intros. destruct ls1, ls2; try reflexivity; try solve [inversion H].
  simpl in H; destruct_ands; f_equal; auto with expr_beq.
  apply eqb_option_sound in H; auto with expr_beq.
  apply Zbool.Zeq_bool_eq.
Qed.

