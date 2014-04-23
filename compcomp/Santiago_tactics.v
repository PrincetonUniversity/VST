(*Rewriters*)

Ltac rewriter:=
  match goal with
      | H: _ = _ |- _ => rewrite H
  end.

Ltac rewriter_back:=
  match goal with
      | H: _ = _ |- _ => rewrite <- H
  end.

Ltac erewriter:=
  match goal with
      | H: _ = _ |- _ => erewrite H
  end.

Ltac rewriter':=
  match goal with
      | H: _ = _ |- _ => rewrite H in *
  end.

Ltac rewriter_clear:=
  match goal with
      | H: _ = _ |- _ => rewrite H in *; clear H
  end.

Ltac open_eHyp:= match goal with
                     | [H: exists _, _ |- _] => destruct H
                 end.
Ltac descend:= repeat (first [split | progress intros | simpl] ).
Ltac edescend:= repeat (first [split | eexists| progress intros | simpl]).
Ltac edescend':= repeat (first [split | eexists| open_eHyp | progress intros | simpl in *]).

Ltac split_all:= repeat split.

Ltac esplit_all:= repeat esplit.

Ltac open_Hyp:= match goal with
                     | [H: and _ _ |- _] => destruct H
                     | [H: exists _, _ |- _] => destruct H
                 end.

(*Pattern for fresh variables:
let x := fresh "x" in
               evar (x : T);
               let x' := eval unfold x in x in
                 clear x; tactic.
*)