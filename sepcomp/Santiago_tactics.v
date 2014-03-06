(*Rewriters*)

Ltac rewriter:=
  match goal with
      | H: _ = _ |- _ => rewrite H
  end.

Ltac rewriter':=
  match goal with
      | H: _ = _ |- _ => rewrite H in *
  end.

Ltac rewriter_clear:=
  match goal with
      | H: _ = _ |- _ => rewrite H in *; clear H
  end.

Ltac split_all:= repeat split.

Ltac esplit_all:= repeat esplit.