Require Import compcert.lib.Coqlib.

(* Ltac by Andrew Appel *)
Ltac do_range H tac :=
  match type of H with
    | ?lo <= ?i < ?hi =>
      try omega;
    let H' := fresh in let H'' := fresh in
                       destruct (zlt lo i) as [H' | H'];
    [ assert (H'' : lo + 1 <= i < hi) by omega;
      simpl in H'';
      clear H H'; rename H'' into H;
      try do_range H tac
    | try (assert (i = lo) by omega; subst i; tac)
    ]
  end.

Lemma test : forall i,
               0 <= i < 256 -> i + 1 > i.
Proof.
  intros.
  do_range H omega.             (* could use simpl; reflexivity, etc. *)
Qed.