Require Import VST.floyd.proofauto.

(* Tactics for cleaning up proof goals for use as examples
  to send to an SMT solver or some other decision procedure.

  USAGE:   Require Import VST.floyd.extract_smt.
  When you are faced with an entailment,
  instead of calling [entailer], call [extract_smt] instead.

  This leaves a proof goal in which:
  Above the line, there are any hypotheses containing "forbidden"
  terms.  A forbidden term is one that we don't expect the
  solver to be able to handle.
  Below the line, there is a quantified implication containing
  permitted terms.

  Inspect this proof goal.  If you think it is solvable WITHOUT
  using the forbidden terms, then do "clear", then call
  extract_smt again to revert everything else.

  Now, below the line you have the statement of a lemma.
  Copy it into some file such as floyd/smt_test.v,
  and put a comment in your current file with the name
  of that lemma, so that we can trace where these tests came from.

  BUG:  the tactic "extract_smt_forbidden" is undoubtedly incomplete.
  We should add other forbidden terms to it.

*)

Ltac extract_smt_simplify :=
   match goal with
    | |- context [@reptype ?cs ?t] =>
           let p := fresh "p" in set (p := @reptype cs t);
                       lazy beta zeta iota delta in p; subst p
    end.

Ltac extract_smt_forbidden :=
  match goal with
  | |- context [value_fits] => idtac
  | |- context [field_compatible] => idtac
  end.

Ltac extract_smt :=
 try match goal with
         | |- ?A => has_evar A; fail 5 "Cannot extract_smt with evars present"
         | H: ?A |- _ => has_evar A; fail 5 "Cannot extract_smt with evars present"
         | H:= ?A |- _ => has_evar A; fail 5 "Cannot extract_smt with evars present"
         end;
 try match goal with | |- ?P |-- _ =>
    match type of P with ?T => unify T (environ->mpred); go_lower
    end
  end;
  try match goal with | |- _ |-- _ =>
    repeat (( simple apply derives_extract_prop
                || simple apply derives_extract_prop');
                fancy_intros true);
    autorewrite with gather_prop;
    repeat (( simple apply derives_extract_prop
                || simple apply derives_extract_prop');
                fancy_intros true);
   saturate_local;
   repeat erewrite unfold_reptype_elim in * by reflexivity;
   simpl_compare;
   simpl_denote_tc;
   first [ simple apply prop_right
        | simple apply prop_and_same_derives'
        | simple apply andp_right;
            [apply prop_right |  ]
        ]
   end;
   repeat
    match goal with
    | H := _ |- _ => clear H
    | H : name _ |- _ => clear H
    end;
    repeat extract_smt_simplify;
    try (extract_smt_forbidden; fail 3 "proof goal has a forbidden term");
    repeat match goal with
    | H : ?P |- _ =>
       match type of P with Prop =>
         revert H; repeat extract_smt_simplify;
         try (extract_smt_forbidden; fail 1)
       end
     end;
    repeat match goal with   H : ?P  |- _ =>
       match type of P with
       |Prop => idtac
       | _ => clear H || revert H
       end
    end.
