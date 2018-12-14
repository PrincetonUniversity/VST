Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.nested_field_lemmas.
Require Import VST.floyd.data_at_rec_lemmas.
Require Import VST.floyd.field_at.
Require Import VST.floyd.mapsto_memory_block.
Opaque alignof.

Local Open Scope logic.

(* This is not well developed or well tested yet, but it does
   get through all the Travis tests 11/10/17 *)
Ltac unfold_field_at' :=
 match goal with
 | |- context [field_at_mark ?cs ?sh ?t ?gfs ?v ?p] =>
     let F := fresh "F" in
       set (F := field_at_mark cs sh t gfs v p);
       change field_at_mark with @field_at in F;
     let V := fresh "V" in set (V:=v) in F;
     let P := fresh "P" in set (P:=p) in F;
     let T := fresh "T" in set (T:=t) in F;
     let id := fresh "id" in evar (id: ident);
     let Heq := fresh "Heq" in
     assert (Heq: nested_field_type T gfs = Tstruct id noattr)
           by (unfold id,T; reflexivity);
     let H := fresh in
     assert (H:= @field_at_Tstruct cs sh T gfs id noattr
                          V V P  (eq_refl _) (JMeq_refl _));
     unfold id in H; clear Heq id;
     fold F in H; clearbody F;
     simpl co_members in H;
     lazy beta iota zeta delta  [nested_sfieldlist_at ] in H;
     change (@field_at cs sh T) with (@field_at cs sh t) in H;
     hnf in T; subst T;
     change v with (protect _ v) in V;
     simpl in H;
     unfold withspacer in H; simpl in H;
     change (protect _ v) with v in V;
     subst V;
     repeat match type of H with
     | context[fst (?A,?B)] => change (fst (A,B)) with A in H
     | context[snd (?A,?B)] => change (snd (A,B)) with B in H
     end;
     subst P;
     subst F;
     cbv beta;
     repeat flatten_sepcon_in_SEP;
     repeat simplify_project_default_val
 | |- context [field_at_mark ?cs ?sh ?t ?gfs ?v ?p] =>
     let F := fresh "F" in
       set (F := field_at_mark cs sh t gfs v p);
       change field_at_mark with @field_at in F;
     let V := fresh "V" in set (V:=v) in F;
     let P := fresh "P" in set (P:=p) in F;
     let T := fresh "T" in set (T:=t) in F;
     let id := fresh "id" in evar (id: ident);
     let Heq := fresh "Heq" in
     assert (Heq: nested_field_type T gfs = Tunion id noattr)
           by (unfold id,T; reflexivity);
     let H := fresh in
     assert (H:= @field_at_Tunion cs sh T gfs id noattr
                          V V P  (eq_refl _) (JMeq_refl _));
     unfold id in H; clear Heq id;
     fold F in H; clearbody F;
     simpl co_members in H;
     lazy beta iota zeta delta  [nested_ufieldlist_at ] in H;
     change (@field_at cs sh T) with (@field_at cs sh t) in H;
     hnf in T; subst T;
     change v with (protect _ v) in V;
     simpl in H;
     unfold withspacer in H; simpl in H;
     change (protect _ v) with v in V;
     subst V;
     repeat match type of H with
     | context[fst (?A,?B)] => change (fst (A,B)) with A in H
     | context[snd (?A,?B)] => change (snd (A,B)) with B in H
     end;
     subst P;
     subst F;
     cbv beta;
     repeat flatten_sepcon_in_SEP;
     repeat simplify_project_default_val
 end.

Ltac unfold_field_at_tac N  :=
  find_field_at N; unfold_field_at'.

Ltac unfold_data_at_tac N  :=
  find_data_at N; unfold_field_at'.

Ltac is_nat_uconstr a :=
  try (tryif (pattern (a : nat)) then fail else fail 1).

Import reptype_lemmas.

Tactic Notation "unfold_data_at" uconstr(a) :=
 tryif (is_nat_uconstr a)
 then (
    idtac "Warning: unfold_data_at with numeric argument is deprecated";
     let x := constr:(a) in unfold_data_at_tac x
   )
 else
 (let x := fresh "x" in set (x := a : mpred);
  lazymatch goal with
  | x := ?D : mpred |- _ =>
    match D with
     | (@data_at_ ?cs ?sh ?t ?p) =>
            change D with (@field_at_mark cs sh t (@nil gfield) (@default_val cs (@nested_field_type cs t nil)) p) in x
     | (@data_at ?cs ?sh ?t ?v ?p) =>
            change D with (@field_at_mark cs sh t (@nil gfield) v p) in x
     | (@field_at_ ?cs ?sh ?t ?gfs ?p) =>
            change D with (@field_at_mark cs sh t gfs (@default_val cs (@nested_field_type cs t gfs)) p) in x
     | (@field_at ?cs ?sh ?t ?gfs ?v ?p) =>
            change D with (@field_at_mark cs sh t gfs v p) in x
     end;
        subst x;  unfold_field_at';
   repeat match goal with |- context [@field_at ?cs ?sh ?t ?gfs (@default_val ?cs' ?t') ?p] => 
       change (@field_at cs sh t gfs (default_val cs' t') p) with (@field_at_ cs sh t gfs p)
    end
end).

Tactic Notation "unfold_field_at" uconstr(a) :=
 tryif (is_nat_uconstr a)
 then (
    idtac "Warning: unfold_field_at with numeric argument is deprecated";
     let x := constr:(a) in unfold_field_at_tac x
   )
 else unfold_data_at a.

