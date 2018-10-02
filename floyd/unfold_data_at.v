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

Ltac unfold_field_at N  :=
  find_field_at N; unfold_field_at'.

Ltac unfold_data_at N  :=
  find_data_at N; unfold_field_at'.

