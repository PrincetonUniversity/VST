Require Import floyd.base.
Require Import floyd.client_lemmas.

(* Bug: abbreviate replaces _ALL_ instances, when sometimes
  we only want just one. *)
Tactic Notation "abbreviate" constr(y) "as"  ident(x)  :=
   (first [ is_var y 
           |  let x' := fresh x in pose (x':= @abbreviate _ y); 
              replace y with x' by reflexivity]).

Tactic Notation "abbreviate" constr(y) ":" constr(t) "as"  ident(x)  :=
   (first [ is_var y 
           |  let x' := fresh x in pose (x':= @abbreviate t y); 
               replace y with x' by reflexivity]).

Ltac unfold_abbrev :=
  repeat match goal with H := @abbreviate _ _ |- _ => 
                        unfold H, abbreviate; clear H 
            end.

Ltac unfold_abbrev_ret :=
  repeat match goal with H := @abbreviate ret_assert _ |- _ => 
                        unfold H, abbreviate; clear H 
            end.

Ltac unfold_abbrev_commands :=
  repeat match goal with H := @abbreviate statement _ |- _ => 
                        unfold H, abbreviate; clear H 
            end.

Ltac clear_abbrevs :=  repeat match goal with H := @abbreviate _ _ |- _ => clear H end.

Arguments var_types !Delta / .

Ltac simplify_Delta_core H := 
 repeat match type of H with _ =  ?A => unfold A in H end;
 cbv delta [abbreviate update_tycon func_tycontext] in H; simpl in H;
 repeat
  (first [
          unfold initialized at 15 in H
        | unfold initialized at 14 in H
        | unfold initialized at 13 in H
        | unfold initialized at 12 in H
        | unfold initialized at 11 in H
        | unfold initialized at 10 in H
        | unfold initialized at 9 in H
        | unfold initialized at 8 in H
        |unfold initialized at 7 in H
        |unfold initialized at 6 in H
        |unfold initialized at 5 in H
        |unfold initialized at 4 in H
        |unfold initialized at 3 in H
        |unfold initialized at 2 in H
        |unfold initialized at 1 in H];
   simpl in H);
 unfold initialized in H;
 simpl in H.

Ltac simplify_Delta_from A :=
 let d := fresh "d" in let H := fresh in 
 remember A as d eqn:H;
 simplify_Delta_core H;
 match type of H with (d = ?A) => apply A end.

Ltac simplify_Delta_at A :=
 match A with
 | (_,_,_,_) => idtac
 | _ => let d := fresh "d" in let H := fresh in 
       remember A as d eqn:H;
       simplify_Delta_core H;
       subst d
 end.

Ltac simplify_Delta := 
 match goal with 
| |- semax ?D _ _ _ =>
            simplify_Delta_at D
| |- PROPx _ (LOCALx (tc_environ ?D :: _) _) |-- _ =>
            simplify_Delta_at D
| |- ?A = _ => unfold A, abbreviate
| |- _ = ?B => unfold B, abbreviate
| |- ?A = ?B =>
     simplify_Delta_at A; simplify_Delta_at B; reflexivity
end.

Ltac abbreviate_semax :=
 match goal with
 | |- semax _ _ _ _ => 
        unfold_abbrev;
        simplify_Delta;
        match goal with |- semax ?D _ ?C ?P => 
            abbreviate D : tycontext as Delta;
            abbreviate P : ret_assert as POSTCONDITION;
            match C with
            | Ssequence ?C1 ?C2 =>
               (* use the next 3 lines instead of "abbreviate"
                  in case C1 contains an instance of C2 *)
                let MC := fresh "MORE_COMMANDS" in
                pose (MC := @abbreviate _ C2);
                change C with (Ssequence C1 MC);
                match C1 with
                | Swhile _ ?C3 => abbreviate C3 as LOOP_BODY
                | _ => idtac
                end
            | Swhile _ ?C3 => abbreviate C3 as LOOP_BODY
            | _ => idtac
            end
        end
 | |- _ |-- _ => unfold_abbrev_ret
 | |- _ => idtac
 end;
 clear_abbrevs;
 simpl typeof.
