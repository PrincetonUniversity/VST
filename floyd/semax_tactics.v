Require Import floyd.base.
Require Import floyd.client_lemmas.
(*Require Import floyd.data_at_lemmas.*)
(*Require Import floyd.type_id_env.*)

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

Ltac unfold_abbrev' :=
  repeat match goal with
             | H := @abbreviate ret_assert _ |- _ => 
                        unfold H, abbreviate; clear H 
             | H := @abbreviate tycontext _ |- _ => 
                        unfold H, abbreviate; clear H 
             | H := @abbreviate statement _ |- _ => 
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

Ltac clear_abbrevs :=  repeat match goal with
                                    | H := @abbreviate statement _ |- _ => clear H
                                    | H := @abbreviate ret_assert _ |- _ => clear H  
                                    | H := @abbreviate tycontext _ |- _ => clear H  
                                    end.

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
 | mk_tycontext _ _ _ _ _ _ _ => idtac
 | _ => let d := fresh "d" in let H := fresh in 
       remember A as d eqn:H;
       simplify_Delta_core H;
       subst d
 end.


Fixpoint initialized_list ids D :=
 match ids with
 | nil => D
 | i::il => initialized_list il (initialized i D)
 end.

Lemma initialized_list1:  forall i il a1 a2 a3 a4 a5 a6 a7 d',
    initialized_list il 
      match a1 ! i with
       | Some (ty, _) =>
          mk_tycontext (PTree.set i (ty, true) a1) a2 a3 a4 a5 a6 a7
       | None => mk_tycontext a1 a2 a3 a4 a5 a6 a7
       end = d' ->
    initialized_list (i::il) (mk_tycontext a1 a2 a3 a4 a5 a6 a7) = d'.
Proof. intros; subst; reflexivity.
Qed.

Ltac simplify_Delta := 
 match goal with 
| |- semax ?D _ _ _ =>
            simplify_Delta_at D
| |- PROPx _ (LOCALx (tc_environ ?D :: _) _) |-- _ =>
            simplify_Delta_at D
| |- initialized_list _ _ = ?B =>
         is_var B;
         repeat (apply initialized_list1;
                     simpl PTree.get; cbv beta iota; simpl PTree.set);
         simplify_Delta_at B; reflexivity
| |- ?B = initialized_list _ _ =>
         is_var B;
         symmetry;
         repeat (apply initialized_list1;
                     simpl PTree.get; cbv beta iota; simpl PTree.set);
         simplify_Delta_at B; reflexivity
| |- ?A = ?B =>
     simplify_Delta_at A; simplify_Delta_at B; reflexivity
end.
(*
Ltac build_Struct_env :=
 match goal with
 | SE := @abbreviate type_id_env _ |- _ => idtac
 | Delta := @abbreviate tycontext _ |- _ => 
    pose (Struct_env := @abbreviate _ (type_id_env.compute_type_id_env Delta));
    simpl type_id_env.compute_type_id_env in Struct_env
 end.
*)

Ltac abbreviate_semax :=
 match goal with
 | |- semax _ _ _ _ => 
        simplify_Delta;
        unfold_abbrev';
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
 (*build_Struct_env;*)
 simpl typeof.

Ltac check_Delta :=
match goal with 
 | Delta := @abbreviate tycontext (mk_tycontext _ _ _ _ _ _ _) |- _ =>
    match goal with 
    | |- _ => clear Delta; check_Delta
    | |- semax Delta _ _ _ => idtac 
    end
 | _ => simplify_Delta;
     match goal with |- semax ?D _ _ _ => 
            abbreviate D : tycontext as Delta
     end
end.

Ltac normalize_postcondition :=  (* produces a normal_ret_assert *)
 match goal with 
 | P := _ |- semax _ _ _ ?P =>
     unfold P, abbreviate; clear P; normalize_postcondition
 | |- semax _ _ _ (normal_ret_assert _) => idtac
 | |- _ => apply sequential
  end;
 autorewrite with ret_assert.

Ltac weak_normalize_postcondition := (* does not insist on normal_ret_assert *)
 repeat match goal with P := @abbreviate ret_assert _ |- _ => 
               unfold abbreviate in P; subst P end;
 autorewrite with ret_assert.

(**** BEGIN semax_subcommand stuff  *)

(* Two small-step tactics -- will probbaly not be used very much once the tactics are stable*)
Ltac replaceIdent_and_solve D i DD :=
  replace D with (initialized i DD); try (simplify_Delta; reflexivity); try clear D.

Ltac replaceIdents D ids Delta :=
  match ids with nil => replace Delta with D
   | (cons ?i ?tlids) =>
      replaceIdents (initialized i D) tlids Delta
  end.

(* The core replace & solve tactic*)
Ltac replaceIdents_and_solve D ids Delta :=
  match ids with nil => replace Delta with D; 
        first [simplify_Delta; reflexivity | idtac]
   | (cons ?i ?tlids) =>
      replaceIdents_and_solve (initialized i D) tlids Delta
  end.

Ltac fold_all al :=
 match al with ?a :: ?al' => fold a; fold_all al' | nil => idtac end.

Ltac refold_temp_names F := 
  unfold PTree.prev; simpl PTree.prev_append;
  let fbody := (eval hnf in F) in
   match fbody with
    {| fn_params := ?params; fn_temps := ?temps  |} =>
     let vv := constr:(map fst (params ++ temps)) in
     let v2 := (eval simpl in vv) in
       fold_all v2
   end.


Definition is_init_temp Delta i : bool :=
  match (temp_types Delta) ! i with
  | Some (_ , b) => b
  | None => false
 end. 

Ltac initialized_temps_of_fundec F Delta :=
  let temps := (eval hnf in (fn_temps F)) in
    let vv := constr:(filter (is_init_temp Delta) (map fst temps)) in
     let v2 := (eval simpl in vv) in
        v2.

Ltac mkConciseDelta V G F Delta :=
  let vv := constr:(filter (is_init_temp Delta) (map fst (fn_temps F))) in
    let inits := (eval simpl in vv) in
    replace Delta with (initialized_list inits (func_tycontext F V G))
       by simplify_Delta;
    refold_temp_names F;
  clear Delta.

Ltac semax_subcommand V G F :=
  abbreviate_semax;
  match goal with |- semax ?Delta _ _ _ =>
      mkConciseDelta V G F Delta;
      repeat 
         match goal with
          | P := @abbreviate statement _ |- _ => unfold abbreviate in P; subst P
          | P := @abbreviate ret_assert _ |- _ => unfold abbreviate in P; subst P
         end;
       weak_normalize_postcondition
  end.

(**** END semax_subcommand stuff *)

Arguments join_te te1 te2 / .
Arguments PTree.fold {A} {B} f m v / .
