Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import VST.floyd.base2.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
Require Import VST.floyd.client_lemmas.
Import -(notations) compcert.lib.Maps.

(* Bug: abbreviate replaces _ALL_ instances, when sometimes
  we only want just one. *)
Tactic Notation "abbreviate" constr(y) "as"  ident(x)  :=
   (first [ is_var y
           |  let x' := fresh x in pose (x':= @abbreviate _ y);
               change y with x']).

Tactic Notation "abbreviate" constr(y) ":" constr(t) "as"  ident(x)  :=
   (first [ is_var y
           |  let x' := fresh x in pose (x':= @abbreviate t y);
               change y with x']).

Ltac unfold_abbrev :=
  repeat match goal with H := @abbreviate _ _ |- _ =>
                        unfold H, abbreviate; clear H
            end.

Ltac unfold_abbrev' :=
  repeat match goal with
             | H := @abbreviate ret_assert _ |- _ =>
                        unfold H, abbreviate; clear H
(*             | H := @abbreviate tycontext _ |- _ =>
                        unfold H, abbreviate; clear H
*)
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
       
Arguments var_types _ _  !Delta / .

(*
Fixpoint initialized_list ids D :=
 match ids with
 | nil => D
 | i::il => initialized_list il (initialized i D)
 end.

Lemma initialized_list1:  forall i il a1 a2 a3 a4 a5 ann d',
    initialized_list il
      match a1 ! i with
       | Some (ty, _) =>
          mk_tycontext (PTree.set i (ty, true) a1) a2 a3 a4 a5 ann
       | None => mk_tycontext a1 a2 a3 a4 a5 ann
       end = d' ->
    initialized_list (i::il) (mk_tycontext a1 a2 a3 a4 a5 ann) = d'.
Proof. intros; subst; reflexivity.
Qed.
*)

Ltac reduce_snd S1 :=
match goal with
| |- context [snd ?A] =>
   let j := fresh in set (j := snd A) at 1;
   hnf in j;
   reduce_snd S1;
   subst j
| |- _ => intro S1; simpl in S1
end.

Ltac check_ground_ptree t :=
match t with
| PTree.Empty => idtac
| PTree.Nodes ?m => check_ground_ptree m
| PTree.Node001 ?r  => check_ground_ptree r
| PTree.Node010 _ => idtac
| PTree.Node011 _ ?r  => check_ground_ptree r
| PTree.Node100 ?l =>  check_ground_ptree l
| PTree.Node101 ?l ?r => check_ground_ptree l;  check_ground_ptree r
| PTree.Node110 ?l _ => check_ground_ptree l
| PTree.Node111 ?l _ ?r => check_ground_ptree l;  check_ground_ptree r
end.

Ltac check_ground_Delta :=
match goal with
|  Delta := @abbreviate _ (mk_tycontext ?A ?B _ ?D _ ?Ann) |- _ =>
   first [check_ground_ptree A | fail 99 "Temps component of Delta not a ground PTree"];
   first [check_ground_ptree B | fail 99 "Local Vars component of Delta not a ground PTree"];
   first [check_ground_ptree D | fail 99 "Globals component of Delta not a ground PTree"];
   first [check_ground_ptree Ann | fail 99 "Annotation component of Delta not a ground PTree"]
end;
match goal with
|  Delta := @abbreviate _ (mk_tycontext ?A ?B _ ?D ?DS ?Ann),
   DS' := @abbreviate (PTree.t funspec) ?E  |- _ =>
   constr_eq DS DS';
   first [check_ground_ptree E | fail 99 "Delta_specs not a ground PTree"]
|  Delta := @abbreviate _ (mk_tycontext ?A ?B _ ?D ?DS ?Ann),
   DS' : (PTree.t funspec) |- _ =>
   constr_eq DS DS'
end.

(* This tactic is carefully tuned to avoid proof blowups,
  both in execution and in Qed *)
Ltac simplify_func_tycontext' DD :=
  match DD with context [(func_tycontext ?f ?V ?G ?A)] =>
    let D1 := fresh "D1" in let Delta := fresh "Delta" in
    pose (D1 := (func_tycontext f V G A));
    pose (Delta := @abbreviate tycontext D1);
    change (func_tycontext f V G A) with Delta;
    unfold func_tycontext, make_tycontext in D1;
    let DS := fresh "Delta_specs" in
    let d := constr:(make_tycontext_s G) in
    let d := make_ground_PTree d in 
    pose (DS := @abbreviate (PTree.t funspec) d);
    change (make_tycontext_s G) with DS in D1;
    cbv beta iota zeta delta - [DS] in D1;
    subst D1;
    check_ground_Delta
   end.

Ltac simplify_func_tycontext :=
match goal with
 | |- semax _ ?DD _ _ _ => simplify_func_tycontext'  DD
 | |- ENTAIL ?DD, _ ⊢ _ => simplify_func_tycontext'  DD
end.

Section SEMAX_TACTICS.
Context `{!VSTGS OK_ty Σ} {OK_spec: ext_spec OK_ty}.

Definition with_Delta_specs (DS: PTree.t funspec) (Delta: tycontext) : tycontext :=
  match Delta with
    mk_tycontext a b c d _ ann => mk_tycontext a b c d DS ann
  end.
End SEMAX_TACTICS.

Ltac compute_in_Delta :=
 lazymatch goal with
 | DS := @abbreviate (PTree.t funspec) _, Delta := @abbreviate tycontext _ |- _ =>
           cbv beta iota zeta delta - [abbreviate DS] in Delta
 | Delta := @abbreviate tycontext _ |- _ =>
           cbv beta iota zeta delta - [abbreviate] in Delta
 end.

Ltac simplify_Delta' Delta D DD := 
       match DD with
(*
       | context [update_tycon Delta ?c] =>
           let C := fresh "C" in set (C:=c);
           let U := fresh "U" in pose (U := @abbreviate tycontext (update_tycon D C));
           (* change (update_tycon Delta C) with U; *)
           replace (update_tycon Delta C) with U by (unfold U, abbreviate; reflexivity);
           unfold abbreviate in Delta; subst Delta; rename U into Delta;
           compute_in_Delta; subst C
       | context [initialized ?I Delta] =>
           let U := fresh "U" in pose (U := @abbreviate tycontext (initialized I Delta));
           (* change (initialized I Delta) with U; *)
           replace (initialized I Delta) with U by (unfold U, abbreviate; reflexivity);
           unfold abbreviate in Delta; subst Delta; rename U into Delta;
           compute_in_Delta
*)
       | context [with_Delta_specs ?DS Delta] =>
           let U := fresh "U" in pose (U := @abbreviate tycontext (with_Delta_specs DS Delta));
           (* change (with_Delta_specs DS Delta) with U; *)
           replace (with_Delta_specs DS Delta) with U by (unfold U, abbreviate; reflexivity);
           unfold abbreviate in Delta; subst Delta; rename U into Delta;
           compute_in_Delta
       end.
(*
Ltac simplify_Delta'' DD := 
       match DD with
       | context [initialized_list _ _] => unfold initialized_list
       | context [initialized _ ?D] => try (revert D; fail 1); unfold D
       | context [update_tycon ?D _] => try (revert D; fail 1); unfold D
       end.
*)
(* This tactic is carefully tuned to avoid proof blowups,
  both in execution and in Qed *)

Ltac simplify_Delta :=
match goal with
 | Delta := @abbreviate tycontext _ |- _ => clear Delta; simplify_Delta
 | DS := @abbreviate (PTree.t funspec) _ |- _ => clear DS; simplify_Delta
 | D1 := @abbreviate tycontext _ |- semax _ ?D _ _ _ => 
       constr_eq D1 D (* ONLY this case terminates! *)
(*                 
 | |- semax _ ?D _ _ _ => unfold D; simplify_Delta
 | |- _ => simplify_func_tycontext; simplify_Delta
 | |- semax _ (mk_tycontext ?a ?b ?c ?d ?e) _ _ _ => (* delete this case? *)
     let DS := fresh "Delta_specs" in set (DS := e : PTree.t funspec);
     change e with (@abbreviate (PTree.t funspec) e) in DS;
     let D := fresh "Delta" in set (D := mk_tycontext a b c d DS);
     change (mk_tycontext a b c d DS) with (@abbreviate _ (mk_tycontext a b c d DS)) in D
*)
 | D1 := @abbreviate tycontext _ |- ENTAIL ?D, _ ⊢ _ => 
       constr_eq D1 D (* ONLY this case terminates! *)
 | |- semax _ ?D _ _ _ => unfold D; simplify_Delta
 | |- ENTAIL ?D, _ ⊢_ => unfold D; simplify_Delta
 | |- _ => simplify_func_tycontext; simplify_Delta
 | Delta := @abbreviate tycontext ?D 
      |- semax _ ?DD _ _ _ => simplify_Delta' Delta D DD; simplify_Delta
 | Delta := @abbreviate tycontext ?D 
      |- ENTAIL ?DD, _ ⊢ _ => simplify_Delta' Delta D DD; simplify_Delta
 | |- semax _ ?DD _ _ _ =>  simplify_Delta
 |  |- ENTAIL (ret_tycon ?DD), _ ⊢ _ => 
        let D := fresh "D" in 
          set (D := ret_tycon DD);
          hnf in D; simpl is_void_type in D;
          cbv beta iota in D;
          pose (Delta := @abbreviate tycontext D);
          change D with Delta; subst D; simplify_Delta
 |  |- ENTAIL (ret0_tycon ?DD), _ ⊢ _ => 
        let D := fresh "D" in 
          set (D := ret0_tycon DD);
          hnf in D; simpl is_void_type in D;
          cbv beta iota in D;
          pose (Delta := @abbreviate tycontext D);
          change D with Delta; subst D; simplify_Delta
 | |- ENTAIL (ret_tycon ?DD), _ ⊢ _ => simplify_Delta
 | |- _ => fail "simplify_Delta did not put Delta_specs and Delta into canonical form"
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

Ltac is_sequential br co c :=
 lazymatch c with
 | Ssequence ?c1 ?c2 => is_sequential br co c1; is_sequential br co c2
 | Sifthenelse _ ?c1 ?c2 => is_sequential br co c1; is_sequential br co c2
 | Sloop ?body ?incr => is_sequential true true body; is_sequential false false incr
 | Sfor ?init _ ?body ?incr => is_sequential br co init;
       is_sequential true true body; is_sequential false false incr
 | Swhile _ ?body => is_sequential true true body
 | Sswitch _ ?LS => is_sequential_ls co LS
 | Sbreak => constr_eq br true
 | Scontinue => constr_eq co true
 | Sreturn _ => fail
 | Sswitch _ _ => fail
 | Sgoto _ => fail
 | Sskip => idtac
 | Sassign _ _ => idtac
 | Sset _ _ => idtac
 | Scall _ _ _ => idtac
 | Sbuiltin _ _ _ _ => idtac
 | ?c => match goal with M := @abbreviate statement ?c' |- _ =>
               constr_eq c M; is_sequential br co c'
             end
 end
with is_sequential_ls co ls := 
 lazymatch ls with 
 | LSnil => idtac
 | LScons _ ?s ?ls' => is_sequential true co s; is_sequential_ls co ls'
 end.

Ltac force_sequential  :=
match goal with
| P := @abbreviate ret_assert (normal_ret_assert _) |- semax _ _ _ _ ?P' =>
    constr_eq P P'
| P := @abbreviate ret_assert _ |- semax _ _ _ ?c ?P' =>
    constr_eq P P'; 
    try (is_sequential false false c;
         unfold abbreviate in P; subst P;
         apply sequential; simpl_ret_assert)
| P := @abbreviate ret_assert _ |- _ => unfold abbreviate in P; subst P;
      force_sequential
| P := _ |- semax _ _ _ _ ?P' => 
      constr_eq P P'; unfold abbreviate in P; subst P;
      force_sequential
| |- semax _ _ _ _ (normal_ret_assert ?P) => 
       abbreviate (normal_ret_assert P) : ret_assert as POSTCONDITION
| |- semax _ _ _ ?c ?P =>
    tryif (is_sequential false false c)
    then (apply sequential; simpl_ret_assert;
          match goal with |- semax _ _ _ _ ?Q =>
             abbreviate Q as POSTCONDITION
          end)
    else abbreviate P as POSTCONDITION
end.

Ltac abbreviate_semax :=
 match goal with
 | |- semax _ _ False _ _ => apply semax_ff
 | |- semax _ _ (PROPx (False::_) _) _ _ => Intros; contradiction
 | |- semax _ _ _ _ _ =>
  simplify_Delta;
  repeat match goal with
  | MC := @abbreviate statement _ |- _ => unfold abbreviate in MC; subst MC
  end;
  force_sequential;
  match goal with |- semax _ _ _ ?C _ =>
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
 | |- _ ⊢ _ => unfold_abbrev_ret
 end;
 clear_abbrevs;
 simpl typeof.

Ltac check_Delta :=
match goal with
 | Delta := @abbreviate tycontext (mk_tycontext _ _ _ _ _) |- _ =>
    match goal with
    | |- _ => clear Delta; check_Delta
    | |- semax _ Delta _ _ _ => idtac
    end
 | _ => simplify_Delta;
     match goal with |- semax _ ?D _ _ _ =>
            abbreviate D : tycontext as Delta
     end
end.

Ltac normalize_postcondition :=  (* produces a normal_ret_assert *)
 match goal with
 | P := _ |- semax _ _ _ _ ?P =>
     unfold P, abbreviate; clear P; normalize_postcondition
 | |- semax _ _ _ _ (normal_ret_assert _) => idtac
 | |- _ => apply sequential
  end;
 autorewrite with ret_assert.

Ltac weak_normalize_postcondition := (* does not insist on normal_ret_assert *)
 repeat match goal with P := @abbreviate ret_assert _ |- _ =>
               unfold abbreviate in P; subst P end;
 autorewrite with ret_assert.

(**** BEGIN semax_subcommand stuff  *)
(*
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

Ltac mkConciseDelta V G F Ann Delta :=
  let vv := constr:(filter (is_init_temp Delta) (map fst (fn_temps F))) in
    let inits := (eval simpl in vv) in
    change Delta with (initialized_list inits (func_tycontext F V G Ann))(*;
    refold_temp_names F;
  clear Delta*).
*)
Ltac semax_subcommand V G F Ann :=
  abbreviate_semax;
  match goal with |- semax _ ?Delta _ _ _ =>
(*
      mkConciseDelta V G F Ann Delta;
*)
      repeat
         match goal with
          | P := @abbreviate statement _ |- _ => unfold abbreviate in P; subst P
          | P := @abbreviate ret_assert _ |- _ => unfold abbreviate in P; subst P
         end;
       weak_normalize_postcondition
  end.

(**** END semax_subcommand stuff *)

Arguments PTree.fold {A} {B} f m v / .

Ltac no_reassociate_stmt S := S.

Ltac find_statement_in_body f reassoc pat :=
  let body := eval hnf in (fn_body f)
      in let body := reassoc body
      in let S := pat body
      in exact S.

Ltac check_POSTCONDITION' P :=
    lazymatch P with
    | context [bind_ret] => (* is this case obsolete? *)
         fail 100 "Your POSTCONDITION is messed up; perhaps you inadvertently did something like 'simpl in *' that changes it into a form that Floyd cannot recognize.  Right now, you may do 'unfold abbreviate in POSTCONDITION' to inspect it; and in general, avoid 'simpl in *'"
    | context [fun _:environ => _] =>
         fail 100 "Your POSTCONDITION is messed up; perhaps you inadvertently did something like 'simpl in *' that changes it into a form that Floyd cannot recognize.  Right now, you may do 'unfold abbreviate in POSTCONDITION' to inspect it; and in general, avoid 'simpl in *'"
    | _ => idtac
    end.

Ltac check_POSTCONDITION :=
  match goal with
  | P := ?P' |- semax _ _ _ _ ?P'' =>
     constr_eq P P''; check_POSTCONDITION' P'
  | |- semax _ _ _ _ ?P => check_POSTCONDITION' P
  | _ => fail 100 "Your POSTCONDITION is ill-formed in some way "
  end.

Section SEMAX_TACTICS.

Context `{!VSTGS OK_ty Σ} {OK_spec: ext_spec OK_ty}.

Fixpoint find_expressions {A: Type} (f: expr -> A -> A) (c: statement) (x: A) : A :=
 match c with
 | Sskip => x
 | Sassign e1 e2 => f e1 (f e2 x)
 | Sset _ e => f e x
 | Scall _ e el => f e (fold_right f x el)
 | Sbuiltin _ _ _ el => fold_right f x el
 | Ssequence c1 c2 => find_expressions f c1 (find_expressions f c2 x)
 | Sifthenelse e c1 c2 => f e (find_expressions f c1 (find_expressions f c2 x))
 | Sloop c1 c2 => find_expressions f c1 (find_expressions f c2 x)
 | Sbreak => x
 | Scontinue => x
 | Sreturn (Some e) => f e x
 | Sreturn None => x
 | Sswitch e cl => f e (find_expressions_sl f cl x)
 | Slabel _ c => find_expressions f c x
 | Sgoto _ => x
 end
with find_expressions_sl {A: Type} (f: expr -> A -> A) (c: labeled_statements) (x: A) : A :=
 match c with
 | LSnil => x
 | LScons _ c1 c2 => find_expressions f c1 (find_expressions_sl f c2 x)
 end.

Fixpoint find_vars {A: Type} (f: ident -> A -> A) (e: expr) (x: A) : A :=
 match e with
 | Evar i _ => f i x
 | Ederef e _ => find_vars f e x
 | Eaddrof e _ => find_vars f e x
 | Eunop _ e _ => find_vars f e x
 | Ebinop _ e1 e2 _ => find_vars f e1 (find_vars f e2 x)
 | Ecast e _ => find_vars f e x
 | Efield e _ _ => find_vars f e x
 | _ => x
 end.

Definition isNone {A} (x: option A) :=
 match x with None => true | _ => false end.

Definition check_no_overlap
     (V: varspecs) (G: (@funspecs Σ)) : bool :=
  let table :=  List.fold_left (fun t v => PTree.set (fst v) tt t) G (PTree.empty _)
   in forallb (fun f => isNone (table !! (fst f))) V.

Lemma check_no_overlap_e  :
  forall V G, check_no_overlap V G = true ->
  forall i, In i (map fst V) -> ~ In i (map fst G).
Proof.
intros *. intros H i H1 H0.
unfold check_no_overlap in *.
assert ((fun (f: positive * type)  =>
       isNone
         ((fold_left
            (fun t v =>
             PTree.set (fst v) tt t) G (PTree.empty unit)) !! (fst f)))
 =  (fun f =>
       isNone
         ((fold_right
            (fun v t=>
             PTree.set (fst v) tt t) (PTree.empty unit) G) !! (fst f)))).
{
clear.
extensionality idx.
destruct idx as [j ?].
simpl. clear t.
unfold isNone.
replace ((fold_right
     (fun v t
      => PTree.set (fst v) tt t)
     (PTree.empty unit) G) !! j) with
    ((fold_left
     (fun t v
      => PTree.set (fst v) tt t) G
     (PTree.empty unit)) !! j); auto.
rewrite <- fold_left_rev_right.
forget (PTree.empty unit) as base.
revert base.
induction G; intros; simpl; auto.
rewrite fold_right_app.
simpl.
rewrite IHG; clear IHG.
destruct (ident_eq j (fst a)).
subst j.
rewrite PTree.gss.
revert base; induction G; intros.
apply PTree.gss.
simpl.
change positive with ident .
destruct (ident_eq (fst a) (fst a0)).
rewrite <- e.
rewrite PTree.gss; auto.
rewrite PTree.gso; auto.
rewrite PTree.gso; auto.
revert base; induction G; intros.
simpl; auto.
rewrite PTree.gso; auto.
simpl.
change positive with ident .
destruct (ident_eq j (fst a0)).
subst.
rewrite !PTree.gss; auto.
rewrite !PTree.gso; auto.
}
rewrite H2 in H. clear H2.
induction V.
inv H1.
destruct H1.
-
subst i.
simpl in *.
rewrite andb_true_iff in H.
destruct H.
apply IHV in H1; clear IHV.
auto.
clear H1.
exfalso.
induction G.
inv H0.
destruct H0.
simpl in H.
change positive with ident in *.
rewrite H0 in H.
rewrite PTree.gss in H.
inv H.
apply IHG; auto.
clear H0 IHG.
simpl in H.
change positive with ident in *.
destruct (ident_eq (fst a0) (fst a)).
rewrite e in H.
rewrite PTree.gss in H.
inv H.
rewrite PTree.gso in H; auto.
-
simpl in H.
rewrite andb_true_iff in H.
destruct H.
auto.
Qed.
 
Lemma leaf_function': 
 forall Vprog Gprog (CS: compspecs) f s,
 check_no_overlap Vprog Gprog = true ->
 semax_body Vprog nil f s ->
 semax_body Vprog Gprog f s.
Proof.
intros.
unfold semax_body in *.
destruct s as [id fs].
destruct fs.
destruct H0 as [H0' [H0'' H0]]; split3; auto.
clear H0'.
intros.
specialize (H0 _ x).
eapply semax_Delta_subsumption; [ | apply H0].
clear - H.
split3; [ | | split3; [ | | split]]; auto.
-
intros; simpl; auto.
destruct ((make_tycontext_t (fn_params f) (fn_temps f))
  !! id); auto.
-
intros; hnf; intros.
destruct ((glob_types (func_tycontext f Vprog nil nil))
  !! id) eqn:?H; auto.
simpl in *.
unfold make_tycontext_g.
apply check_no_overlap_e with (i:=id) in H.
forget (fold_right
      (fun v : ident * type =>
       PTree.set (fst v) (snd v))
      (PTree.empty type) Vprog) as base.
induction Gprog.
simpl. auto.
simpl in H.
apply Decidable.not_or in H.
destruct H.
simpl.
rewrite PTree.gso; [|by auto].
auto.
clear - H0.
induction Vprog.
simpl in H0. rewrite PTree.gempty in H0. inv H0.
simpl in *.
destruct (ident_eq (fst a) id).
auto.
rewrite PTree.gso in H0; [|by auto].
auto.
-
intros; hnf; intros.
simpl.
auto.
-
intros.
hnf; intros.
simpl.
auto.
Qed.

Definition check_no_overlap'
    (V: varspecs) (Gtable: PTree.t unit) : bool :=
  forallb (fun f => isNone (Gtable !! (fst f))) V.

Definition check_no_Gvars (Gtable: PTree.t unit) (s: statement) : bool :=
  find_expressions 
    (find_vars (fun i b => match Gtable!!i with Some _=> false | None => b end))
    s true.

Lemma leaf_function: 
 forall Vprog Gprog (CS: compspecs) f s Gtable,
 Gtable = fold_left
    (fun (t : PTree.t unit) (v : ident * funspec) =>
     PTree.set (fst v) tt t) Gprog (PTree.empty unit) ->
 check_no_overlap' Vprog Gtable = true ->
 check_no_Gvars Gtable (fn_body f) = true ->
 semax_body Vprog nil f s ->
 semax_body Vprog Gprog f s.
Proof.
intros.
clear H1.
eapply leaf_function'; try apply H2.
subst Gtable.
apply H0.
Qed.

Fixpoint seq_stmt_size (c: statement) : nat :=
 match c with
 | Ssequence c1 c2 => seq_stmt_size c1 + seq_stmt_size c2
 | _ => 2
 end.

Fixpoint unfold_seqN' (K: nat) (n: nat) (c: statement) : list statement * nat * statement:=
 match K with O => (nil,n,c) | S k =>
  match n with
  | O => (nil, O, c)
  | S n' =>  
  match c with
  | Sskip => (nil, n, c)
  | Ssequence c1 c2 => 
       match unfold_seqN' k n c1 with 
        | (al, n1, Sskip) => match unfold_seqN' k n1 c2
                                 with (bl, n2, c3) => (al++bl, n2, c3)
                                 end
        | (al, n1, c1') => (al, n1, Ssequence c1' c2)
        end
  | _ => (c::nil, n', Sskip)
  end end end.

Definition unfold_seqN n c := unfold_seqN' (seq_stmt_size c) n c.

Fixpoint fold_seq lc : statement :=
  match lc with
  | nil => Sskip
  | c1::nil => c1
  | c :: lc0 => Ssequence c (fold_seq lc0)
  end.

(* Unlike unfold_Ssequence in veric/SeparationLogic.v, unfold_seq preserves Sfor and Swhile.
   In fact, it folds them even if they were not explicitly written in the input.
   Note that we don't treat Sdowhile, because there are no floyd tactics for it, and because
   it would result in 2198 cases when unfold_seq is printed. *)
Fixpoint unfold_seq c : list statement :=
  match c with
  | Sloop (Ssequence (Sifthenelse e Sskip Sbreak) s) Sskip =>
    Swhile e s :: nil
  | Ssequence s1 (Sloop (Ssequence (Sifthenelse e2 Sskip Sbreak) s3) s4) =>
    (* TODO check if this matches cases we don't want it to match and if so, check that the loop
       iteration variable of s1 is the same as in the increment in s4, but then we'll exclude
       multi-statement for loop initialisations *)
    Sfor s1 e2 s3 s4 :: nil
  | Ssequence c1 c2 => unfold_seq c1 ++ unfold_seq c2
  | _ => c::nil
  end.

Lemma flat_map_app: forall {A B: Type} (f: A -> list B) l1 l2,
  flat_map f l1 ++ flat_map f l2 = flat_map f (l1 ++ l2).
Proof.
  intros. induction l1.
  - reflexivity.
  - simpl. rewrite <- app_assoc. congruence.
Qed.

Lemma unfold_Ssequence_idempotent: forall c,
  flat_map unfold_Ssequence (unfold_Ssequence c) = unfold_Ssequence c.
Proof.
  intro c. induction c; try reflexivity.
  simpl. rewrite <- flat_map_app. congruence.
Qed.

Lemma flat_map_unfold_Ssequence_idempotent: forall ls,
  flat_map unfold_Ssequence (flat_map unfold_Ssequence ls) = flat_map unfold_Ssequence ls.
Proof.
  intro. induction ls.
  - reflexivity.
  - simpl. rewrite <- flat_map_app. f_equal; [ | assumption ].
    apply unfold_Ssequence_idempotent.
Qed.

Lemma unfold_seq_to_unfold_Ssequence: forall cs,
  unfold_Ssequence cs = flat_map unfold_Ssequence (unfold_seq cs).
Proof.
  intro cs. induction cs; try reflexivity.
  - simpl. rewrite IHcs1 IHcs2. rewrite flat_map_app.
    destruct cs2; try reflexivity;
    try rewrite flat_map_unfold_Ssequence_idempotent; try reflexivity.
    destruct cs2_1; try reflexivity;
    try rewrite flat_map_unfold_Ssequence_idempotent; try reflexivity.
    destruct cs2_1_1; try reflexivity;
    try rewrite flat_map_unfold_Ssequence_idempotent; try reflexivity.
    destruct cs2_1_1_1; try reflexivity;
    try rewrite flat_map_unfold_Ssequence_idempotent; try reflexivity.
    destruct cs2_1_1_2; try reflexivity;
    try rewrite flat_map_unfold_Ssequence_idempotent; try reflexivity.
    rewrite <- flat_map_app.
    simpl. rewrite app_nil_r. f_equal; [ symmetry; assumption | ].
    destruct cs2_2; reflexivity.
  - simpl.
    destruct cs1; try reflexivity.
    destruct cs1_1; try reflexivity.
    destruct cs1_1_1; try reflexivity.
    destruct cs1_1_2; try reflexivity.
    destruct cs2; reflexivity.
Qed.

Lemma semax_unfold_seq {CS: compspecs} : forall E c1 c2,
  unfold_seq c1 = unfold_seq c2 ->
  forall P Q Delta, semax Delta P E c1 Q -> semax Delta P E c2 Q.
Proof.
  intros. eapply semax_unfold_Ssequence; [ | eassumption ].
  do 2 rewrite unfold_seq_to_unfold_Ssequence.
  congruence.
Qed.

Ltac first_N_statements n :=
 lazymatch goal with |- semax _ _ _ ?c _ =>
 let c' := constr:(unfold_seqN n c) in
 let c' := eval cbv beta iota zeta delta
   [seq_stmt_size app unfold_seqN unfold_seqN' Init.Nat.add]
      in c' in 
 lazymatch c' with
 | (_, S _, _) => fail "There were fewer than" n "statements in the sequence"
 | (?al, O, ?c'') => let al' := constr:(fold_seq al) in
                         let al' := eval cbv beta iota zeta delta [fold_seq] in al' in
                         apply semax_unfold_seq with (Ssequence al' c''); 
                         [reflexivity | eapply semax_seq' ]
 end end.
End SEMAX_TACTICS.

Definition function_pointers := tt.
Ltac function_pointers :=
 let x := fresh "there_are" in
 pose (x := function_pointers).

Ltac leaf_function := 
 try lazymatch goal with
 | x := function_pointers |- _ => clear x
 | |- semax_body ?Vprog ?Gprog _ _ =>
 eapply leaf_function;
 [reflexivity 
 | reflexivity; fail "Error in leaf_function tactic: your" Vprog "and" Gprog "overlap!"
 | reflexivity; fail "Error in leaf_function tactic: your function body refers to an identifier in" Gprog
 | ]
end.

(*
Definition any_gvars (ds: PTree.t funspec) (s: statement) : bool :=
  find_expressions 
    (find_vars (fun i b => match ds!i with Some _=> true | None => b end))
    s false.

Ltac suggest_leaf_function :=
 lazymatch goal with 
 | x := function_pointers |- _ => clear x
 | DS := @abbreviate (PTree.t funspec) ?ds,
   D := @abbreviate tycontext (mk_tycontext _ _ _ _ ?DS' _) |-
   semax _ ?D' _ ?c _ =>
   constr_eq DS DS'; constr_eq D D';
   let b := constr:(any_gvars ds c) in
   let b := eval compute in b in
   constr_eq b false;
   idtac "This function appears to be a leaf function, that is, has no function calls.
   * If you will reason about function-pointers (using make_func_ptr) in this proof, apply the tactic [function_pointers] before doing [start_function].
    * If this semax_body proof does NOT involve function-pointers, use the tactic [leaf_function] before [start_function]; this is optional but will speed up the proof by clearing the body of Delta_specs."
    end.
    *)