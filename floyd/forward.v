Require Import floyd.base.
Require Import floyd.client_lemmas.
Require Import floyd.field_mapsto.
Require Import floyd.assert_lemmas.
Require Import floyd.canonicalize floyd.forward_lemmas floyd.call_lemmas.
Require Import floyd.loadstore_lemmas.
Require Import floyd.malloc_lemmas.
Require Import floyd.array_lemmas.
Require Import floyd.entailer.
Import Cop.

Local Open Scope logic.

Definition abbreviate {A:Type} (x:A) := x.
Implicit Arguments abbreviate [[A][x]].
(* Notation "'...'" := (abbreviate _). *)

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

Ltac abbreviate_semax :=
 match goal with
 | |- semax _ _ _ _ => unfold_abbrev;
        match goal with |- semax ?D _ ?C ?P => 
            abbreviate D : tycontext as Delta;
            abbreviate P : ret_assert as POSTCONDITION;
            match C with
            | Ssequence ?C1 ?C2 =>
                abbreviate C2 as MORE_COMMANDS;
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
 clear_abbrevs.

Definition query_context Delta id :=
     match ((temp_types Delta) ! id) with 
      | Some _ => (temp_types Delta) ! id =
                  (temp_types Delta) ! id
      | None => 
        match (var_types Delta) ! id with
          | Some _ =>   (var_types Delta) ! id =
                        (var_types Delta) ! id
          | None =>
            match (glob_types Delta) ! id with
              | Some _ => (var_types Delta) ! id =
                          (var_types Delta) ! id
              | None => (temp_types Delta) ! id = None /\
                        (var_types Delta) ! id = None /\
                        (glob_types Delta) ! id = None
            end
        end
    end.


Lemma is_and : forall A B,
A /\ B -> A /\ B.
Proof.
auto.
Qed.

Ltac solve_query_context :=
unfold query_context; simpl; auto.


Ltac query_context Delta id :=
let qu := fresh "QUERY" in
assert (query_context Delta id) as qu by solve_query_context;
hnf in qu;
first [apply is_and in qu |
simpl PTree.get at 2 in qu].

(* BEGIN HORRIBLE1.
  The following lemma is needed because CompCert clightgen
 produces the following AST for function call:
  (Ssequence (Scall (Some id') ... ) (Sset id (Etempvar id' _)))
instead of the more natural
   (Scall id ...)
Our general tactics are powerful enough to reason about the sequence,
one statement at a time, but it is not nice to burden the user with knowing
about id'.  So we handle it all in one gulp.
 
The lemma goes here, because it imports from both forward_lemmas and call_lemmas.

 See also BEGIN HORRIBLE1 , later in this file
*)
 

Lemma semax_call_id1_x:
 forall Espec Delta P Q R ret ret' id retty bl argsig A x Pre Post
   (GLBL: (var_types Delta) ! id = None),
   (glob_types Delta) ! id = Some (Global_func (mk_funspec (argsig,retty) A Pre Post)) ->
   match retty with Tvoid => False | Tcomp_ptr _ _ => False | _ => True end ->
  forall
   (CLOSQ: Forall (closed_wrt_vars (eq ret')) Q)
   (CLOSR: Forall (closed_wrt_vars (eq ret')) R),
   type_is_volatile retty = false -> 
   (temp_types Delta) ! ret' = Some (retty, false) ->
   is_neutral_cast retty retty = true ->
   match (temp_types Delta) ! ret with Some (t,_) => eqb_type t retty | None => false end = true ->
  @semax Espec Delta (PROPx P (LOCALx (tc_exprlist Delta (snd (split argsig)) bl :: Q) (SEPx (`(Pre x) (make_args' (argsig,retty) (eval_exprlist (snd (split argsig)) bl)) :: R))))
    (Ssequence (Scall (Some ret')
             (Evar id (Tfunction (type_of_params argsig) retty))
             bl)
      (Sset ret (Etempvar ret' retty)))
    (normal_ret_assert 
       (EX old:val, 
          PROPx P (LOCALx (map (subst ret (`old)) Q) 
             (SEPx (`(Post x) (get_result1 ret) :: map (subst ret (`old)) R))))).
Proof.
 pose (H1:=True); pose (H2:=True).

 intros. rename H3 into NONVOL.
 eapply semax_seq'.
 assert (H0':    match retty with Tvoid => False | _ => True end)
  by (clear - H0; destruct retty; try contradiction; auto).
 apply (semax_call_id1' _ _ P Q R ret' _ _ bl _ _ x _ _ GLBL H H0' CLOSQ CLOSR).
match goal with |- semax ?D (PROPx ?P ?QR) ?c ?Post =>
   assert ( (fold_right and True P) -> semax D (PROPx nil QR) c Post)
 end.
Focus 2.
 clear - H3.
 unfold PROPx. 
 unfold PROPx at 1 in H3.
 normalize in H3.
 apply semax_extract_prop. apply H3.
 (* End Focus 2 *)
 intro.
 apply semax_post_flipped
 with (normal_ret_assert (EX  x0 : val,
PROP  ()
(LOCALx
   (tc_environ
      (initialized ret
         (update_tycon Delta
            (Scall (Some ret') (Evar id (Tfunction (type_of_params argsig) retty)) bl)))
    :: `eq (eval_id ret)
         (subst ret (`x0) (eval_expr (Etempvar ret' retty)))
       :: map (subst ret (`x0)) Q)
   (SEPx
      (map (subst ret (`x0)) (`(Post x) (get_result1 ret') :: R)))))).
  make_sequential;
          eapply semax_post_flipped;
          [ apply forward_setx; 
            try solve [intro rho; rewrite andp_unfold; apply andp_right; apply prop_right;
                            repeat split ]
           | intros ?ek ?vl; apply after_set_special1 ].
 apply andp_right.
 intro rho; unfold tc_expr; simpl.
 rewrite NONVOL. simpl.
 replace ( (temp_types (initialized ret' Delta)) ! ret' ) 
     with (Some (retty, true)).
Focus 2.
 unfold initialized;  simpl. rewrite H4.
 unfold temp_types; simpl.
 rewrite PTree.gss. auto.
 (* End Focus 2 *)
 unfold local; apply prop_right.
 simpl.  destruct retty; simpl; inv H5; try apply I.
 contradiction.
 intro rho; apply prop_right; unfold tc_temp_id; simpl.
 unfold typecheck_temp_id.
 destruct (eq_dec ret' ret).
 subst ret'.
 unfold temp_types. unfold initialized; simpl.
 rewrite H4. simpl. rewrite PTree.gss.
 rewrite H5.
 simpl.
 unfold isCastResultType. unfold is_neutral_cast in H5.
 destruct (Cop.classify_cast retty retty); try discriminate.
 rewrite eqb_type_refl. apply I.
 unfold temp_types. unfold initialized; simpl.
 rewrite H4. simpl. rewrite PTree.gso by auto. 
 destruct ((temp_types Delta) ! ret); try discriminate.
 destruct p. apply eqb_type_true in H6.
 subst t. rewrite H5.
 simpl.
 unfold isCastResultType. unfold is_neutral_cast in H5.
 destruct (Cop.classify_cast retty retty); try discriminate.
 rewrite eqb_type_refl. apply I.
 auto.
 intros.
 apply andp_left2. apply normal_ret_assert_derives'.
 apply exp_derives; intro old.
 apply andp_derives.
 apply prop_right; auto.
 go_lowerx.
 apply sepcon_derives; auto.
 rewrite subst_lift1'.
 replace (subst ret (fun _ => old) (get_result1 ret') rho)
   with (get_result1 ret rho); auto.
 destruct (eq_dec ret ret').
 subst.
 unfold get_result1.
 unfold subst. f_equal.
 autorewrite with subst in H8.
 normalize in H8. rewrite H8.
 f_equal. unfold eval_id.  simpl. rewrite Map.gss. reflexivity.
 clear - H6 H8 H7.
 unfold tc_environ in H7.
 unfold env_set. destruct rho; simpl in *; f_equal.
 unfold eval_id in H8; simpl in H8. 
 unfold subst in H8.
 simpl in *. rewrite Map.gss in H8. simpl in H8.
 unfold lift in H8. 
 unfold Map.set. extensionality i. 
 destruct (ident_eq i ret'); auto.  subst i.
 unfold typecheck_environ in H7.
 destruct H7 as [? [_  [_ _]]].
 simpl te_of in H.
 hnf in H.
 specialize (H ret').
 revert H6; case_eq ((temp_types Delta)!ret'); intros; try discriminate.
 destruct p.
 unfold temp_types, initialized in H; simpl in H.
 rewrite H0 in H. unfold temp_types in *. simpl in H. rewrite PTree.gss in H.
 simpl in H. rewrite PTree.gss in H.
 specialize (H true t (eq_refl _)). 
 destruct H as [v [? ?]]. unfold Map.get in H,H8; rewrite H in *.
 f_equal. destruct H1. inv H1.  destruct v; inv H8; inv H1; auto.
  rewrite closed_wrt_subst; auto with closed.
 unfold get_result1.
 f_equal. f_equal.
 rewrite H8.
  rewrite closed_wrt_subst; auto with closed.
Qed.

(* END HORRIBLE1 *)


Ltac ignore x := idtac.

(*start tactics for forward_while unfolding *)
Ltac intro_ex_local_derives :=
(match goal with 
   | |- local (_) && exp (fun y => _) |-- _ =>
       rewrite exp_andp2; apply exp_left; let y':=fresh y in intro y'
end).

Ltac unfold_and_function_derives_left :=
(repeat match goal with 
          | |- _ && (exp _) |--  _ => fail 1
          | |- _ && (PROPx _ _) |-- _ => fail 1
          | |- _ && (?X _ _ _ _ _) |--  _ => unfold X
          | |- _ && (?X _ _ _ _) |--  _ => unfold X
          | |- _ && (?X _ _ _) |--  _ => unfold X
          | |- _ && (?X _ _) |--  _ => unfold X
          | |- _ && (?X _) |--  _ => unfold X
          | |- _ && (?X) |--  _ => unfold X
end).

Ltac unfold_and_local_derives :=
try rewrite <- local_lift2_and;
unfold_and_function_derives_left;
repeat intro_ex_local_derives;
try rewrite local_lift2_and;
repeat (try rewrite andp_assoc; rewrite canonicalize.canon9).

Ltac unfold_function_derives_right :=
(repeat match goal with 
          | |- _ |-- (exp _) => fail 1
          | |- _ |-- (PROPx _ _) => fail 1
          | |- _ |-- (?X _ _ _ _ _)  => unfold X
          | |- _ |-- (?X _ _ _ _)  => unfold X
          | |- _ |-- (?X _ _ _)  => unfold X
          | |- _ |-- (?X _ _)  => unfold X
          | |- _ |-- (?X _)  => unfold X
          | |- _ |-- (?X)  => unfold X

end).

Ltac unfold_pre_local_andp :=
(repeat match goal with 
          | |- semax _ ((local _) && exp _) _ _ => fail 1
          | |- semax _ ((local _) && (PROPx _ _)) _ _ => fail 1
          | |- semax _ ((local _) && ?X _ _ _ _ _) _ _ => unfold X at 1
          | |- semax _ ((local _) && ?X _ _ _ _) _ _ => unfold X at 1
          | |- semax _ ((local _) && ?X _ _ _) _ _ => unfold X at 1
          | |- semax _ ((local _) && ?X _ _) _ _ => unfold X at 1
          | |- semax _ ((local _) && ?X _) _ _ => unfold X at 1
          | |- semax _ ((local _) && ?X) _ _ => unfold X at 1
        end).

Ltac intro_ex_local_semax :=
(match goal with 
   | |- semax _ (local (_) && exp (fun y => _)) _ _  =>
       rewrite exp_andp2; apply extract_exists_pre; let y':=fresh y in intro y'
end).

Ltac unfold_and_local_semax :=
unfold_pre_local_andp;
repeat intro_ex_local_semax;
rewrite canonicalize.canon9.


Ltac forward_while Inv Postcond :=
  first [ignore (Inv: environ->mpred) 
         | fail 1 "Invariant (first argument to forward_while) must have type (environ->mpred)"];
  first [ignore (Postcond: environ->mpred)
         | fail 1 "Postcondition (second argument to forward_while) must have type (environ->mpred)"];
  apply semax_pre with Inv;
    [  unfold_function_derives_right 
    | (apply semax_seq with Postcond;
       [ first 
          [ apply semax_while' 
          | apply semax_while
          ]; 
          [ compute; auto 
          | unfold_and_local_derives
          | unfold_and_local_derives
          | unfold_and_local_semax
          ] 
       | simpl update_tycon 
       ])
    ]; abbreviate_semax; autorewrite with ret_assert.
(*end forward_while *)

Ltac forward_if post :=
first [ignore (post: environ->mpred) 
      | fail 1 "Invariant (first argument to forward_if) must have type (environ->mpred)"];
apply semax_seq with post;
[match goal with 
| |- @semax _ ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) 
                                 (Sifthenelse ?e _ _) _ => 
(apply semax_pre with (PROPx P (LOCALx (tc_expr Delta e :: Q) (SEPx R))));
[ | apply semax_ifthenelse_PQR; 
    [ reflexivity | | ]] || fail 2 "semax_ifthenelse_PQR did not match"
end | ].

Ltac normalize :=
 try match goal with |- context[subst] =>  autorewrite with subst typeclass_instances end;
 try match goal with |- context[ret_assert] =>  autorewrite with ret_assert typeclass_instances end;
 match goal with 
 | |- semax _ _ _ _ =>
  floyd.client_lemmas.normalize;
  repeat 
  (first [ simpl_tc_expr
         | simple apply semax_extract_PROP_True; [solve [auto] | ]
         | simple apply semax_extract_PROP; intro
         | extract_prop_in_LOCAL
         | move_from_SEP
         ]; cbv beta; msl.log_normalize.normalize)
  | |- _  => 
 (* simple apply normal_ret_assert_derives
         | simple apply normal_ret_assert_derives'
         | simple apply normal_ret_assert_derives'' *)
    floyd.client_lemmas.normalize
  end.

Ltac unfold_fold_eval_expr :=
  unfold eval_expr,eval_lvalue, eval_cast; fold eval_cast; fold eval_expr; fold eval_lvalue.

Ltac forward_setx_aux1 :=
      apply forward_setx; 
      try solve [intro rho; rewrite andp_unfold; apply andp_right; apply prop_right;
                            repeat split ].

Ltac forward_setx_aux2 id :=
           match goal with 
           | Name: name id |- _ => 
                let x:= fresh Name in intro x; unfold_fold_eval_expr; autorewrite with subst; try clear x
           | |- _ => let x:= fresh in intro x; unfold_fold_eval_expr; autorewrite with subst; try clear x
           end.

Ltac forward_setx :=
first [apply forward_setx_closed_now;
            [solve [auto 50 with closed] | solve [auto 50 with closed] | solve [auto 50 with closed]
            | try solve [intro rho; apply prop_right; repeat split]
            | try solve [intro rho; apply prop_right; repeat split]
            |  ]
        | make_sequential;
          eapply semax_post_flipped;
          [ apply forward_setx; 
            try solve [intro rho; rewrite andp_unfold; apply andp_right; apply prop_right;
                            repeat split ]
           | intros ?ek ?vl; apply after_set_special1 ]
        ].

Ltac hoist_later_in_pre :=
     match goal with |- semax _ ?P _ _ =>
       let P' := strip1_later P in apply semax_pre0 with (|> P'); [solve [auto 50 with derives] | ]
     end.

Ltac isolate_mapsto_tac e R := 
  match R with 
     | context [|> `(mapsto ?sh ?ty) ?e' _ :: ?R'] =>
          let n := length_of R in let n' := length_of R' 
             in rewrite (grab_nth_SEP (n- S n')); simpl minus; unfold nth, delete_nth;
                replace e' with (eval_expr e) by auto
     | context [`(mapsto ?sh ?ty) ?e' _ :: ?R'] =>
          let n := length_of R in let n' := length_of R' 
             in rewrite (grab_nth_SEP (n- S n')); simpl minus; unfold nth, delete_nth;
                replace e' with (eval_expr e) by auto
     | context [|> `(mapsto_ ?sh ?ty) ?e' :: ?R'] =>
          let n := length_of R in let n' := length_of R' 
             in rewrite (grab_nth_SEP (n- S n')); simpl minus; unfold nth, delete_nth;
                replace e' with (eval_expr e) by auto
     | context [`(mapsto_ ?sh ?ty) ?e' :: ?R'] =>
          let n := length_of R in let n' := length_of R' 
             in rewrite (grab_nth_SEP (n- S n')); simpl minus; unfold nth, delete_nth;
                replace e' with (eval_expr e) by auto
     end
  || fail 4 "Could not isolate `(mapsto _ _) (eval_expr " e "), or equivalent, in precondition".

Ltac intro_old_var' id :=
  match goal with 
  | Name: name id |- _ => 
        let x := fresh Name in
        intro x; unfold_fold_eval_expr; autorewrite with subst; try clear x
  | |- _ => let x := fresh "x" in 
        intro x; unfold_fold_eval_expr; autorewrite with subst; try clear x  
  end.

Ltac intro_old_var c :=
  match c with 
  | Sset ?id _ => intro_old_var' id
  | Scall (Some ?id) _ _ => intro_old_var' id
  | _ => intro x; unfold_fold_eval_expr; autorewrite with subst; try clear x
  end.

Ltac intro_old_var'' id :=
  match goal with 
  | Name: name id |- _ => 
        let x := fresh Name in
        intro x
  | |- _ => let x := fresh "x" in 
        intro x
  end.

Ltac get_global_fun_def Delta f fsig A Pre Post :=
    let VT := fresh "VT" in let GT := fresh "GT" in  
      assert (VT: (var_types Delta) ! f = None) by 
               (reflexivity || fail 1 "Variable " f " is not a function, it is an addressable local variable");
      assert (GT: (glob_types Delta) ! f = Some (Global_func (mk_funspec fsig A Pre Post)))
                    by ((unfold fsig, A, Pre, Post; simpl; reflexivity) || 
                          fail 1 "Function " f " has no specification in the type context");
     clear VT GT.


Ltac semax_call_id_tac_aux Espec Delta P Q R id f bl :=
      let fsig:=fresh "fsig" in let A := fresh "A" in let Pre := fresh "Pre" in let Post := fresh"Post" in
      evar (fsig: funsig); evar (A: Type); evar (Pre: A -> environ->mpred); evar (Post: A -> environ->mpred);
      get_global_fun_def Delta f fsig A Pre Post;
 let SCI := fresh "SCI" in
    let H := fresh in let witness := fresh "witness" in let F := fresh "Frame" in
      evar (witness:A); evar (F: list (environ->mpred)); 
      assert (SCI := semax_call_id1 Espec Delta P Q F id f 
                 (snd fsig) bl (fst fsig) A witness Pre Post 
                      (eq_refl _) (eq_refl _) I);
      assert (H: PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
                      PROPx P (LOCALx (tc_exprlist Delta (snd (split (fst fsig))) bl:: Q)
                                      (SEPx (`(Pre witness) (make_args' fsig (eval_exprlist (snd (split (fst fsig))) bl)) :: F))));
     [ unfold fsig, A, Pre, Post
     |  apply semax_pre_simple with (PROPx P
                (LOCALx (tc_exprlist Delta (snd (split (fst fsig))) bl :: Q)
                 (SEPx (`(Pre witness)  (make_args' fsig (eval_exprlist (snd (split (fst fsig))) bl)) ::
                            F))));
       [apply (semax_call_id_aux1 _ _ _ _ _ H)
       | eapply semax_post'; [ unfold  witness,F | unfold F in *; apply SCI] 
               ]];
  clear SCI; try clear H;
  unfold fsig, A, Pre, Post in *; clear fsig A Pre Post.


Ltac semax_call0_id_tac_aux Espec Delta P Q R f bl :=
      let fsig:=fresh "fsig" in let A := fresh "A" in let Pre := fresh "Pre" in let Post := fresh"Post" in
      evar (fsig: funsig); evar (A: Type); evar (Pre: A -> environ->mpred); evar (Post: A -> environ->mpred);
       get_global_fun_def Delta f fsig A Pre Post;
 let SCI := fresh "SCI" in
    let H := fresh in let witness := fresh "witness" in let F := fresh "Frame" in
      evar (witness:A); evar (F: list (environ->mpred)); 
      assert (SCI := semax_call_id0 Espec Delta P Q F f 
                  bl (fst fsig) A witness Pre Post 
                      (eq_refl _)  (eq_refl _) );
      assert (H: PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
                      PROPx P (LOCALx (tc_exprlist Delta (snd (split (fst fsig))) bl:: Q)
                                      (SEPx (`(Pre witness) (make_args' fsig (eval_exprlist (snd (split (fst fsig))) bl)) :: F))));
     [ unfold fsig, A, Pre, Post
     |  apply semax_pre_simple with (PROPx P
                (LOCALx (tc_exprlist Delta (snd (split (fst fsig))) bl :: Q)
                 (SEPx (`(Pre witness)  (make_args' fsig (eval_exprlist (snd (split (fst fsig))) bl)) ::
                            F))));
       [ apply (semax_call_id_aux1 _ _ _ _ _ H)
       | eapply semax_post'; [ unfold  witness,F | unfold F in *; apply SCI] 
               ]];
  clear SCI; try clear H;
  unfold fsig, A, Pre, Post in *; clear fsig A Pre Post.

(* BEGIN HORRIBLE1.
  The following tactic is needed because CompCert clightgen
 produces the following AST for function call:
  (Ssequence (Scall (Some id') ... ) (Sset id (Etempvar id' _)))
instead of the more natural
   (Scall id ...)
Our general tactics are powerful enough to reason about the sequence,
one statement at a time, but it is not nice to burden the user with knowing
about id'.  So we handle it all in one gulp.
 See also BEGIN HORRIBLE1 in forward_lemmas.v
*)

Ltac semax_call_id_tac_aux_x Espec Delta P Q R id id' f bl :=
         let fsig:=fresh "fsig" in let A := fresh "A" in let Pre := fresh "Pre" in let Post := fresh"Post" in
         evar (fsig: funsig); evar (A: Type); evar (Pre: A -> environ->mpred); evar (Post: A -> environ->mpred);
         get_global_fun_def Delta f fsig A Pre Post;

 let SCI := fresh "SCI" in
    let H := fresh in let x := fresh "witness" in let F := fresh "Frame" in
      evar (x:A); evar (F: list (environ->mpred)); 

      assert (SCI := semax_call_id1_x Espec Delta P Q F id id' f 
                   (snd fsig) bl (fst fsig) A x Pre Post 
                      (eq_refl _) (eq_refl _) I);
      assert (H: PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
                      PROPx P (LOCALx (tc_exprlist Delta (snd (split (fst fsig))) bl:: Q)
                                      (SEPx (`(Pre x) (make_args' fsig (eval_exprlist (snd (split (fst fsig))) bl)) :: F))));
     [ unfold fsig, A, Pre, Post
     |  apply semax_pre_simple with (PROPx P
                (LOCALx (tc_exprlist Delta (snd (split (fst fsig))) bl :: Q)
                 (SEPx (`(Pre x)  (make_args' fsig (eval_exprlist (snd (split (fst fsig))) bl)) ::
                            F))));
       [apply (semax_call_id_aux1 _ _ _ _ _ H)
       | eapply semax_post'; [ unfold  x,F | unfold F in *; 
              ( apply SCI ; [ (solve[ simpl; auto with closed]  || solve [auto with closed]) (* FIXME!*)
                                 | (*solve[simpl; auto with closed] PREMATURELY INSTANTIATES FRAME *) 
                                 | reflexivity | reflexivity | reflexivity | reflexivity ] ) ]
               ]];
  clear SCI; try clear H;
  unfold fsig, A, Pre, Post in *; clear fsig A Pre Post.

(* END HORRIBLE1.  *)

Ltac check_sequential s :=
 match s with
 | Sskip => idtac
 | Sassign _ _ => idtac
 | Sset _ _ => idtac
 | Scall _ _ _ => idtac
 | Ssequence ?s1 ?s2 => check_sequential s1; check_sequential s2
 | _ => fail
 end.

Ltac sequential := 
 match goal with
 |  |- @semax _ _ _ _ (normal_ret_assert _) => fail 2
 |  |- @semax _ _ _ ?s _ =>  check_sequential s; apply sequential
 end.

Ltac is_canonical P :=
 match P with 
 | PROPx _ (LOCALx _ (SEPx _)) => idtac
 | _ => fail 2 "precondition is not canonical (PROP _ LOCAL _ SEP _)"
 end.

Ltac bool_compute b :=
let H:= fresh in 
  assert (b=true) as H by auto; clear H. 

Ltac tac_if b T F := 
first [bool_compute b;T | F].

Definition ptr_compare e :=
match e with
| (Ebinop cmp e1 e2 ty) =>
   andb (andb (is_comparison cmp) (is_pointer_type (typeof e1))) (is_pointer_type (typeof e2))
| _ => false
end.

Ltac forward_ptr_cmp := 
first [eapply forward_ptr_compare_closed_now;
       [    solve [auto 50 with closed] 
          | solve [auto 50 with closed] 
          | solve [auto 50 with closed] 
          | solve [auto 50 with closed]
          | first [solve [auto] 
                  | (right; go_lower; apply andp_right; 
                                [ | solve [subst;cancel]];
                                apply andp_right; 
                                [ normalize 
                                | solve [subst;cancel]])]
          | reflexivity ]
       | eapply forward_ptr_compare'; try reflexivity; auto].
 
Ltac forward_setx_with_pcmp e :=
tac_if (ptr_compare e) ltac:forward_ptr_cmp ltac:forward_setx.

(* BEGIN new semax_load and semax_store tactics *************************)

Lemma semax_post3: 
  forall R' Espec Delta P c R,
    local (tc_environ (update_tycon Delta c)) && R' |-- R ->
    @semax Espec Delta P c (normal_ret_assert R') ->
    @semax Espec Delta P c (normal_ret_assert R) .
Proof.
 intros. eapply semax_post; [ | apply H0].
 intros. unfold local,lift1, normal_ret_assert.
 intro rho; normalize. eapply derives_trans; [ | apply H].
 simpl; apply andp_right; auto. apply prop_right; auto.
Qed.

Ltac ensure_normal_ret_assert :=
 match goal with 
 | |- semax _ _ _ (normal_ret_assert _) => idtac
 | |- semax _ _ _ _ => apply sequential
 end.

Definition whatever {A: Type} (x: A) := True.
Opaque whatever.
Lemma whatever_i {A: Type}: forall x: A, whatever x.
intro. apply I.
Qed.


Ltac unify_force w x :=
 first [ unify w x | unify w (`force_ptr x)].

Ltac find_equation E L n F :=
 match L with 
  | `(eq ?x) ?E' :: _ => unify_force E E'; F n (@liftx (LiftEnviron val) x) E
  | _ :: ?Y => let n' := constr:(S n) in find_equation E Y n' F
  | nil => F O E E
  end.

Ltac find_mapsto n R F eq_n xE E :=
 match R with
 | `(mapsto ?sh ?t ?x ?v2) :: _ => 
     (unify_force E (@liftx (LiftEnviron val) x) || unify xE (@liftx (LiftEnviron val) x)) ;  
    change (`(mapsto sh t x v2)) with (`(mapsto sh t) `x `v2); 
    F n E (@liftx (LiftEnviron val) x) sh (@liftx (LiftEnviron val) v2)
 | `(mapsto ?sh ?t) ?E' ?v2 :: _ => 
     (unify_force E E' || unify xE E'); 
    F n E E' sh v2
 | _ :: ?R' => let n' := constr:(S n) in find_mapsto n' R' F eq_n xE E
 | _ => fail "find_mapsto"
  end.

Lemma go_lower_lem24:
  forall rho (Q1: environ -> Prop)  Q R PQR,
  (Q1 rho -> LOCALx Q R rho |-- PQR) ->
  LOCALx (Q1::Q) R rho |-- PQR.
Proof.
   unfold LOCALx,local; super_unfold_lift; simpl; intros.
 normalize. 
 eapply derives_trans;  [ | apply (H H0)].
 normalize.
Qed.

Ltac quick_load_equality :=
 (intros ?rho; apply prop_right; unfold_lift; force_eq_tac) ||
 (apply go_lower_lem20;
  intros ?rho; 
  simpl derives; repeat (simple apply go_lower_lem24; intro);
  apply prop_right; simpl; unfold_lift; force_eq_tac) ||
  idtac.

Ltac load_aux0 n' e1' v1' sh' v2' := 
hoist_later_in_pre;
eapply semax_post3; [ |
 eapply semax_load'' with (n:=n')(sh:=sh')(v1:= v1')(v2:=v2');
  [ reflexivity | reflexivity | reflexivity | reflexivity
      | try solve [go_lower; apply prop_right; auto ] 
  | quick_load_equality |   reflexivity]];
 unfold replace_nth.

Lemma lift_field_mapsto_force_ptr:
 forall sh t fld v, `(field_mapsto sh t fld) (`force_ptr v) = 
                    `(field_mapsto sh t fld) v.
Proof.
intros. extensionality y rho. unfold_lift. rewrite field_mapsto_force_ptr.
auto.
Qed.

Ltac found_mapsto n' e1' v1' sh' v2' := idtac.

Ltac semax_load_aux F0 Q R eval_e F :=
   let E := fresh "E" in
    assert (E := whatever_i eval_e);
    simpl in E;
    match type of E with whatever ?E' => 
        clear E;
        let F := F0 O R F in
         find_equation E' Q O F
    end;
    unfold replace_nth.

Ltac semax_load_tac :=
 ensure_normal_ret_assert;
 hoist_later_in_pre;
match goal with 
  | |- @semax _ ?Delta (|> PROPx ?P (LOCALx ?Q (SEPx ?R)))
                    (Sset ?id (Ederef ?e1 _)) _ =>
   semax_load_aux find_mapsto Q R (eval_expr e1) load_aux0
end.

Lemma sem_add_ptr_int:
 forall v t i, 
   isptr v -> 
   Cop2.sem_add (tptr t) tint v (Vint (Int.repr i)) = Some (add_ptr_int t v i).
Proof.
intros. destruct v; inv H; reflexivity.
Qed.
Hint Rewrite sem_add_ptr_int using assumption : norm.

Ltac general_load_tac := 
 hoist_later_in_pre;
 eapply semax_load_37';
  [entailer;
   apply andp_right; [apply prop_right | solve [cancel] ];
    do 2 eexists; split; reflexivity].

Ltac new_load_tac :=   (* matches:  semax _ _ (Sset _ (Efield _ _ _)) _  *)
 ensure_normal_ret_assert;
 hoist_later_in_pre;
 first [
   eapply (semax_load_field_39);
   [ solve [auto 50 with closed] | solve [auto 50 with closed]
   | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity 
   | try apply trivial_typecheck; try solve [entailer]
   | solve [entailer; cancel]
   ]
   | eapply (semax_load_field_38);
   [ solve [auto 50 with closed] | solve [auto 50 with closed]
   | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity 
   | solve [go_lower; apply prop_right; try rewrite <- isptr_force_ptr'; auto]
   | solve [entailer; cancel]
   ]
  | eapply (semax_load_field_37);
   [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity 
   | try solve [entailer]
   | solve [entailer; cancel]
   ]
 | match goal with |- semax _ _ (Sset _ (Ederef (Ebinop Oadd ?e1 ?e2 _) _)) _ =>
    eapply semax_load_array with (lo:=0)(v1:=eval_expr e1)(v2:=eval_expr e2);
      [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity 
      | solve [entailer; cancel]
      | ]
    end
 | eapply semax_load_37';
   [entailer;
    try (apply andp_right; [apply prop_right | solve [cancel] ];
           do 2 eexists; split; reflexivity)
    ]
  ].

Definition numbd {A} (n: nat) (x: A) : A := x.

Lemma numbd_eq: forall A n (x: A), numbd n x = x.
Proof. reflexivity. Qed.

Fixpoint number_list {A} (k: nat)  (xs: list A): list A :=
 match xs with nil => nil | x::xs' => numbd k x :: number_list (S k) xs' end.

Lemma number_list_eq: forall {A} k (xs: list A), number_list k xs = xs.
Proof.
intros. revert k; induction xs; simpl; auto.
intro; f_equal; auto.
Qed.

Lemma numbd_derives:
 forall n (P Q: mpred), P |-- Q -> numbd n P |-- numbd n Q.
Proof. intros. apply H. Qed.
Lemma numbd_rewrite1:
  forall A B n (f: A->B) (x: A), numbd n f x = numbd n (f x).
Proof. intros. reflexivity. Qed.

Opaque numbd.

Hint Rewrite numbd_rewrite1 : norm.
Hint Resolve numbd_derives : cancel.

Lemma numbd_lift1:
  forall A n f v,
   numbd n ((@liftx (Tarrow A (LiftEnviron mpred)) f) v) = 
   (@liftx (Tarrow A (LiftEnviron mpred)) (numbd n f)) v.
Proof. reflexivity. Qed.
Lemma numbd_lift2:
  forall A B n f v1 v2 ,
   numbd n ((@liftx (Tarrow A (Tarrow B (LiftEnviron mpred))) f) v1 v2) = 
   (@liftx (Tarrow A (Tarrow B (LiftEnviron mpred))) (numbd n f)) v1 v2.
Proof. reflexivity. Qed.

Lemma semax_post_flipped3: 
  forall R' Espec Delta P c R,
    @semax Espec Delta P c (normal_ret_assert R') ->
    local (tc_environ (update_tycon Delta c)) && R' |-- R ->
    @semax Espec Delta P c (normal_ret_assert R) .
Proof.
intros; eapply semax_post3; eauto.
Qed.

Lemma semax_store_aux31:
 forall P Q1 Q R R', 
    PROPx P (LOCALx (Q1::Q) (SEPx R)) |-- fold_right sepcon emp R' ->
    PROPx P (LOCALx (Q1::Q) (SEPx R)) |-- PROPx P (LOCALx Q (SEPx R')).
Proof.
intros. 
apply andp_right. apply andp_left1; auto.
apply andp_right. apply andp_left2; apply andp_left1.
intro rho; unfold local, lift1; unfold_lift; apply prop_derives; intros [? ?]; auto.
apply H.
Qed.

Lemma semax_pre_later:
 forall P' Espec Delta P1 P2 P3 c R,
     (PROPx P1 (LOCALx (tc_environ Delta :: P2) (SEPx P3))) |-- P' ->
     @semax Espec Delta (|> P') c R  -> 
     @semax Espec Delta (|> (PROPx P1 (LOCALx P2 (SEPx P3)))) c R.
Proof.
intros.
eapply semax_pre_simple; try apply H0.
eapply derives_trans; [ | apply later_derives; apply H ].
eapply derives_trans.
2: apply later_derives; rewrite <- insert_local; apply derives_refl.
rewrite later_andp; apply andp_derives; auto; apply now_later.
Qed.

Lemma fast_entail:
  forall n P Q1 Q Rn Rn' R, 
      nth_error R n = Some Rn ->
      PROPx P (LOCALx (Q1::Q) (SEP (Rn))) |-- Rn'  ->
      PROPx P (LOCALx (Q1::Q) (SEPx R)) |-- PROPx P (LOCALx Q (SEPx (replace_nth n R Rn'))).
Proof.
intros.
go_lowerx.
specialize (H0 rho).
unfold PROPx, LOCALx, SEPx, local,lift1 in H0.
unfold_lift in H0. simpl in H0.
repeat  rewrite prop_true_andp in H0 by auto.
clear P H1 Q1 Q H3 H2.
rewrite sepcon_emp in H0.
revert R H H0; induction n; destruct R; simpl; intros; inv H;
 apply sepcon_derives; auto.
Qed.

Lemma local_lifted_reflexivity:
forall A P (x: environ -> A), P |-- local (`eq x x).
Proof. intros. intro rho. apply prop_right. hnf. reflexivity.
Qed.

Ltac new_store_tac := 
ensure_normal_ret_assert;
hoist_later_in_pre;
match goal with
| |- @semax ?Esp ?Delta (|> (PROPx ?P (LOCALx ?Q (SEPx ?R)))) 
     (Sassign (Ederef (Ebinop Oadd ?e1 ?ei _) ?t) ?e2) _ =>
  let n := fresh "n" in evar (n: nat); 
  let sh := fresh "sh" in evar (sh: share);
  let contents := fresh "contents" in evar (contents: Z -> reptype t);
  let lo := fresh "lo" in evar (lo: Z);
  let hi := fresh "hi" in evar (hi: Z);
  let a := fresh "a" in evar (a: val);
  let H := fresh in 
  assert (H: PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx (number_list O R))) 
     |-- (`(numbd n (array_at t sh contents lo hi a))) * TT);
  [unfold number_list, n, sh, contents, lo, hi, a; 
   repeat rewrite numbd_lift1; repeat rewrite numbd_lift2;
   solve [entailer; cancel]
 | clear H ];
 eapply(@semax_store_array Esp Delta n sh t contents lo hi (`a));
  unfold number_list, n, sh, contents, lo, hi, a;
  clear n sh contents lo hi a;
  [solve [auto] | reflexivity | reflexivity | hnf; intuition 
  | reflexivity
  | autorewrite with norm; try reflexivity;
    fail 4 "Cannot prove 6th premise of semax_store_array"
  | ]
 | |- semax ?Delta (|> (PROPx ?P (LOCALx ?Q (SEPx ?R)))) (Sassign (Efield ?e ?fld _) _) _ =>
  let n := fresh "n" in evar (n: nat); 
  let sh := fresh "sh" in evar (sh: share);
  let H := fresh in 
  assert (H: PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx (number_list O R))) 
     |-- (`(numbd n (field_mapsto_ sh (typeof e) fld)) (eval_lvalue e)) * TT);
  [unfold number_list, n, sh; 
   repeat rewrite numbd_lift1; repeat rewrite numbd_lift2;
   solve [entailer; cancel]
 | clear H ];
(**** 12.8 seconds to here ****)
 apply (semax_pre_later (PROPx P (LOCALx Q 
                (SEPx (replace_nth n R (`(field_mapsto_ sh (typeof e) fld) (eval_lvalue e)))))));
 [ first [eapply (fast_entail n); [reflexivity | entailer; cancel]
    | simple apply semax_store_aux31; unfold n,sh,replace_nth; entailer; solve [cancel]
    ]
 |];
(**** 14.2 seconds to here in the fast_entail case; otherwise 25.6 seconds to here *)
 eapply semax_post_flipped3;
 [ eapply (semax_store_field'' _ _ n sh); unfold n, sh in *; clear n sh;
   [auto | reflexivity | reflexivity | reflexivity 
      | try solve [repeat split; hnf; simpl; intros; congruence]
      | entailer
      | entailer
      | (apply local_lifted_reflexivity || quick_load_equality)
      | reflexivity
      | simple apply derives_refl]
 | unfold n, sh,replace_nth in *; clear n sh; try simple apply derives_refl
 ]
 (**** 21.1 seconds to here in fast_entail case,  or 32.5 seconds to here *****)
  | |- @semax _ ?Delta (|> PROPx ?P (LOCALx ?Q (SEPx ?R))) 
                     (Sassign (Ederef ?e ?t2) ?e2) _ =>
       apply (semax_pre (|> PROPx P 
                (LOCALx (tc_expr Delta e :: tc_expr Delta (Ecast e2 t2) ::Q) 
                (SEPx R))));
   [ apply later_derives; try solve [entailer!; try intuition]
   |  isolate_mapsto_tac e R;
       eapply semax_post'';  
       [ | first [eapply semax_store_PQR; 
                     [ auto | reflexivity | hnf; intuition | reflexivity ]
                   | eapply semax_store_PQR; 
                     [ auto | reflexivity | hnf; intuition | reflexivity ]
                   ]              
       ]
   ]
  | |- @semax _ ?Delta (|> PROPx ?P (LOCALx ?Q (SEPx ?R))) 
                     (Sassign (Ederef ?e ?t2) ?e2) _ =>
       apply (semax_pre_later (PROPx P 
                (LOCALx (tc_expr Delta e :: tc_expr Delta (Ecast e2 t2) ::Q) 
                (SEPx R))));
   [ solve [entailer!; try intuition]
   |  isolate_mapsto_tac e R;
       eapply semax_post'';  
       [ | first [eapply semax_store_PQR; 
                     [ auto | reflexivity | hnf; intuition | reflexivity ]
                   | eapply semax_store_PQR; 
                     [ auto | reflexivity | hnf; intuition | reflexivity ]
                   ]              
       ]
   ]
end.

(* END new semax_load and semax_store tactics *************************)

Ltac semax_logic_and_or :=
first [ eapply semax_logical_or_PQR | eapply semax_logical_and_PQR];
[ auto 50 with closed
| auto 50 with closed
| auto 50 with closed
| auto 50 with closed
| auto | auto | reflexivity
| try solve [intro rho; simpl; repeat apply andp_right; apply prop_right; auto] | ].

Ltac forward1 :=   
   match goal with |- @semax _ _ (PROPx _ (LOCALx _ (SEPx _))) _ _ => idtac 
       | |- _ => fail 2 "precondition is not canonical (PROP _ LOCAL _ SEP _)"
  end;
  match goal with 
  | |- @semax _ _ _ (Sassign (Efield _ _ _) _) _ =>      
         new_store_tac || fail 2 "new_store_tac failed"
  | |- @semax _ _ _ (Sassign (Ederef _ _) _) _ =>      
         new_store_tac || fail 2 "new_store_tac failed"
  | |- @semax _ _ _ (Sset _ (Efield _ _ _)) _ => 
(*         semax_load_tac || fail 2 "semax_load_tac failed" *)
           new_load_tac || fail 2 "new_load_tac failed"
  | |- @semax _ _ _ (Sset _ (Ederef _ _)) _ => 
         new_load_tac ||
         (* semax_load_tac ||*) fail 2 "new_load_tac failed" 
  | |- @semax _ _ _ (Sset ?id ?e) _ => 
          forward_setx_with_pcmp e || fail 2 "forward_setx failed"
  | |- @semax _ ?Delta (PROPx ?P (LOCALx ?Q ?R)) 
                                 (Sifthenelse ?e _ _) _ =>
             semax_logic_and_or ||  fail 2 "Use this tactic:  forward_if POST
                                            where POST is the post condition"
  | |- @semax _ _ _ (Sreturn _) _ => 
         repeat match goal with |- semax _ _ _ ?D => unfold D, abbreviate; clear D end;
        (eapply semax_pre; [  | apply semax_return ]; entailer)
          || fail 2 "forward1 Sreturn failed"
  | |-  @semax _ _ _ (Swhile _ _) _ => 
           fail 2 "Use this tactic:  forward_while INV POST
    where INV is the loop invariant and POST is the postcondition."
(* see comment HACK below, in forward tactic...
  | |- @semax ?Espec ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) (Scall (Some ?id) (Evar ?f _) ?bl)  _ =>
                   semax_call_id_tac_aux Espec Delta P Q R id f bl
*)
  end.


Ltac forward0 :=  (* USE FOR DEBUGGING *)
  match goal with 
  | |- @semax _ _ ?PQR (Ssequence ?c1 ?c2) ?PQR' => 
           let Post := fresh "Post" in
              evar (Post : environ->mpred);
              apply semax_seq' with Post;
               [ 
               | unfold exit_tycon, update_tycon, Post; clear Post ]
  end.

Lemma normal_ret_assert_derives'': 
  forall P Q R, P |-- R ->  normal_ret_assert (local Q && P) |-- normal_ret_assert R.
Proof. 
  intros. intros ek vl rho. apply normal_ret_assert_derives. 
 simpl. apply andp_left2. apply H.
Qed.

Lemma drop_tc_environ:
 forall Delta R, local (tc_environ Delta) && R |-- R.
Proof.
intros. apply andp_left2; auto.
Qed.

(*
Ltac redefine_Delta := 
  match goal with 
  | Delta:= _: tycontext |- @semax _ (initialized _ _) _ _ _ =>
       unfold Delta in *; clear Delta;
       match goal with |- @semax _ (?D: tycontext) _ _ _ => 
           set (Delta:=D); change tycontext in (type of Delta)
       end
  | Delta:= _: tycontext |- @semax _ (join_tycon _ _) _ _ _ =>
       unfold Delta in *; clear Delta;
       match goal with |- @semax _ (?D: tycontext) _ _ _ => 
           set (Delta:=D); change tycontext in (type of Delta)
       end
  | |- _ => idtac
end.
*)


Ltac forward_with F1 :=
match goal with
 (* BEGIN HORRIBLE2.  (see BEGIN HORRIBLE1, above)  *)
  | |- @semax ?Espec ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) 
               (Ssequence (Ssequence (Scall (Some ?id') (Evar ?f _) ?bl)
                       (Sset ?id (Etempvar ?id' _))) _) _ =>
       (* HACK ... need this extra clause, because trying to do it via the general case
          of the next clause leads to unification difficulties; maybe the general case
          will work in Coq 8.4 *)
           eapply semax_seq';
           [  semax_call_id_tac_aux_x Espec Delta P Q R id id' f bl; [ | apply derives_refl | ] 
           |  try unfold exit_tycon; 
                 simpl update_tycon; unfold map; fold @map;
            try (apply extract_exists_pre; intro_old_var'' id)
           ]; abbreviate_semax
 (* END HORRIBLE2 *)
  | |- @semax _ _ _ (Ssequence (Ssequence _ _) _) _ =>
          apply -> seq_assoc; forward_with F1
  | |- @semax ?Espec ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) (Ssequence (Scall (Some ?id) (Evar ?f _) ?bl) _) _ =>
       (* HACK ... need this extra clause, because trying to do it via the general case
          of the next clause leads to unification difficulties; maybe the general case
          will work in Coq 8.4 *)
           eapply semax_seq';
           [ semax_call_id_tac_aux Espec Delta P Q R id f bl  ; [ | apply derives_refl  ] 
           |  try unfold exit_tycon; 
                 simpl update_tycon; unfold map; fold @map;
            try (apply extract_exists_pre; intro_old_var'' id)
            ]; abbreviate_semax
  | |- @semax ?Espec ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) (Scall (Some ?id) (Evar ?f _) ?bl) _ =>
       (* HACK ... need this extra clause, because trying to do it via the general case
          of the next clause leads to unification difficulties; maybe the general case
          will work in Coq 8.4 *)
               eapply semax_post_flipped';
               [ semax_call_id_tac_aux Espec Delta P Q R id f bl  ; [ | apply derives_refl ] 
               | try (apply exp_left; intro_old_var'' id)
               ]; abbreviate_semax
  | |- @semax ?Espec ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) (Ssequence (Scall None (Evar ?f _) ?bl) _) _ =>
       (* HACK ... need this extra clause, because trying to do it via the general case
          of the next clause leads to unification difficulties; maybe the general case
          will work in Coq 8.4 *)
           eapply semax_seq';
           [ semax_call0_id_tac_aux Espec Delta P Q R f bl ; [ | apply derives_refl  ] 
           |  try unfold exit_tycon; 
                 simpl update_tycon; simpl map
            ]; abbreviate_semax
  | |- @semax ?Espec ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) (Scall None (Evar ?f _) ?bl) _ =>
       (* HACK ... need this extra clause, because trying to do it via the general case
          of the next clause leads to unification difficulties; maybe the general case
          will work in Coq 8.4 *)
           eapply semax_post_flipped';
           [ semax_call0_id_tac_aux Espec Delta P Q R f bl ; [ | apply derives_refl  ] 
           | 
            ]; abbreviate_semax
  | |- @semax _ _ _ (Ssequence ?c1 ?c2) _ => 
           let Post := fresh "Post" in
              evar (Post : environ->mpred);
              apply semax_seq' with Post;
               [ F1; unfold Post; try clear Post;
                 try (simple apply normal_ret_assert_derives'' || simple apply normal_ret_assert_derives');
                 try (simple apply drop_tc_environ || apply derives_refl)
               | try unfold exit_tycon; 
                   simpl update_tycon; simpl map;
                   try (unfold Post; clear Post);
                    unfold replace_nth; cbv beta;
                    try (apply extract_exists_pre; intro_old_var c1);
                    try simple apply elim_redundant_Delta
               ]; abbreviate_semax
  | |- @semax _ _ _ ?c1 _ => F1;
                  try (simple apply drop_tc_environ || rewrite insert_local);
                  try unfold exit_tycon; 
                  simpl update_tycon;
                  try (apply exp_left; intro_old_var c1);
                  abbreviate_semax
  end.

Ltac forward := forward_with forward1.

Lemma start_function_aux1:
  forall R1 P Q R, 
      (PROPx P (LOCALx Q (SEPx R))) * R1 = 
      (PROPx P (LOCALx Q (SEPx (R1::R)))).
Proof.
intros.
extensionality rho.
unfold PROPx, LOCALx, SEPx; normalize.
f_equal. f_equal. rewrite sepcon_comm. auto.
Qed. 

Ltac unfold_Delta := 
repeat
match goal with Delta := func_tycontext ?f ?V ?G |- _ =>
  first [unfold f in Delta | unfold V in Delta | unfold G in Delta ]
end;
 match goal with Delta := func_tycontext ?f ?V ?G |- _ =>
     change (func_tycontext f V G) with (@abbreviate _ (func_tycontext f V G)) in Delta;
      unfold func_tycontext, make_tycontext,
     make_tycontext_t, make_tycontext_v, make_tycontext_g,
      fn_temps,fn_params, fn_vars, fn_return in Delta;
     simpl in Delta
 end.

Ltac start_function := 
 match goal with |- semax_body _ _ _ ?spec => try unfold spec end;
 match goal with |- semax_body _ _ _ (pair _ (mk_funspec _ _ ?Pre _)) =>
   match Pre with 
   | (fun x => match x with (a,b) => _ end) => intros Espec [a b] 
   | (fun i => _) => intros Espec i
   end;
   simpl fn_body; simpl fn_params; simpl fn_return
 end;
 repeat match goal with |- @semax _ _ (match ?p with (a,b) => _ end * _) _ _ =>
             destruct p as [a b]
           end;
 match goal with |- @semax _ (func_tycontext ?F ?V ?G) _ _ _ => 
   set (Delta := func_tycontext F V G); unfold_Delta
 end;
  match goal with
  | |- @semax _ _ (?P * stackframe_of ?F) _ _ =>
            change (stackframe_of F) with (@emp (environ->mpred) _ _);
            rewrite sepcon_emp;
            rewrite frame_ret_assert_emp
  | |- @semax _ _ ((PROPx ?P (LOCALx ?Q (SEPx ?R))) * stackframe_of ?F) _ _ =>
        rewrite (start_function_aux1 (stackframe_of F) P Q R)
 | |- _ => idtac
  end;
 match goal with
  | |- @semax _ _ (PROPx _ _) _ _ => idtac 
  | _ => canonicalize_pre 
 end;
 repeat (apply semax_extract_PROP; intro);
 abbreviate_semax.

Opaque sepcon.
Opaque emp.
Opaque andp.

Arguments overridePost Q R !ek !vl / _ .
Arguments eq_dec A EqDec / a a' .
Arguments EqDec_exitkind !a !a'.

Ltac debug_store' := 
ensure_normal_ret_assert;
hoist_later_in_pre;
match goal with |- semax ?Delta (|> (PROPx ?P (LOCALx ?Q (SEPx ?R)))) (Sassign (Efield ?e ?fld _) _) _ =>
  let n := fresh "n" in evar (n: nat); 
  let sh := fresh "sh" in evar (sh: share);
  let H := fresh in 
  assert (H: PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx (number_list O R))) 
     |-- (`(numbd n (field_mapsto_ sh (typeof e) fld)) (eval_lvalue e)) * TT);
  [unfold number_list;
   repeat rewrite numbd_lift1; repeat rewrite numbd_lift2;
   gather_entail
  |  ]
end.

Ltac debug_store := (forward0; [debug_store' | ]) || debug_store'.
