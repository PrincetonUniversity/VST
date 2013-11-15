Require Import floyd.base.
Require Import floyd.client_lemmas.
Require Import floyd.field_mapsto.
Require Import floyd.assert_lemmas.
Require Import floyd.canonicalize floyd.forward_lemmas floyd.call_lemmas.
Require Import floyd.loadstore_lemmas.
Require Import floyd.malloc_lemmas.
Require Import floyd.array_lemmas.
Require Import floyd.entailer.
Require Import floyd.globals_lemmas.
Import Cop.

Arguments Int.unsigned n : simpl never.

Local Open Scope logic.

(* Move these elsewhere *)

Lemma expr_closed_field: forall S e f t,
  lvalue_closed_wrt_vars S e ->
  expr_closed_wrt_vars S (Efield e f t).
Proof.
 unfold lvalue_closed_wrt_vars, expr_closed_wrt_vars; intros.
 simpl.
 super_unfold_lift.
 f_equal.
 f_equal. apply H.  auto.
Qed.
Hint Resolve expr_closed_field : closed.

Lemma semax_frame1:
 forall {Espec: OracleKind} Frame Delta Delta1
     P Q c R P1 Q1 R1 P2 Q2 R2,
    semax Delta1 (PROPx P1 (LOCALx Q1 (SEPx R1))) c 
                      (normal_ret_assert (PROPx P2 (LOCALx Q2 (SEPx R2)))) ->
    Delta1 = Delta ->
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
    PROPx P1 (LOCALx Q1 (SEPx (R1 ++ Frame))) ->
    closed_wrt_modvars c (SEPx Frame) ->
    semax Delta (PROPx P (LOCALx Q (SEPx R))) c 
                      (normal_ret_assert (PROPx P2 (LOCALx Q2 (SEPx (R2++Frame))))).
Proof.
intros. subst.
eapply semax_pre.
apply H1.
apply semax_frame_PQR; auto.
Qed.

(* end of "stuff to move elsewhere" *)

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

Ltac simplify_Delta := 
let x := fresh "x" in
repeat 
 match goal with 
| |- let y := initialized ?i ?D in ?B =>
      change (let x := D in let y := initialized i x in B)
| D := _ |- let y := ?D in ?B =>  cbv delta [D]; clear D
| |- let y := @abbreviate _ ?D in ?B =>
       intro x; cbv delta [abbreviate] in x; revert x
| |- let y := update_tycon _ _ in _ => 
       intro x; simpl update_tycon in x; revert x
| |- let y := PTree.Node _ _ _ in _ =>
      intro x; cbv delta [x]; clear x
| |- let y := PTree.Leaf in _ =>
      intro x; cbv delta [x]; clear x
| |- let x := func_tycontext _ _ _ in _ =>
   intro x;
   cbv beta iota zeta delta [
     initialized temp_types
     func_tycontext make_tycontext
     make_tycontext_t make_tycontext_v make_tycontext_g
     fold_right
     fn_temps
     PTree.set PTree.get PTree.empty] in x;
  simpl in x; revert x
| |- let y := ?A in _ => cbv delta [A]
| |- semax ?D ?P ?c ?R =>
      change (let x := D in semax x P c R)
| |- ?A = _ => unfold A, abbreviate
| |- _ = ?B => unfold B, abbreviate
| |- initialized ?i _ = ?initialized ?i _ => f_equal
| |- ?A = initialized ?i ?D =>
     change (let x := D in A = initialized i x)
| |- ?A = func_tycontext ?a ?b ?c ?D =>
     change (let x := D in A = func_tycontext a b c)
| |- initialized ?i ?D = ?B =>
     change (let x := D in initialized i x = B)
| |- func_tycontext ?a ?b ?c ?D = ?B =>
     change (let x := D in func_tycontext a b c = B)
end;
repeat 
match goal with
| |- let y := initialized _ _ in _ =>
      intro x; unfold initialized in x; simpl in x;
      cbv delta [x]; clear x
| |- let y := (_, _) in _ =>
       intro x; cbv delta [x]; clear x
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
   match retty with Tvoid => False | Tcomp_ptr _ _ => False | Tarray _ _ _ => False | _ => True end ->
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
  replace (implicit_deref retty) with retty by (clear - H0; destruct retty; try contradiction; reflexivity).
 rewrite H5.
 simpl.
 unfold isCastResultType. unfold is_neutral_cast in H5.
 destruct (Cop.classify_cast retty retty); try discriminate.
 rewrite eqb_type_refl. apply I.
 unfold temp_types. unfold initialized; simpl.
 rewrite H4. simpl. rewrite PTree.gso by auto.
  replace (implicit_deref retty) with retty by (clear - H0; destruct retty; try contradiction; reflexivity).
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
end | ]; abbreviate_semax; autorewrite with ret_assert.

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
  unfold eval_expr,eval_lvalue, sem_cast; fold sem_cast; fold eval_expr; fold eval_lvalue.

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
        | apply forward_setx; 
            try solve [intro rho; rewrite andp_unfold; apply andp_right; apply prop_right;
                            repeat split ]
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
  | Ssequence _ (Sset ?id _) => intro_old_var' id
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

Lemma sequential': forall Espec Delta Pre c R Post,
  @semax Espec Delta Pre c (normal_ret_assert R) ->
  @semax Espec Delta Pre c (overridePost R Post).
Proof.
intros.
eapply semax_post0; [ | apply H].
unfold normal_ret_assert; intros ek vl rho; simpl; normalize; subst.
unfold overridePost. rewrite if_true by auto.
normalize.
Qed.

Ltac ensure_open_normal_ret_assert :=
 try simple apply sequential';
 match goal with 
 | |- semax _ _ _ (normal_ret_assert ?X) => is_evar X
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
Definition force_eq ( x y: val) := force_ptr x = force_ptr y.


Lemma force_force_eq:
  forall v, force_ptr (force_ptr v) = force_ptr v.
Proof. intros. destruct v; reflexivity. Qed.

Lemma force_eq1: forall v w, force_eq v w -> force_eq (force_ptr v) w .
Proof. unfold force_eq; intros; rewrite force_force_eq; auto. Qed.

Lemma force_eq2: forall v w, force_eq v w -> force_eq v (force_ptr w).
Proof. unfold force_eq; intros; rewrite force_force_eq; auto. Qed.

Lemma force_eq0: forall v w, v=w -> force_eq v w.
Proof. intros. subst. reflexivity. Qed.

Ltac force_eq_tac := repeat first [simple apply force_eq1 | simple apply force_eq2];
                                 try apply force_eq0;
                                 first [assumption |  reflexivity].

Ltac quick_load_equality :=
 (intros ?rho; apply prop_right; unfold_lift; force_eq_tac) ||
 (apply go_lower_lem20;
  intros ?rho; 
  simpl derives; repeat (simple apply go_lower_lem24; intro);
  apply prop_right; simpl; unfold_lift; force_eq_tac) ||
  idtac.

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
 match goal with   
 | |- semax _ _ (Sset _ (Efield ?e _ _)) _ =>
 match e with
 | Ederef _ _ => 
   (eapply (semax_load_field_40);
   [ solve [auto 50 with closed] | solve [auto 50 with closed]
   | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity 
   | solve [entailer!]
   ]) || fail 1
 | _ =>
   eapply (semax_load_field_38);
   [ solve [auto 50 with closed] | solve [auto 50 with closed]
   | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity 
   | solve [go_lower; apply prop_right; try rewrite <- isptr_force_ptr'; auto]
   | solve [entailer; cancel]
   ]
 end
 | |- semax _ _ (Sset _ (Efield _ _ _)) _ =>
  eapply (semax_load_field'');
   [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity 
   | try solve [entailer]
   | solve [entailer; cancel]
   ]
 | |- semax _ _ (Sset _ (Ederef (Ebinop Oadd ?e1 ?e2 _) _)) _ =>
    eapply semax_load_array with (lo:=0)(v1:=eval_expr e1)(v2:=eval_expr e2);
      [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity 
      | solve [entailer; cancel]
      | ]
 | |- _ => eapply semax_load_37';
   [entailer;
    try (apply andp_right; [apply prop_right | solve [cancel] ];
           do 2 eexists; split; reflexivity)
    ]
 end.

Ltac load_tac :=   (* matches:  semax _ _ (Sset _ (Efield _ _ _)) _  *)
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
  | eapply (semax_load_field'');
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

Lemma saturate_local_numbd:
 forall n (P Q : mpred), P |-- Q -> numbd n P |-- Q.
Proof. intros. apply H.
Qed.
Hint Resolve saturate_local_numbd: saturate_local.

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

Lemma numbd_lift0:
  forall n f,
   numbd n (@liftx (LiftEnviron mpred) f) = 
   (@liftx (LiftEnviron mpred)) (numbd n f).
Proof. reflexivity. Qed.
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
ensure_open_normal_ret_assert;
hoist_later_in_pre;
match goal with
| |- @semax ?Esp ?Delta (|> (PROPx ?P (LOCALx ?Q (SEPx ?R)))) 
     (Sassign (Ederef (Ebinop Oadd ?e1 ?ei _) ?t) ?e2) _ =>
  let n := fresh "n" in evar (n: nat); 
  let sh := fresh "sh" in evar (sh: share);
  let contents := fresh "contents" in evar (contents: Z -> option (reptype t));
  let lo := fresh "lo" in evar (lo: Z);
  let hi := fresh "hi" in evar (hi: Z);
  assert (PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx (number_list O R))) 
     |-- (`(numbd n (array_at t sh contents lo hi)) (eval_expr e1)) * TT) as _;
  [unfold number_list, n, sh, contents, lo, hi; 
   repeat rewrite numbd_lift0; repeat rewrite numbd_lift1; repeat rewrite numbd_lift2;
   solve [entailer; cancel]
 |  ];
  eapply(@semax_store_array Esp Delta n sh t contents lo hi);
  unfold number_list, n, sh, contents, lo, hi;
  clear n sh contents lo hi;
  [solve [auto] | reflexivity | reflexivity | reflexivity
  | autorewrite with norm; try reflexivity;
    fail 4 "Cannot prove 6th premise of semax_store_array"
  | ]
 | |- semax ?Delta (|> (PROPx ?P (LOCALx ?Q (SEPx ?R)))) (Sassign (Efield ?e ?fld _) _) _ =>
  let n := fresh "n" in evar (n: nat); 
  let sh := fresh "sh" in evar (sh: share);
  assert (PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx (number_list O R))) 
     |-- (`(numbd n (field_mapsto_ sh (typeof e) fld)) (eval_lvalue e)) * TT) as _;
  [unfold number_list, n, sh; 
   repeat rewrite numbd_lift1; repeat rewrite numbd_lift2;
   solve [entailer; cancel]
 |  ];
(**** 12.8 seconds to here ****)
 apply (semax_pre_later (PROPx P (LOCALx Q 
                (SEPx (replace_nth n R (`(field_mapsto_ sh (typeof e) fld) (eval_lvalue e)))))));
 [ eapply (fast_entail n); [reflexivity | entailer; cancel] | ];
(**** 14.2 seconds to here  *)
 eapply (semax_store_field'' _ _ n sh); 
   [auto | reflexivity | reflexivity 
      | try solve [repeat split; hnf; simpl; intros; congruence]
      | entailer
      | entailer
      | (apply local_lifted_reflexivity || quick_load_equality)
      | reflexivity
      | simple apply derives_refl ];
  unfold n,sh; clear n sh
 (**** 21.1 seconds to here *****)
  | |- @semax ?Espec ?Delta (|> PROPx ?P (LOCALx ?Q (SEPx ?R))) 
                     (Sassign ?e ?e2) _ =>

 let n := fresh "n" in evar (n: nat); 
  let sh := fresh "sh" in evar (sh: share);
  assert (PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx (number_list O R))) 
     |-- (`(numbd n (mapsto_ sh (typeof e))) (eval_lvalue e)) * TT) as _;
  [ unfold number_list, n, sh; 
   repeat rewrite numbd_lift1; repeat rewrite numbd_lift2;
   solve [entailer; cancel]
  |  ];
  eapply (@semax_store_nth Espec n Delta P Q R e e2);
    (unfold n,sh; clear n sh);
     [reflexivity | reflexivity |solve [entailer; cancel] | solve [auto] 
     | try solve [entailer!] ]
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

Ltac forward_return :=
     repeat match goal with |- semax _ _ _ ?D => unfold D, abbreviate; clear D end;
     (eapply semax_pre; [  | apply semax_return ]; entailer).

Ltac forward_ifthenelse :=
           semax_logic_and_or 
           ||  fail 2 "Use this tactic:  forward_if POST, where POST is the post condition".

Ltac forward_while_complain :=
           fail 2 "Use this tactic:  forward_while INV POST,
    where INV is the loop invariant and POST is the postcondition.".

Ltac forward_compound_call :=
  idtac; (* need this to make it sufficiently lazy *)
   match goal with |-  @semax ?Espec ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) 
               (Ssequence (Scall (Some ?id') (Evar ?f _) ?bl)
                       (Sset ?id (Etempvar ?id' _))) _ =>
           semax_call_id_tac_aux_x Espec Delta P Q R id id' f bl; [ | apply derives_refl | ] 
end.

Ltac forward_call_id :=
  idtac; (* need this to make it sufficiently lazy *)
 match goal with 
  | |- @semax ?Espec ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) (Scall (Some ?id) (Evar ?f _) ?bl) _ =>
            semax_call_id_tac_aux Espec Delta P Q R id f bl  ; [ | apply derives_refl ]
  | |- @semax ?Espec ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) (Scall None (Evar ?f _) ?bl) _ =>
           semax_call0_id_tac_aux Espec Delta P Q R f bl ; [ | apply derives_refl  ]
 end.

Ltac forward_skip := apply semax_skip.

Ltac no_loads_expr e as_lvalue :=
 match e with
 | Econst_int _ _ => idtac
 | Econst_float _ _ => idtac
 | Econst_long _ _ => idtac
 | Evar _ _ => match as_lvalue with true => idtac end
 | Etempvar _ _ => idtac
 | Eaddrof ?e1 _ => no_loads_expr e1 true
 | Eunop _ ?e1 _ => no_loads_expr e1 as_lvalue
 | Ebinop _ ?e1 ?e2 _ => no_loads_expr e1 as_lvalue; no_loads_expr e2 as_lvalue
 | Ecast ?e1 _ => no_loads_expr e1 as_lvalue
 | Efield ?e1 _ _ => match as_lvalue with true =>
                              no_loads_expr e1 true
                              end
 | _ =>
            let r := fresh "The_expression_or_parameter_list_must_not_contain_any_loads_but_the_following_subexpression_is_an_implicit_or_explicit_load_Please_refactor_this_stament_of_your_program" 
           in pose (r:=e) 
end.

Ltac no_loads_exprlist e :=
 match e with
 | ?e1::?er => no_loads_expr e1 false; no_loads_exprlist er
 | nil => idtac
 end.

Ltac forward1 s :=  (* Note: this should match only those commands that
                                     can take a normal_ret_assert *)
  lazymatch s with 
  | Sassign _ _ => new_store_tac
  | Sset _ (Efield ?e _ ?t) => 
      no_loads_expr e true;
      first [unify true (match t with Tarray _ _ _ => true | _ => false end);
               forward_setx
              |new_load_tac]
  | Sset _ (Ederef ?e _) => no_loads_expr e true; new_load_tac
  | Sset _ (Evar _ _) => new_load_tac
  | Sset _ ?e => no_loads_expr e false; (bool_compute e; forward_ptr_cmp) || forward_setx
  | Sifthenelse ?e _ _ => no_loads_expr e false; forward_ifthenelse
  |  Swhile _ _ => forward_while_complain
  |  Ssequence (Scall (Some ?id') (Evar _ _) ?el) (Sset _ (Etempvar ?id' _)) => 
          no_loads_exprlist el; forward_compound_call
  | Scall _ (Evar _ _) ?el =>  no_loads_exprlist el; forward_call_id
  | Sskip => forward_skip
  end.

Ltac derives_after_forward :=
             first [ simple apply derives_refl 
                     | simple apply drop_tc_environ
                     | simple apply normal_ret_assert_derives'' 
                     | simple apply normal_ret_assert_derives'
                     | idtac].

Ltac normalize_postcondition :=
 match goal with 
 | P := _ |- semax _ _ _ ?P =>
     unfold P, abbreviate; clear P; normalize_postcondition
 | |- semax _ _ _ (normal_ret_assert _) => idtac
 | |- _ => apply sequential
  end.

Ltac forward_break :=
eapply semax_pre; [ | apply semax_break ];
  unfold_abbrev_ret;
  autorewrite with ret_assert.

Ltac forward_with F1 :=
 match goal with 
  | |- semax _ _ (Ssequence (Sreturn _) _) _ =>
            apply semax_seq with FF; [ | apply semax_ff];
            forward_return
  | |- semax _ _ (Sreturn _) _ =>  forward_return
  | |- semax _ _ (Ssequence Sbreak _) _ =>
            apply semax_seq with FF; [ | apply semax_ff];
            forward_break
  | |- semax _ _ Sbreak _ => forward_break
  | |- semax _ _ (Ssequence ?c _) _ =>
    let ftac := F1 c in
       ((eapply semax_seq'; 
             [ftac; derives_after_forward
             | unfold replace_nth; cbv beta;
               try (apply extract_exists_pre; intro_old_var c);
               abbreviate_semax
             ]) 
        ||  fail 0)  (* see comment FORWARD_FAILOVER below *)
  | |- semax _ _ (Ssequence (Ssequence _ _) _) _ =>
       apply -> seq_assoc; forward_with F1
  | |- semax _ _ ?c _ =>
     let ftac := F1 c in
      normalize_postcondition;
       eapply semax_post_flipped3;
             [ftac; derives_after_forward
             | try rewrite exp_andp2;
               try (apply exp_left; intro_old_var c);
               try rewrite insert_local
             ] 
end.

(* FORWARD_FAILOVER:
  The first clause of forward_with starts by calling F1, and if it matches,
  then, in principle, no other clause of forward_with should be needed.
  The way to enforce "no other clause" is by writing "fail 1".
  However, there is a small bug in the forward_compound_call tactic:
  if the second assignment has an _implicit_ cast, then the lemma
  semax_call_id1_x  is just a bit too weak to work.   An example
  that demonstrates this is in verif_queue.v, in make_elem at the
  call to mallocN.   Until this lemma
  is generalized, then failover is necessary, so we have "fail 0" instead
  of "fail 1".

  Related remark: 
  In the tactic semax_call_id_tac_aux_x, the "eapply semax_post' " 
   is probably redundant, now that forward1 is always called with
 a standardized postcondition of (normal_ret_assert ?evar).
*)

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
 abbreviate_semax;
 try expand_main_pre.

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
