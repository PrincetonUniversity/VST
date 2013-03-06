Load loadpath.
Require Import floyd.base.
Require Import floyd.client_lemmas.
Require Import floyd.field_mapsto.
Require Import floyd.assert_lemmas.
Require Export floyd.canonicalize floyd.forward_lemmas floyd.call_lemmas.
Import Cop.

Local Open Scope logic.

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
 forall Delta P Q R ret ret' id retty bl argsig A x Pre Post
   (GLBL: (var_types Delta) ! id = None),
   (glob_types Delta) ! id = Some (Global_func (mk_funspec (argsig,retty) A Pre Post)) ->
   match retty with Tvoid => False | _ => True end ->
  forall
   (CLOSQ: Forall (closed_wrt_vars (eq ret')) Q)
   (CLOSR: Forall (closed_wrt_vars (eq ret')) R),
   type_is_volatile retty = false -> 
   (temp_types Delta) ! ret' = Some (retty, false) ->
   is_neutral_cast retty retty = true ->
   match (temp_types Delta) ! ret with Some (t,_) => eqb_type t retty | None => false end = true ->
  semax Delta (PROPx P (LOCALx (tc_exprlist Delta (snd (split argsig)) bl :: Q) (SEPx (`(Pre x) (make_args' (argsig,retty) (eval_exprlist (snd (split argsig)) bl)) :: R))))
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
 apply (semax_call_id1' _ P Q R ret' _ _ bl _ _ x _ _ GLBL H H0 CLOSQ CLOSR).
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
 simpl. rewrite eqb_type_refl. apply I.
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
 intro rho; unfold LOCALx, local,lift1.
change SEPx with SEPx'.
 simpl. 
  normalize. unfold_lift.
 apply sepcon_derives; auto.
 repeat rewrite subst_lift1'.
(*  normalize. *)
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


Ltac forward_while Inv Postcond :=
  apply semax_pre with Inv;
    [ | (apply semax_seq with Postcond;
            [ apply semax_while' ; [ compute; auto | | | ] 
            | simpl update_tycon ])
        || (repeat match goal with 
         | |- semax _ (exp _) _ _ => fail 1
         | |- semax _ (?X _ _ _ _ _) _ _ => unfold X
         | |- semax _ (?X _ _ _ _) _ _ => unfold X
         | |- semax _ (?X _ _ _) _ _ => unfold X
         | |- semax _ (?X _ _) _ _ => unfold X
         | |- semax _ (?X _) _ _ => unfold X
         | |- semax _ ?X _ _ => unfold X
        end;
          match goal with
          | |- semax _  (exp (fun y => _)) _ _ =>
             (* Note: matching in this special way uses the user's name 'y'  as a hypothesis *)
              apply semax_seq with Postcond ;
               [apply semax_whilex;
                  [ compute; auto 
                  | let y':=fresh y in intro y'
                  | let y':=fresh y in intro y'
                  | let y':=fresh y in intro y';
                     match goal with |- semax _ _ _ (loop1_ret_assert ?S _) =>
                             change S with Inv
                     end
                  ]
               | simpl update_tycon ]
          | |- semax _  (exp (fun y1 => (exp (fun y2 => _)))) _ _ =>
             (* Note: matching in this special way uses the user's name 'y'  as a hypothesis *)
              apply semax_seq with Postcond ;
               [apply semax_whilex2; 
                 [ compute; auto
                 | intros y1 y2 
                 | intros y1 y2 
                 | intros y1 y2; 
                     match goal with |- semax _ _ _ (loop1_ret_assert ?S _) =>
                             change S with Inv
                     end
                 ]
               | simpl update_tycon ]
        end)

   ].

Ltac normalize :=
 try match goal with |- context[subst] =>  autorewrite with subst end;
 try match goal with |- context[ret_assert] =>  autorewrite with ret_assert end;
 match goal with 
 | |- semax _ _ _ _ =>
  msl.log_normalize.normalize;
  repeat 
  (first [ apply normal_ret_assert_derives
         | apply normal_ret_assert_derives'
         | apply normal_ret_assert_derives''
         | simpl_tc_expr
         | flatten_sepcon_in_SEP
          | apply semax_extract_PROP_True; [solve [auto] | ]
          | apply semax_extract_PROP; intro
         | extract_prop_in_LOCAL
         | extract_exists_in_SEP
         ]; cbv beta; msl.log_normalize.normalize)
  | |- _  => msl.log_normalize.normalize
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

Ltac isolate_field_tac_deref e fld R := 
  match R with 
     | context [|> `(field_mapsto ?sh ?struct fld) ?e' ?v :: ?R'] =>
          let n := length_of R in let n' := length_of R' 
             in rewrite (grab_nth_SEP (n- S n')); simpl minus; unfold nth, delete_nth;
                change e' with (eval_expr e)
     | context [ `(field_mapsto ?sh ?struct fld) ?e' ?v  :: ?R'] =>
          let n := length_of R in let n' := length_of R' 
             in rewrite (grab_nth_SEP (n- S n')); simpl minus; unfold nth, delete_nth;
                change e' with (eval_expr e)
     end.

Ltac isolate_field_tac e fld R := 
  match R with 
     | context [|> `(field_mapsto ?sh ?struct fld) ?e' ?v :: ?R'] =>
          let n := length_of R in let n' := length_of R' 
             in rewrite (grab_nth_SEP (n- S n')); simpl minus; unfold nth, delete_nth;
                change e' with (eval_lvalue e)
     | context [ `(field_mapsto ?sh ?struct fld) ?e' ?v  :: ?R'] =>
          let n := length_of R in let n' := length_of R' 
             in rewrite (grab_nth_SEP (n- S n')); simpl minus; unfold nth, delete_nth;
                change e' with (eval_lvalue e)
     end.

Ltac hoist_later_in_pre :=
     match goal with |- semax _ ?P _ _ =>
       let P' := strip1_later P in apply semax_pre0 with (|> P'); [solve [auto 50 with derives] | ]
     end.

Ltac semax_field_tac :=
match goal with
 |  |- semax ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R)))
                    (Sset ?id (Efield (Ederef ?e _) ?fld _)) _ =>
     apply (semax_pre_simple (PROPx P (LOCALx (tc_expr Delta e :: Q) (SEPx R))));
     [ apply semax_load_assist1; [reflexivity]
     | isolate_field_tac_deref e fld R; hoist_later_in_pre;
       eapply semax_post'; [ | eapply semax_load_field_deref; 
                               [ reflexivity | reflexivity | simpl; reflexivity 
                               | reflexivity | reflexivity ]]
     ]
 |  |- semax ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R)))
                    (Sset ?id (Efield ?e ?fld _)) _ =>
     apply (semax_pre_simple (PROPx P (LOCALx (tc_lvalue Delta e :: Q) (SEPx R))));
     [ apply semax_load_assist1; [reflexivity]
     | isolate_field_tac e fld R; hoist_later_in_pre;
       eapply semax_post'; [ | eapply semax_load_field'; 
                               [ reflexivity | reflexivity | simpl; reflexivity 
                               | reflexivity | reflexivity ] ]
     ]
end.

Lemma mapsto_mapsto_: forall sh t v v',
   mapsto sh t v v' |-- mapsto_ sh t v.
Proof. unfold mapsto, mapsto_; intros.
apply exp_right with v'. apply andp_left2; auto.
Qed.

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
     end.

Ltac isolate_mapsto__tac_deref e fld R := 
  match R with 
     | context [|> `(field_mapsto ?sh ?struct fld) ?e' _ :: ?R'] =>
          let n := length_of R in let n' := length_of R' 
             in rewrite (grab_nth_SEP (n- S n')); simpl minus; unfold nth, delete_nth;
                change (lift1 force_ptr e') with (eval_lvalue e);
                apply later_field_mapsto_mapsto__at1
     | context [ `(field_mapsto ?sh ?struct fld) ?e' _  :: ?R'] =>
          let n := length_of R in let n' := length_of R' 
             in rewrite (grab_nth_SEP (n- S n')); simpl minus; unfold nth, delete_nth;
                change (lift1 force_ptr e') with (eval_lvalue e);
                apply field_mapsto_mapsto__at1
     | context [|> `(field_mapsto_ ?sh ?struct fld) ?e' :: ?R'] =>
          let n := length_of R in let n' := length_of R' 
             in rewrite (grab_nth_SEP (n- S n')); simpl minus; unfold nth, delete_nth;
                change (lift1 force_ptr e') with (eval_lvalue e)
     | context [ `(field_mapsto_ ?sh ?struct fld) ?e'  :: ?R'] =>
          let n := length_of R in let n' := length_of R' 
             in rewrite (grab_nth_SEP (n- S n')); simpl minus; unfold nth, delete_nth; 
                change (lift1 force_ptr e') with (eval_lvalue e)
     end.


Ltac isolate_mapsto__tac e fld R := 
  match R with 
     | context [|> `(field_mapsto ?sh ?struct fld) ?e' _ :: ?R'] =>
          let n := length_of R in let n' := length_of R' 
             in rewrite (grab_nth_SEP (n- S n')); simpl minus; unfold nth, delete_nth;
                change e' with (eval_lvalue e);
                apply later_field_mapsto_mapsto__at1
     | context [ `(field_mapsto ?sh ?struct fld) ?e' _  :: ?R'] =>
          let n := length_of R in let n' := length_of R' 
             in rewrite (grab_nth_SEP (n- S n')); simpl minus; unfold nth, delete_nth;
                change e' with (eval_lvalue e);
                apply field_mapsto_mapsto__at1
     | context [|> `(field_mapsto_ ?sh ?struct fld) ?e' :: ?R'] =>
          let n := length_of R in let n' := length_of R' 
             in rewrite (grab_nth_SEP (n- S n')); simpl minus; unfold nth, delete_nth;
                change e' with (eval_lvalue e)
     | context [ `(field_mapsto_ ?sh ?struct fld) ?e'  :: ?R'] =>
          let n := length_of R in let n' := length_of R' 
             in rewrite (grab_nth_SEP (n- S n')); simpl minus; unfold nth, delete_nth; 
                change e' with (eval_lvalue e)
     end.


Ltac store_field_tac :=
  match goal with
  | |- semax ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) 
                     (Sassign (Efield (Ederef ?e ?t3) ?fld ?t2) ?e2) _ =>
       (apply (semax_pre (PROPx P 
                (LOCALx (tc_expr Delta e :: tc_expr Delta (Ecast e2 t2) ::Q) 
                (SEPx R))));
   [ try solve [go_lower2; apply andp_right;
                    [apply prop_right; intuition | apply derives_refl]]
   | isolate_mapsto__tac_deref (Ederef e t3) fld R; hoist_later_in_pre;
       eapply semax_post''; [ | eapply semax_store_field_deref; 
                                             [ auto | reflexivity | reflexivity | reflexivity |
                                             try solve [hnf; intuition]] ]
    ]) || fail 1
  | |- semax ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) 
                     (Sassign (Efield ?e ?fld ?t2) ?e2) _ =>
       apply (semax_pre (PROPx P 
                (LOCALx (tc_lvalue Delta e :: tc_expr Delta (Ecast e2 t2) ::Q) 
                (SEPx R))));
   [  try solve [go_lower2; apply andp_right;
                    [apply prop_right; intuition | apply derives_refl]]
   |  isolate_mapsto__tac e fld R; hoist_later_in_pre;
       eapply semax_post''; [ | eapply semax_store_field'; 
                                             [ auto | reflexivity | reflexivity | reflexivity |
                                             try solve [hnf; intuition] ]]
   ]
  end.

Ltac store_tac :=
 match goal with
  | |- semax ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) 
                     (Sassign (Ederef ?e ?t2) ?e2) _ =>
       apply (semax_pre (PROPx P 
                (LOCALx (tc_expr Delta e :: tc_expr Delta (Ecast e2 t2) ::Q) 
                (SEPx R))));
   [ try solve [go_lower2; apply andp_right;
                    [apply prop_right; intuition | apply derives_refl]]
   |  isolate_mapsto_tac e R; hoist_later_in_pre;
       eapply semax_post'';  
       [ | first [eapply semax_store_PQR; 
                     [ auto | reflexivity | hnf; intuition | reflexivity ]
                   | eapply semax_store_PQR; 
                     [ auto | reflexivity | hnf; intuition | reflexivity ]
                   ]              
       ]
   ]
  end.

Lemma semax_load_assist2:
 forall P Q1 Q2 Q R,
  PROPx P (LOCALx (Q1::Q) (SEPx R)) |-- local Q2 ->
  PROPx P (LOCALx (Q1::Q) (SEPx R)) |-- PROPx P (LOCALx (Q2::Q) (SEPx R)).
Proof.
intros.
apply derives_trans with
 (local Q2 && PROPx P (LOCALx Q (SEPx R))).
apply andp_right; auto.
apply andp_derives; auto.
apply andp_derives; auto.
unfold local,lift1; unfold_lift; intro rho; simpl.
apply prop_derives. intros [_ ?]; auto.
normalize.
Qed.


Ltac load_array_tac :=
match goal with |- semax ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R)))
                    (Sset ?id (Ederef (Ebinop Oadd ?e1 ?e2 ?t1) _)) _ =>
     apply (semax_pre 
              (PROPx P (LOCALx (tc_expr Delta (Ebinop Oadd e1 e2 t1) :: Q) (SEPx R))));
     [ ((apply semax_load_assist1; [reflexivity])
        || apply semax_load_assist2; try solve [go_lower; normalize] )
     | isolate_mapsto_tac (Ebinop Oadd e1 e2 t1) R; hoist_later_in_pre;
       eapply semax_post'; [ | eapply semax_load'; solve [simpl; reflexivity]]
     ]
end.

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

Ltac semax_call_id_tac_aux Delta P Q R id f bl :=
   let VT := fresh "VT" in let GT := fresh "GT" in 
         let fsig:=fresh "fsig" in let A := fresh "A" in let Pre := fresh "Pre" in let Post := fresh"Post" in
         evar (fsig: funsig); evar (A: Type); evar (Pre: A -> environ->mpred); evar (Post: A -> environ->mpred);
      assert (VT: (var_types Delta) ! f = None) by reflexivity;
      assert (GT: (glob_types Delta) ! f = Some (Global_func (mk_funspec fsig A Pre Post)))
                    by (unfold fsig, A, Pre, Post; simpl; reflexivity);
 let SCI := fresh "SCI" in
    let H := fresh in let witness := fresh "witness" in let F := fresh "Frame" in
      evar (witness:A); evar (F: list (environ->mpred)); 
      assert (SCI := semax_call_id1 Delta P Q F id f 
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
  clear SCI VT GT; try clear H;
  unfold fsig, A, Pre, Post in *; clear fsig A Pre Post.


Ltac semax_call0_id_tac_aux Delta P Q R f bl :=
   let VT := fresh "VT" in let GT := fresh "GT" in 
         let fsig:=fresh "fsig" in let A := fresh "A" in let Pre := fresh "Pre" in let Post := fresh"Post" in
         evar (fsig: funsig); evar (A: Type); evar (Pre: A -> environ->mpred); evar (Post: A -> environ->mpred);
      assert (VT: (var_types Delta) ! f = None) by reflexivity;
      assert (GT: (glob_types Delta) ! f = Some (Global_func (mk_funspec fsig A Pre Post)))
                    by (unfold fsig, A, Pre, Post; simpl; reflexivity);
 let SCI := fresh "SCI" in
    let H := fresh in let witness := fresh "witness" in let F := fresh "Frame" in
      evar (witness:A); evar (F: list (environ->mpred)); 
      assert (SCI := semax_call_id0 Delta P Q F f 
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
  clear SCI VT GT; try clear H;
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

Ltac semax_call_id_tac_aux_x Delta P Q R id id' f bl :=
   let VT := fresh "VT" in let GT := fresh "GT" in 
         let fsig:=fresh "fsig" in let A := fresh "A" in let Pre := fresh "Pre" in let Post := fresh"Post" in
         evar (fsig: funsig); evar (A: Type); evar (Pre: A -> environ->mpred); evar (Post: A -> environ->mpred);

      assert (VT: (var_types Delta) ! f = None) by reflexivity;
      assert (GT: (glob_types Delta) ! f = Some (Global_func (mk_funspec fsig A Pre Post)))
                    by (unfold fsig, A, Pre, Post; simpl; reflexivity);

 let SCI := fresh "SCI" in
    let H := fresh in let x := fresh "witness" in let F := fresh "Frame" in
      evar (x:A); evar (F: list (environ->mpred)); 

      assert (SCI := semax_call_id1_x Delta P Q F id id' f 
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
  clear SCI VT GT; try clear H;
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
 |  |- semax _ _ _ (normal_ret_assert _) => fail 2
 |  |- semax _ _ ?s _ =>  check_sequential s; apply sequential
 end.

Ltac redefine_Delta := 
  match goal with 
  | Delta:= _: tycontext |- semax (initialized _ _) _ _ _ =>
       unfold Delta in *; clear Delta;
       match goal with |- semax (?D: tycontext) _ _ _ => 
           set (Delta:=D); change tycontext in (type of Delta)
       end
  | Delta:= _: tycontext |- semax (join_tycon _ _) _ _ _ =>
       unfold Delta in *; clear Delta;
       match goal with |- semax (?D: tycontext) _ _ _ => 
           set (Delta:=D); change tycontext in (type of Delta)
       end
  | |- _ => idtac
end.

Ltac is_canonical P :=
 match P with 
 | PROPx _ (LOCALx _ (SEPx _)) => idtac
 | _ => fail 2 "precondition is not canonical (PROP _ LOCAL _ SEP _)"
 end.

Ltac forward1 :=   
   match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx _))) _ _ => idtac 
       | |- _ => fail 2 "precondition is not canonical (PROP _ LOCAL _ SEP _)"
  end;
  match goal with 
  | |- semax _ _ (Sassign (Efield _ _ _) _) _ =>      store_field_tac
  | |- semax _ _ (Sassign (Ederef _ _) _) _ =>      store_tac
  | |- semax _ _ (Sset _ (Efield _ _ _)) _ => semax_field_tac || fail 2
  | |- semax _ _ (Sset _ (Ederef _ _)) _ => load_array_tac || fail 2
  | |- semax _ _ (Sset ?id ?e) _ => forward_setx
  | |- semax ?Delta (PROPx ?P (LOCALx ?Q ?R)) 
                                 (Sifthenelse ?e _ _) _ =>
            apply semax_pre
                     with (PROPx P (LOCALx (tc_expr Delta e :: Q) R));
             [ | apply semax_ifthenelse_PQR; [ reflexivity | | ]]
  | |- semax _ _ (Sreturn _) _ => 
                    eapply semax_pre_simple; [ go_lower1 | apply semax_return ]
(* see comment HACK below, in forward tactic...
  | |- semax ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) (Scall (Some ?id) (Evar ?f _) ?bl)  _ =>
                   semax_call_id_tac_aux Delta P Q R id f bl
*)
  end.

Ltac forward0 :=  (* USE FOR DEBUGGING *)
  match goal with 
  | |- semax _ ?PQR (Ssequence ?c1 ?c2) ?PQR' => 
           let Post := fresh "Post" in
              evar (Post : environ->mpred);
              apply semax_seq' with Post;
               [ 
               | unfold exit_tycon, update_tycon, Post; clear Post ]
  end.

Ltac forward :=
match goal with
 (* BEGIN HORRIBLE2.  (see BEGIN HORRIBLE1, above)  *)
  | |- semax ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) 
               (Ssequence (Ssequence (Scall (Some ?id') (Evar ?f _) ?bl)
                       (Sset ?id (Etempvar ?id' _))) _) _ =>
       (* HACK ... need this extra clause, because trying to do it via the general case
          of the next clause leads to unification difficulties; maybe the general case
          will work in Coq 8.4 *)
           eapply semax_seq';
           [  semax_call_id_tac_aux_x Delta P Q R id id' f bl; [ | apply derives_refl | ] 
           |  try unfold exit_tycon; 
                 simpl update_tycon; unfold map; fold @map;
            try (apply extract_exists_pre; intro_old_var'' id)
           ]
 (* END HORRIBLE2 *)
  | |- semax _ _ (Ssequence (Ssequence _ _) _) _ =>
          apply -> seq_assoc; forward
  | |- semax ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) (Ssequence (Scall (Some ?id) (Evar ?f _) ?bl) _) _ =>
       (* HACK ... need this extra clause, because trying to do it via the general case
          of the next clause leads to unification difficulties; maybe the general case
          will work in Coq 8.4 *)
           eapply semax_seq';
           [ semax_call_id_tac_aux Delta P Q R id f bl  ; [ | apply derives_refl  ] 
           |  try unfold exit_tycon; 
                 simpl update_tycon; unfold map; fold @map;
            try (apply extract_exists_pre; intro_old_var'' id)
            ]
  | |- semax ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) (Scall (Some ?id) (Evar ?f _) ?bl) _ =>
       (* HACK ... need this extra clause, because trying to do it via the general case
          of the next clause leads to unification difficulties; maybe the general case
          will work in Coq 8.4 *)
               eapply semax_post_flipped';
               [ semax_call_id_tac_aux Delta P Q R id f bl  ; [ | apply derives_refl ] 
               | try (apply exp_left; intro_old_var'' id)
               ]

  | |- semax ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) (Ssequence (Scall None (Evar ?f _) ?bl) _) _ =>
       (* HACK ... need this extra clause, because trying to do it via the general case
          of the next clause leads to unification difficulties; maybe the general case
          will work in Coq 8.4 *)
           eapply semax_seq';
           [ semax_call0_id_tac_aux Delta P Q R f bl ; [ | apply derives_refl  ] 
           |  try unfold exit_tycon; 
                 simpl update_tycon; simpl map
            ]
  | |- semax ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) (Scall None (Evar ?f _) ?bl) _ =>
       (* HACK ... need this extra clause, because trying to do it via the general case
          of the next clause leads to unification difficulties; maybe the general case
          will work in Coq 8.4 *)
           eapply semax_post_flipped';
           [ semax_call0_id_tac_aux Delta P Q R f bl ; [ | apply derives_refl  ] 
           | 
            ]
  | |- semax _ _ (Ssequence ?c1 ?c2) _ => 
           let Post := fresh "Post" in
              evar (Post : environ->mpred);
              apply semax_seq' with Post;
               [ forward1; unfold Post; 
                 try apply normal_ret_assert_derives';
                 try apply derives_refl
               | try unfold exit_tycon; 
                   simpl update_tycon; simpl map;
                   try (unfold Post; clear Post);
                    try (apply extract_exists_pre; intro_old_var c1);
                    try apply elim_redundant_Delta;
                    redefine_Delta
               ]
  | |- semax _ _ ?c1 _ => forward1;
                  try unfold exit_tycon; 
                  simpl update_tycon;
                  try (apply exp_left; intro_old_var c1)
  end.

Lemma start_function_aux1:
  forall R1 P Q R, 
      (PROPx P (LOCALx Q (SEPx R))) * R1 = 
      (PROPx P (LOCALx Q (SEPx (R1::R)))).
Proof.
intros.
extensionality rho.
change SEPx with SEPx'.
unfold PROPx, LOCALx, SEPx'; normalize.
f_equal. f_equal. rewrite sepcon_comm. auto.
Qed. 


Ltac start_function := 
 match goal with |- semax_body _ _ _ ?spec => try unfold spec end;
 match goal with |- semax_body _ _ _ (pair _ (mk_funspec _ _ ?Pre _)) =>
   match Pre with 
   | (fun x => match x with (a,b) => _ end) => intros [a b] 
   | (fun i => _) => intro i
   end;
   simpl fn_body; simpl fn_params; simpl fn_return
 end;
 repeat match goal with |- semax _ (match ?p with (a,b) => _ end * _) _ _ =>
             destruct p as [a b]
           end;
 match goal with |- semax (func_tycontext ?F ?V ?G) _ _ _ => 
   set (Delta := func_tycontext F V G)
 end;
  match goal with
  | |- semax _ (?P * stackframe_of ?F) _ _ =>
            change (stackframe_of F) with (@emp (environ->mpred) _ _);
            rewrite sepcon_emp;
            rewrite frame_ret_assert_emp
  | |- semax _ ((PROPx ?P (LOCALx ?Q (SEPx ?R))) * stackframe_of ?F) _ _ =>
        rewrite (start_function_aux1 (stackframe_of F) P Q R)
 | |- _ => idtac
  end;
 match goal with
  | |- semax _ (PROPx _ _) _ _ => idtac 
  | _ => canonicalize_pre 
 end;
 repeat (apply semax_extract_PROP; intro).

Opaque sepcon.
Opaque emp.
Opaque andp.
