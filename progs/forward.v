Load loadpath.
Require Import Coqlib compositional_compcert.Coqlib2.
Require Import veric.SeparationLogic.
Require veric.SequentialClight.
Import SequentialClight.SeqC.CSL.
Require Import progs.client_lemmas.
Require Import progs.field_mapsto.
Require Import progs.assert_lemmas.
Require Export progs.forward_lemmas progs.call_lemmas.

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
 See also BEGIN HORRIBLE1 in forward.v
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
 intro rho; unfold LOCALx, local.
change SEPx with SEPx'.
 simpl. 
  normalize.
 unfold coerce, lift1_C, lift0_C.
 apply sepcon_derives; auto.
 normalize.
 replace (subst ret (lift0 old) (get_result1 ret') rho)
   with (get_result1 ret rho); auto.
 destruct (eq_dec ret ret').
 subst.
 unfold get_result1.
 unfold subst. f_equal.
 normalize in H8.
 normalize. f_equal. auto.
 clear - H6 H8 H7.
 unfold tc_environ in H7.
 unfold env_set. destruct rho; simpl in *; f_equal.
 unfold eval_id in H8; simpl in H8. unfold subst in H8.
 simpl in *. rewrite Map.gss in H8. simpl in H8.
 unfold_coerce. subst.
 unfold Map.set. extensionality i. 
 destruct (ident_eq i ret'); auto.  subst i.
 unfold typecheck_environ in H7.
 repeat rewrite andb_true_iff in H7.
 destruct H7 as [[[? _] _] _].
 simpl te_of in H.
 apply environ_lemmas.typecheck_te_eqv in H.
 hnf in H.
 specialize (H ret').
 revert H6; case_eq ((temp_types Delta)!ret'); intros; try discriminate.
 destruct p.
 unfold temp_types, initialized in H; simpl in H.
 rewrite H0 in H. unfold temp_types in *. simpl in H. rewrite PTree.gss in H.
 simpl in H. rewrite PTree.gss in H.
 specialize (H true t (eq_refl _)). 
 destruct H as [v [? ?]]. rewrite H.
 apply H.
  rewrite closed_wrt_subst; auto with closed.
 unfold get_result1.
 f_equal. f_equal.
 rewrite H8.
  rewrite closed_wrt_subst; auto with closed.
Qed.

(* END HORRIBLE1 *)

Ltac normalizex :=
  normalize;
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
         ]; cbv beta; normalize).

Ltac forward_setx_aux1 :=
      apply forward_setx; 
      try solve [intro rho; rewrite andp_unfold; apply andp_right; apply prop_right;
                            repeat split ].

Ltac forward_setx_aux2 id :=
           match goal with 
           | Name: name id |- _ => 
                let x:= fresh Name in intro x; simpl eval_expr; autorewrite with subst; try clear x
           | |- _ => let x:= fresh in intro x; simpl eval_expr; autorewrite with subst; try clear x
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

Ltac semax_field_tac1 := 
   eapply semax_load_field'; 
     [ reflexivity 
     | reflexivity 
     | simpl; reflexivity 
     | type_of_field_tac ].

Ltac isolate_field_tac e fld R := 
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

Ltac hoist_later_in_pre :=
     match goal with |- semax _ ?P _ _ =>
       let P' := strip1_later P in apply semax_pre0 with (|> P'); [solve [auto 50 with derives] | ]
     end.

Ltac semax_field_tac :=
match goal with |- semax ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R)))
                    (Sset ?id (Efield (Ederef ?e _) ?fld _)) _ =>
     apply (semax_pre (PROPx P (LOCALx (tc_expr Delta e :: Q) (SEPx R))));
     [ apply semax_load_assist1; [reflexivity]
     | isolate_field_tac e fld R; hoist_later_in_pre;
       eapply semax_post'; [ | semax_field_tac1 ]
     ]
end.

Definition storable (sh: share) (t: type) (v: val) :=
 EX v':val, mapsto sh t v v'.

Lemma mapsto_storable: forall sh t v v',
   mapsto sh t v v' |-- storable sh t v.
Proof. unfold storable; intros. apply exp_right with v'; auto.
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
     | context [|> `(storable ?sh ?ty) ?e' :: ?R'] =>
          let n := length_of R in let n' := length_of R' 
             in rewrite (grab_nth_SEP (n- S n')); simpl minus; unfold nth, delete_nth;
                replace e' with (eval_expr e) by auto
     | context [`(storable ?sh ?ty) ?e' :: ?R'] =>
          let n := length_of R in let n' := length_of R' 
             in rewrite (grab_nth_SEP (n- S n')); simpl minus; unfold nth, delete_nth;
                replace e' with (eval_expr e) by auto
     end.

Ltac isolate_storable_tac e fld R := 
  match R with 
     | context [|> `(field_mapsto ?sh ?struct fld) ?e' _ :: ?R'] =>
          let n := length_of R in let n' := length_of R' 
             in rewrite (grab_nth_SEP (n- S n')); simpl minus; unfold nth, delete_nth;
                change e' with (eval_expr e);
                apply later_field_mapsto_storable_at1
     | context [ `(field_mapsto ?sh ?struct fld) ?e' _  :: ?R'] =>
          let n := length_of R in let n' := length_of R' 
             in rewrite (grab_nth_SEP (n- S n')); simpl minus; unfold nth, delete_nth;
                change e' with (eval_expr e);
                apply field_mapsto_storable_at1
     | context [|> `(field_storable ?sh ?struct fld) ?e' :: ?R'] =>
          let n := length_of R in let n' := length_of R' 
             in rewrite (grab_nth_SEP (n- S n')); simpl minus; unfold nth, delete_nth;
                change e' with (eval_expr e)
     | context [ `(field_storable ?sh ?struct fld) ?e'  :: ?R'] =>
          let n := length_of R in let n' := length_of R' 
             in rewrite (grab_nth_SEP (n- S n')); simpl minus; unfold nth, delete_nth; 
                change e' with (eval_expr e)
     end.

Ltac store_field_tac1 := 
  eapply semax_store_field'; [ auto | reflexivity | reflexivity | type_of_field_tac |
               try solve [hnf; intuition] ].


Lemma semax_store_PQR':
forall (Delta: tycontext) sh t1 P Q R e1 e2
    (WS: writable_share sh)
    (NONVOL: type_is_volatile t1 = false)
    (TC: typecheck_store (Ederef e1 t1)),
    typeof e1 = Tpointer t1 noattr ->
    semax Delta 
       (|> PROPx P (LOCALx (tc_expr Delta e1::tc_expr Delta (Ecast e2 t1)::Q)
                             (SEPx (`(storable sh t1) (eval_expr e1)::R))))
       (Sassign (Ederef e1 t1) e2) 
       (normal_ret_assert
          (PROPx P (LOCALx Q
              (SEPx  (`(mapsto sh t1) (eval_expr e1) 
                  (`(eval_cast (typeof e2) t1) (eval_expr e2)) :: R))))).
Proof.
intros.
apply semax_pre0 with
   (EX v2:val, |> PROPx P (LOCALx (tc_expr Delta e1::tc_expr Delta (Ecast e2 t1)::Q)
                             (SEPx (`(mapsto sh t1) (eval_expr e1) `v2::R)))).
change SEPx with SEPx'.
unfold PROPx, LOCALx, SEPx', local; intro rho; simpl.
rewrite <- later_exp' by apply Vundef.
apply later_derives. unfold storable. unfold_coerce.
normalize. apply exp_right with v'. normalize.
apply extract_exists_pre; intro v2.
apply semax_store_PQR; auto.
Qed.

Ltac store_field_tac :=
  match goal with
  | |- semax ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) 
                     (Sassign (Efield (Ederef ?e _) ?fld ?t2) ?e2) _ =>
       apply (semax_pre_PQR (PROPx P 
                (LOCALx (tc_expr Delta e :: tc_expr Delta (Ecast e2 t2) ::Q) 
                (SEPx R))));
   [ try solve [go_lower2; apply andp_right;
                    [apply prop_right; intuition | apply derives_refl]]
   | isolate_storable_tac e fld R; hoist_later_in_pre;
       eapply semax_post''; [ | store_field_tac1]
   ]
  end.

Ltac store_tac :=
 match goal with
  | |- semax ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) 
                     (Sassign (Ederef ?e ?t2) ?e2) _ =>
       apply (semax_pre_PQR (PROPx P 
                (LOCALx (tc_expr Delta e :: tc_expr Delta (Ecast e2 t2) ::Q) 
                (SEPx R))));
   [ try solve [go_lower2; apply andp_right;
                    [apply prop_right; intuition | apply derives_refl]]
   |  isolate_mapsto_tac e R; hoist_later_in_pre;
       eapply semax_post'';  
       [ | first [eapply semax_store_PQR; 
                     [ auto | reflexivity | hnf; intuition | reflexivity ]
                   | eapply semax_store_PQR'; 
                     [ auto | reflexivity | hnf; intuition | reflexivity ]
                   ]              
       ]
   ]
  end.


Ltac intro_old_var' id :=
  match goal with 
  | Name: name id |- _ => 
        let x := fresh Name in
        intro x; simpl eval_expr; autorewrite with subst; try clear x
  | |- _ => let x := fresh "x" in 
        intro x; simpl eval_expr; autorewrite with subst; try clear x  
  end.

Ltac intro_old_var c :=
  match c with 
  | Sset ?id _ => intro_old_var' id
  | Scall (Some ?id) _ _ => intro_old_var' id
  | _ => intro x; simpl eval_expr; autorewrite with subst; try clear x
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
         evar (fsig: funsig); evar (A: Type); evar (Pre: A -> assert); evar (Post: A -> assert);
      assert (VT: (var_types Delta) ! f = None) by reflexivity;
      assert (GT: (glob_types Delta) ! f = Some (Global_func (mk_funspec fsig A Pre Post)))
                    by (unfold fsig, A, Pre, Post; simpl; reflexivity);
 let SCI := fresh "SCI" in
    let H := fresh in let witness := fresh "witness" in let F := fresh "Frame" in
      evar (witness:A); evar (F: list assert); 
      assert (SCI := semax_call_id1 Delta P Q F id f 
                 (snd fsig) bl (fst fsig) A witness Pre Post 
                      (eq_refl _) (eq_refl _) I);
      assert (H: PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
                      PROPx P (LOCALx (tc_exprlist Delta (snd (split (fst fsig))) bl:: Q)
                                      (SEPx (`(Pre witness) (make_args' fsig (eval_exprlist (snd (split (fst fsig))) bl)) :: F))));
     [ unfold fsig, A, Pre, Post
     |  apply semax_pre with (PROPx P
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
         evar (fsig: funsig); evar (A: Type); evar (Pre: A -> assert); evar (Post: A -> assert);
      assert (VT: (var_types Delta) ! f = None) by reflexivity;
      assert (GT: (glob_types Delta) ! f = Some (Global_func (mk_funspec fsig A Pre Post)))
                    by (unfold fsig, A, Pre, Post; simpl; reflexivity);
 let SCI := fresh "SCI" in
    let H := fresh in let witness := fresh "witness" in let F := fresh "Frame" in
      evar (witness:A); evar (F: list assert); 
      assert (SCI := semax_call_id0 Delta P Q F f 
                  bl (fst fsig) A witness Pre Post 
                      (eq_refl _)  (eq_refl _) );
      assert (H: PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
                      PROPx P (LOCALx (tc_exprlist Delta (snd (split (fst fsig))) bl:: Q)
                                      (SEPx (`(Pre witness) (make_args' fsig (eval_exprlist (snd (split (fst fsig))) bl)) :: F))));
     [ unfold fsig, A, Pre, Post
     |  apply semax_pre with (PROPx P
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
         evar (fsig: funsig); evar (A: Type); evar (Pre: A -> assert); evar (Post: A -> assert);

      assert (VT: (var_types Delta) ! f = None) by reflexivity;
      assert (GT: (glob_types Delta) ! f = Some (Global_func (mk_funspec fsig A Pre Post)))
                    by (unfold fsig, A, Pre, Post; simpl; reflexivity);

 let SCI := fresh "SCI" in
    let H := fresh in let x := fresh "witness" in let F := fresh "Frame" in
      evar (x:A); evar (F: list assert); 

      assert (SCI := semax_call_id1_x Delta P Q F id id' f 
                   (snd fsig) bl (fst fsig) A x Pre Post 
                      (eq_refl _) (eq_refl _) I);
      assert (H: PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
                      PROPx P (LOCALx (tc_exprlist Delta (snd (split (fst fsig))) bl:: Q)
                                      (SEPx (`(Pre x) (make_args' fsig (eval_exprlist (snd (split (fst fsig))) bl)) :: F))));
     [ unfold fsig, A, Pre, Post
     |  apply semax_pre with (PROPx P
                (LOCALx (tc_exprlist Delta (snd (split (fst fsig))) bl :: Q)
                 (SEPx (`(Pre x)  (make_args' fsig (eval_exprlist (snd (split (fst fsig))) bl)) ::
                            F))));
       [apply (semax_call_id_aux1 _ _ _ _ _ H)
       | eapply semax_post'; [ unfold  x,F | unfold F in *; 
              ( apply SCI ; [ solve[simpl; auto with closed] 
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
  | |- semax _ _ (Sset ?id ?e) _ => forward_setx
  | |- semax ?Delta (PROPx ?P (LOCALx ?Q ?R)) 
                                 (Sifthenelse ?e _ _) _ =>
            apply semax_pre_PQR
                     with (PROPx P (LOCALx (tc_expr Delta e :: Q) R));
             [ | apply semax_ifthenelse_PQR; [ reflexivity | | ]]
  | |- semax _ _ (Sreturn _) _ => 
                    eapply semax_pre; [ go_lower1 | apply semax_return ]
(* see comment HACK below, in forward tactic...
  | |- semax ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) (Scall (Some ?id) (Evar ?f _) ?bl)  _ =>
                   semax_call_id_tac_aux Delta P Q R id f bl
*)
  end.

(*
Ltac forward0 :=  (* USE FOR DEBUGGING *)
  match goal with 
  | |- semax _ ?PQR (Ssequence ?c1 ?c2) ?PQR' => 
           let Post := fresh "Post" in
              evar (Post : assert);
              apply semax_seq' with Post;
               [ 
               | unfold exit_tycon, update_tycon, Post; clear Post ]
  end.
*)

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
                 simpl update_tycon; simpl map;
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
                 simpl update_tycon; simpl map;
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
              evar (Post : assert);
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

Ltac start_function :=
match goal with |- semax_body _ _ _ ?spec => try unfold spec end;
match goal with |- semax_body _ _ _ (pair _ (mk_funspec _ _ ?Pre _)) =>
  match Pre with 
  | (fun x => match x with (a,b) => _ end) => intros [a b] 
  | (fun i => _) => intro i
  end;
  simpl fn_body; simpl fn_params; simpl fn_return;
  canonicalize_pre
 end;
 match goal with |- semax (func_tycontext ?F ?V ?G) _ _ _ => 
   set (Delta := func_tycontext F V G)
 end;
  try match goal with |- context [stackframe_of ?F] =>
            change (stackframe_of F) with emp;
            rewrite frame_ret_assert_emp
         end;
  repeat (apply semax_extract_PROP; intro).

Opaque sepcon.
Opaque emp.
Opaque andp.
