Require Import floyd.base.
Require Import floyd.client_lemmas.
Require Import floyd.assert_lemmas.
Require Import floyd.closed_lemmas.
Require Import floyd.canonicalize floyd.forward_lemmas floyd.call_lemmas.
Require Import floyd.extcall_lemmas.
Require Import floyd.nested_field_lemmas.
Require Import floyd.efield_lemmas.
Require Import floyd.nested_field_re_lemmas.
Require Import floyd.mapsto_memory_block.
Require Import floyd.data_at_lemmas.
Require Import floyd.field_at.
Require Import floyd.array_lemmas.
Require Import floyd.loadstore_mapsto.
Require Import floyd.loadstore_data_at.
Require Import floyd.loadstore_field_at.
Require Import floyd.nested_loadstore.
Require Import floyd.sc_set_load_store.
Require Import floyd.local2ptree.
Require Import floyd.unfold_data_at.
Require Import floyd.entailer.
Require Import floyd.globals_lemmas.
Require Import floyd.type_id_env.
Require Import floyd.semax_tactics.
Require Import floyd.for_lemmas.
Require Import floyd.diagnosis.
Import Cop.

Local Open Scope logic.

Definition tc_option_val' (t: type) : option val -> Prop :=
 match t with Tvoid => fun v => match v with None => True | _ => False end | _ => fun v => tc_val t (force_val v) end.
Lemma tc_option_val'_eq: tc_option_val = tc_option_val'.
Proof. extensionality t v. destruct t as [ | | | [ | ] |  | | | | | ] eqn:?,v eqn:?; simpl; try reflexivity.
Qed.
Hint Rewrite tc_option_val'_eq : norm.

Lemma emp_make_ext_rval:
  forall ge v, @emp (environ->mpred) _ _ (make_ext_rval ge v) = emp.
Proof. reflexivity. Qed.
Hint Rewrite emp_make_ext_rval : norm.

Ltac semax_func_cons_ext_tc :=
  repeat match goal with
  | |- (forall x: (?A * ?B), _) => 
      intros [? ?];  match goal with a1:_ , a2:_ |- _ => revert a1 a2 end
  | |- forall x, _ => intro  
  end; 
  normalize; simpl tc_option_val' .

Ltac semax_func_skipn :=
  repeat first [apply semax_func_nil'
                     | apply semax_func_skip1;
                       [clear; solve [auto with closed] | ]].

Ltac semax_func_cons L :=
 first [apply semax_func_cons; 
           [ reflexivity 
           | repeat apply Forall_cons; try apply Forall_nil; computable
           | reflexivity | precondition_closed | apply L | 
           ]
        | eapply semax_func_cons_ext;
             [reflexivity | reflexivity | reflexivity | reflexivity 
             | semax_func_cons_ext_tc | apply L |
             ]
        ].

Ltac semax_func_cons_ext :=
  eapply semax_func_cons_ext;
    [reflexivity | reflexivity | reflexivity | reflexivity 
    | semax_func_cons_ext_tc 
    | solve[ eapply semax_ext; 
          [ repeat first [reflexivity | left; reflexivity | right]
          | apply compute_funspecs_norepeat_e; reflexivity 
          | reflexivity 
          | reflexivity ]] 
      || fail "Try 'eapply semax_func_cons_ext.'" 
              "To solve [semax_external] judgments, do 'eapply semax_ext.'"
              "Make sure that the Espec declared using 'Existing Instance' 
               is defined as 'add_funspecs NullExtension.Espec Gprog.'"
    | 
    ].

Ltac forward_seq := 
  first [eapply semax_seq'; [  | abbreviate_semax ]
         | eapply semax_post_flipped' ].

Ltac simpl_stackframe_of := 
  unfold stackframe_of, fn_vars; simpl map; unfold fold_right; rewrite sepcon_emp;
  repeat rewrite var_block_data_at_ by reflexivity;
  repeat rewrite prop_true_andp by (simpl sizeof; computable).

(* end of "stuff to move elsewhere" *)

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
 forall Espec Delta P Q R ret ret' id retty retty' bl argsig A x Pre Post
   (GLBL: (var_types Delta) ! id = None),
   (glob_specs Delta) ! id = Some (mk_funspec (argsig,retty') A Pre Post) ->
   (glob_types Delta) ! id = Some (type_of_funspec (mk_funspec (argsig,retty') A Pre Post)) ->
   match retty' with Tvoid => False | Tcomp_ptr _ _ => False | Tarray _ _ _ => False | _ => True end ->
  forall
   (CLOSQ: Forall (closed_wrt_vars (eq ret')) Q)
   (CLOSR: Forall (closed_wrt_vars (eq ret')) R),
   (temp_types Delta) ! ret' = Some (retty', false) ->
   is_neutral_cast retty' retty = true ->
   match (temp_types Delta) ! ret with Some (t,_) => eqb_type t retty | None => false end = true ->
  @semax Espec Delta (PROPx P (LOCALx (tc_exprlist Delta (argtypes argsig) bl :: Q) 
                                     (SEPx (`(Pre x) (make_args' (argsig,retty') (eval_exprlist (argtypes argsig) bl)) :: R))))
    (Ssequence (Scall (Some ret')
             (Evar id (Tfunction (type_of_params argsig) retty' cc_default))
             bl)
      (Sset ret (Etempvar ret' retty')))
    (normal_ret_assert 
       (EX old:val, 
          PROPx P (LOCALx (map (subst ret (`old)) Q) 
             (SEPx (`(Post x) (get_result1 ret) :: map (subst ret (`old)) R))))).
Proof.
 intros until 1. intro Hspecs.
 pose (H1:=True); pose (H2:=True).
 intros ? ? ?. pose proof I. intros.  clear H3. (* rename H3 into NONVOL. *)
 eapply semax_seq';
 [assert (H0':    match retty' with Tvoid => False | _ => True end)
  by (clear - H0; destruct retty'; try contradiction; auto);
   apply (semax_call_id1' _ _ P Q R _ _ _ bl _ _ x _ _ GLBL Hspecs H H0'); auto
 | ].
simpl. rewrite H4; auto.
match goal with |- semax ?D (PROPx ?P ?QR) ?c ?Post =>
   assert ( (fold_right and True P) -> semax D (PROPx nil QR) c Post)
 end.
Focus 2. {
 clear - H3.
 unfold PROPx. 
 unfold PROPx at 1 in H3.
 normalize in H3.
 apply semax_extract_prop. apply H3.
} Unfocus.
 intro.
 apply semax_post_flipped
 with (normal_ret_assert (EX  x0 : val,
PROP  ()
(LOCALx
   (tc_environ
      (initialized ret
         (update_tycon Delta
            (Scall (Some ret') (Evar id (Tfunction (type_of_params argsig) retty' cc_default)) bl)))
    :: `eq (eval_id ret)
         (subst ret (`x0) (eval_expr (Etempvar ret' retty')))
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
 replace ( (temp_types (initialized ret' Delta)) ! ret' ) 
     with (Some (retty', true))
   by (unfold initialized;  simpl; rewrite H4;
        unfold temp_types; simpl; rewrite PTree.gss; auto).
 simpl @snd; simpl @fst; cbv iota zeta beta.
 unfold local; apply prop_right.
 simpl.
 clear - H5.
  destruct retty as [ | [ | | | ] [ | ] | | [ | ] |  | | | | | ], retty' as [ |  [ | | | ] [ | ] | | [ | ] |  | | | | | ];
     simpl; try inv H5; try apply I.
 intro rho; apply prop_right; unfold tc_temp_id; simpl.
 unfold typecheck_temp_id.
 destruct (eq_dec ret' ret).
 subst ret'.
 unfold temp_types. unfold initialized; simpl.
 rewrite H4. simpl. rewrite PTree.gss.
  replace (implicit_deref retty') with retty' by (clear - H0; destruct retty'; try contradiction; reflexivity).
 rewrite H4 in H6. apply eqb_type_true in H6. subst retty'.
 rewrite H5.
 simpl.
 apply neutral_isCastResultType; auto.
 replace (implicit_deref retty') with retty' by (clear - H0; destruct retty'; try contradiction; reflexivity).
 destruct ((temp_types Delta) ! ret) eqn:?; try discriminate.
 destruct p. apply eqb_type_true in H6.
 subst t.
 unfold temp_types, initialized.  rewrite H4. simpl. rewrite PTree.gso by auto.
 rewrite Heqo.
 rewrite denote_tc_assert_andp; split.
 rewrite H5; reflexivity.
 apply neutral_isCastResultType; auto.
 apply derives_refl.
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

Lemma local_True_right:
 forall (P: environ -> mpred),
   P |-- local (`True).
Proof. intros. intro rho; apply TT_right.
Qed.

Lemma normalize_lvar:
  forall v i t rho,  isptr (eval_lvar i t rho) ->
        v  = (eval_lvar i t rho) -> lvar i t v rho.
Proof.
unfold_lift.
unfold lvar, eval_lvar.
intros.
destruct (Map.get (ve_of rho) i) as [[? ?] | ].
destruct (eqb_type t t0); inv H; auto.
inv H.
Qed.

Lemma lvar_isptr:
  forall i t v rho, lvar i t v rho -> isptr v.
Proof.
unfold lvar; intros.
destruct (Map.get (ve_of rho) i) as [[? ?]|]; try contradiction.
destruct (eqb_type t t0); try contradiction; subst; apply I.
Qed.

Lemma gvar_isptr:
  forall i v rho, gvar i v rho -> isptr v.
Proof.
unfold gvar; intros.
destruct (Map.get (ve_of rho) i) as [[? ?]|]; try contradiction.
destruct (ge_of rho i); try contradiction.
subst; apply I.
Qed.

Lemma sgvar_isptr:
  forall i v rho, sgvar i v rho -> isptr v.
Proof.
unfold sgvar; intros.
destruct (ge_of rho i); try contradiction.
subst; apply I.
Qed.

Lemma lvar_eval_lvar:
  forall i t v rho, lvar i t v rho -> eval_lvar i t rho = v.
Proof.
unfold lvar, eval_lvar; intros.
destruct (Map.get (ve_of rho) i) as [[? ?]|]; try contradiction.
destruct (eqb_type t t0); try contradiction; subst; auto.
Qed.

Lemma lvar_eval_lvar':
  forall i t rho, 
   isptr (eval_lvar i t rho) ->
   lvar i t (eval_lvar i t rho) rho.
Proof.
 intros.
  unfold lvar, eval_lvar in *.
  destruct (Map.get (ve_of rho) i) as [[? ?]|]; try contradiction; auto.
  destruct (eqb_type t t0); try contradiction; auto.
Qed.

Lemma lvar_eval_var:
 forall i t v rho, lvar i t v rho -> eval_var i t rho = v.
Proof.
intros.
unfold eval_var. hnf in H. destruct (Map.get (ve_of rho) i) as [[? ?]|]; try inv H.
destruct (eqb_type t t0); try inv H. auto.
Qed.

Lemma lvar_isptr_eval_var:
 forall i t v rho, lvar i t v rho -> isptr (eval_var i t rho).
Proof.
intros.
erewrite lvar_eval_var; eauto.
eapply lvar_isptr; eauto.
Qed.

Hint Extern 1 (isptr (eval_var _ _ _)) => (eapply lvar_isptr_eval_var; eassumption).

Ltac fixup_local_var  :=  (* this tactic is needed only until start_function
                                           handles lvars in a better way *)
 match goal with |- semax _ ?Pre0 _ _ => match Pre0 with 
    context [@liftx (Tarrow val (LiftEnviron mpred)) ?F (eval_lvar ?i ?t)] =>
     let v := fresh "v" in 
    apply (remember_value (eval_lvar i t)); intro v;
    assert_LOCAL (lvar i t v);
      [entailer!; apply lvar_eval_lvar'; auto | ];
    drop_LOCAL 1%nat;
    match goal with |- semax _ ?Pre _ _ =>
    match Pre with context C [@liftx (Tarrow val (LiftEnviron mpred)) F (eval_lvar i t)] =>
     let D := context C[ (@liftx (LiftEnviron mpred) (F v))  ]   in
        apply semax_pre with D; [ entailer!; rewrite (lvar_eval_lvar i t v) by auto; auto | ] 
    end end;
    revert v
 end end.

Lemma force_val_sem_cast_neutral_isptr:
  forall v,
  isptr v ->
  Some (force_val (sem_cast_neutral v)) = Some v.
Proof.
intros.
 destruct v; try contradiction; reflexivity.
Qed.

Lemma force_val_sem_cast_neutral_lvar:
  forall i t v rho,
  lvar i t v rho ->
  Some (force_val (sem_cast_neutral v)) = Some v.
Proof.
intros.
 apply lvar_isptr in H; destruct v; try contradiction; reflexivity.
Qed.

Lemma force_val_sem_cast_neutral_gvar:
  forall i v rho,
  gvar i v rho ->
  Some (force_val (sem_cast_neutral v)) = Some v.
Proof.
intros.
 apply gvar_isptr in H; destruct v; try contradiction; reflexivity.
Qed.

Lemma force_val_sem_cast_neutral_sgvar:
  forall i v rho,
  sgvar i v rho ->
  Some (force_val (sem_cast_neutral v)) = Some v.
Proof.
intros.
 apply sgvar_isptr in H; destruct v; try contradiction; reflexivity.
Qed.

Lemma prop_Forall_cons:
 forall {B}{A} {NB: NatDed B} (P: B) F (a:A) b,
  P |-- !! F a && !! Forall F b ->
  P |-- !! Forall F (a::b).
Proof.
intros. eapply derives_trans; [apply H |].
normalize.
Qed.

Lemma prop_Forall_cons':
 forall {B}{A} {NB: NatDed B} (P: B) P1 F (a:A) b,
  P |-- !! (P1 /\ F a) && !! Forall F b ->
  P |-- !! P1 && !! Forall F (a::b).
Proof.
intros. eapply derives_trans; [apply H |].
normalize. destruct H0; normalize.
Qed.

Lemma prop_Forall_nil:
 forall {B}{A} {NB: NatDed B} (P: B)  (F: A -> Prop),
  P |-- !! Forall F nil.
Proof.
intros. apply prop_right; constructor.
Qed.

Lemma prop_Forall_nil':
 forall {B}{A} {NB: NatDed B} (P: B)  P1 (F: A -> Prop),
  P |-- !! P1->
  P |-- !! P1 && !! Forall F nil.
Proof.
intros. eapply derives_trans; [apply H |].
normalize.
Qed.

Lemma prop_Forall_cons1:
 forall {B}{A} {NB: NatDed B} (P: B) (F: A -> Prop) (a:A) b,
  F a ->
  P |-- !! Forall F b ->
  P |-- !! Forall F (a::b).
Proof.
intros. eapply derives_trans; [apply H0 |].
normalize.
Qed.

Ltac Forall_pTree_from_elements :=
 cbv beta;
 go_lower; ent_iter;
 repeat first
   [ apply prop_Forall_cons1;
     [unfold check_one_temp_spec, check_one_var_spec; 
     simpl; auto;
     solve [eapply force_val_sem_cast_neutral_lvar; eassumption
              | eapply force_val_sem_cast_neutral_gvar; eassumption
              | eapply force_val_sem_cast_neutral_sgvar; eassumption
              | apply force_val_sem_cast_neutral_isptr; auto
              ]
     | ]
   | apply prop_Forall_cons'
   | apply prop_Forall_cons
   | apply prop_Forall_nil'
   | apply prop_Forall_nil
   ];
 unfold check_one_temp_spec;
 simpl PTree.get; 
 change (@snd ident val) with (fun p: ident*val => let (_,y) := p in y);
  cbv beta iota; simpl force_val;
 entailer.

Ltac Forall_check_spec :=
 apply prop_right; repeat constructor; hnf; simpl;
       first [eapply force_val_sem_cast_neutral_lvar; eassumption
             | apply force_val_sem_cast_neutral_isptr; auto
             | idtac
             ].

Ltac try_solve_Forall_pTree_from_elements :=
  match goal with |- _ |-- !! Forall ?A _ =>
   let ptf := fresh "ptf" in set (ptf := A);
 unfold pTree_from_elements in ptf; 
   simpl in ptf; cbv beta iota in ptf; subst ptf;
 try solve [Forall_check_spec];
 entailer;
 try solve [Forall_check_spec]
 end.

Lemma exp_uncurry2:
  forall {T} {ND: NatDed T} A B C F,
    @exp T ND A (fun a => @exp T ND B (fun b => @exp T ND C
           (fun c => F a b c)))
   = @exp T ND (A*B*C) (fun x => F (fst (fst x)) (snd (fst x)) (snd x)).
Proof.
intros.
repeat rewrite exp_uncurry; auto.
Qed.

Lemma exp_uncurry3:
  forall {T} {ND: NatDed T} A B C D F,
    @exp T ND A (fun a => @exp T ND B (fun b => @exp T ND C
           (fun c => @exp T ND D (fun d => F a b c d))))
   = @exp T ND (A*B*C*D) 
        (fun x => F (fst (fst (fst x))) (snd (fst (fst x))) (snd (fst x)) (snd x)).
Proof.
intros.
repeat rewrite exp_uncurry; auto.
Qed.

Ltac  unify_postcondition_exps :=
first [ reflexivity
  | rewrite exp_uncurry;
     apply exp_congr; intros [? ?]; simpl; reflexivity
  | rewrite exp_uncurry2; 
     apply exp_congr; intros [[? ?] ?]; simpl; reflexivity
  | rewrite exp_uncurry3; 
     apply exp_congr; intros [[[? ?] ?] ?]; simpl; reflexivity
  ].

Ltac forward_call_id1_x_wow witness :=
let Frame := fresh "Frame" in
 evar (Frame: list (mpred));
 eapply (semax_call_id1_x_wow witness Frame);
 [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
 | apply I | apply I | reflexivity 
 | (clear; let H := fresh in intro H; inversion H)
 | reflexivity
 | prove_local2ptree | repeat constructor 
 | entailer!
 | reflexivity
 | prove_local2ptree | repeat constructor 
 | reflexivity | reflexivity
 | Forall_pTree_from_elements
 | Forall_pTree_from_elements
 | unfold fold_right at 1 2; cancel
 | cbv beta; extensionality rho; 
   repeat rewrite exp_uncurry;
   try rewrite no_post_exists; repeat rewrite exp_unfold;
   apply exp_congr; intros ?vret; reflexivity
 | intros; try match goal with  |- extract_trivial_liftx ?A _ =>
        (has_evar A; fail 1) || (repeat constructor)
     end
 | repeat constructor; auto with closed
 | repeat constructor; auto with closed
 | unify_postcondition_exps
 | unfold fold_right_and; repeat rewrite and_True; auto
 ].

Ltac forward_call_id1_y_wow witness :=
let Frame := fresh "Frame" in
 evar (Frame: list (mpred));
 eapply (semax_call_id1_y_wow witness Frame);
 [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
 | apply I | apply I | reflexivity 
 | (clear; let H := fresh in intro H; inversion H)
 | reflexivity
 | prove_local2ptree | repeat constructor 
 | entailer!
 | reflexivity
 | prove_local2ptree | repeat constructor 
 | reflexivity | reflexivity
 | Forall_pTree_from_elements
 | Forall_pTree_from_elements
 | unfold fold_right at 1 2; cancel
 | cbv beta; extensionality rho; 
   repeat rewrite exp_uncurry;
   try rewrite no_post_exists; repeat rewrite exp_unfold;
   apply exp_congr; intros ?vret; reflexivity
 | intros; try match goal with  |- extract_trivial_liftx ?A _ =>
        (has_evar A; fail 1) || (repeat constructor)
     end
 | repeat constructor; auto with closed
 | repeat constructor; auto with closed
 | unify_postcondition_exps
 | unfold fold_right_and; repeat rewrite and_True; auto
 ].

Ltac forward_call_id1_wow witness :=
let Frame := fresh "Frame" in
 evar (Frame: list (mpred));
 eapply (semax_call_id1_wow witness Frame);
 [ reflexivity | reflexivity | reflexivity | reflexivity
 | apply I | reflexivity
 | prove_local2ptree
 | repeat constructor 
 | try apply local_True_right; entailer!
 | reflexivity
 | prove_local2ptree | repeat constructor 
 | reflexivity | reflexivity
 | Forall_pTree_from_elements
 | Forall_pTree_from_elements
 | unfold fold_right at 1 2; cancel
 | cbv beta; extensionality rho; 
   repeat rewrite exp_uncurry;
   try rewrite no_post_exists; repeat rewrite exp_unfold;
   apply exp_congr; intros ?vret; reflexivity
 | intros; try match goal with  |- extract_trivial_liftx ?A _ =>
        (has_evar A; fail 1) || (repeat constructor)
     end
 | repeat constructor; auto with closed
 | unify_postcondition_exps
 | unfold fold_right_and; repeat rewrite and_True; auto
 ].

Ltac forward_call_id01_wow witness :=
let Frame := fresh "Frame" in
 evar (Frame: list (mpred));
 eapply (semax_call_id01_wow witness Frame);
 [ reflexivity | reflexivity | reflexivity | apply I | reflexivity
 | prove_local2ptree | repeat constructor 
 | try apply local_True_right; entailer!
 | reflexivity
 | prove_local2ptree | repeat constructor 
 | reflexivity | reflexivity
 | Forall_pTree_from_elements
 | Forall_pTree_from_elements
 | unfold fold_right at 1 2; cancel
 | cbv beta; extensionality rho; 
   repeat rewrite exp_uncurry;
   try rewrite no_post_exists; repeat rewrite exp_unfold;
   apply exp_congr; intros ?vret; reflexivity
 | intros; try match goal with  |- extract_trivial_liftx ?A _ =>
        (has_evar A; fail 1) || (repeat constructor)
     end
 | unify_postcondition_exps
 | unfold fold_right_and; repeat rewrite and_True; auto
 ].

Ltac forward_call_id00_wow witness :=
let Frame := fresh "Frame" in
 evar (Frame: list (mpred));
 eapply (semax_call_id00_wow witness Frame);
 [ reflexivity | reflexivity | reflexivity | reflexivity
 | prove_local2ptree | repeat constructor 
 | try apply local_True_right; entailer!
 | reflexivity
 | prove_local2ptree | repeat constructor 
 | reflexivity | reflexivity
 | Forall_pTree_from_elements
 | Forall_pTree_from_elements
 | unfold fold_right at 1 2; cancel
 | cbv beta iota; 
    repeat rewrite exp_uncurry;
    try rewrite no_post_exists0; 
    first [reflexivity | extensionality; simpl; reflexivity]
 | intros; try match goal with  |- extract_trivial_liftx ?A _ =>
        (has_evar A; fail 1) || (repeat constructor)
     end
 | unify_postcondition_exps
 | unfold fold_right_and; repeat rewrite and_True; auto
 ].

Ltac simpl_strong_cast :=
try match goal with |- context [strong_cast ?t1 ?t2 ?v] =>
  first [change (strong_cast t1 t2 v) with v
         | change (strong_cast t1 t2 v) with
                (force_val (sem_cast t1 t2 v))
          ]
end.

Ltac unfold_map_liftx_etc := 
change (@map (lift_T (LiftEnviron mpred)) (LiftEnviron mpred)
                 (@liftx (LiftEnviron mpred)))
 with (fix map (l : list (lift_T (LiftEnviron mpred))) : list (LiftEnviron mpred) :=
  match l with
  | nil => nil 
  | cons a t => cons (liftx a) (map t)
  end); 
change (@app mpred)
  with (fix app (l m : list mpred) {struct l} : list mpred :=
  match l with
  | nil => m
  | cons a l1 => cons a (app l1 m)
  end);
change (@app Prop)
  with (fix app (l m : list Prop) {struct l} : list Prop :=
  match l with
  | nil => m
  | cons a l1 => cons a (app l1 m)
  end);
cbv beta iota.

Lemma revert_unit: forall (P: Prop), (forall u: unit, P) -> P.
Proof. intros. apply (H tt).
Qed.

Ltac after_forward_call2 :=
      cbv beta iota; 
      try rewrite <- no_post_exists0;
      unfold_map_liftx_etc;
      fold (@map (lift_T (LiftEnviron mpred)) (LiftEnviron mpred) liftx); 
      simpl_strong_cast;
      abbreviate_semax.

Ltac after_forward_call :=
  first [apply extract_exists_pre; 
             let v := fresh "v" in intro v; after_forward_call; revert v
          | after_forward_call2
          ].

Ltac fwd_skip :=
 match goal with |- semax _ _ Sskip _ =>
   normalize_postcondition;
   first [eapply semax_pre | eapply semax_pre_simple]; 
      [ | apply semax_skip]
 end.

Ltac fwd_call' witness :=
 try match goal with
      | |- semax _ _ (Scall _ _ _) _ => rewrite -> semax_seq_skip
      end;
 first [
     revert witness; 
     match goal with |- let _ := ?A in _ => intro; fwd_call' A 
     end
   | eapply semax_seq';
     [first [forward_call_id1_wow witness
           | forward_call_id1_x_wow witness
           | forward_call_id1_y_wow witness
           | forward_call_id01_wow witness ]
     | after_forward_call
     ]
  |  eapply semax_seq'; [forward_call_id00_wow witness 
          | after_forward_call ]
  | rewrite <- seq_assoc; fwd_call' witness
  ].

Definition In_the_previous_'forward'_use_an_intro_pattern_of_type (t: Type) := False.

Ltac no_intros :=
     match goal with
     | |- ?t -> _ => 
         elimtype False; fold (In_the_previous_'forward'_use_an_intro_pattern_of_type t)
     end.

(* 
Tactic Notation "forward_call'" constr(witness) :=
    check_canonical_call;
    fwd_call' witness;
   [ .. | 
    first [intros _ | no_intros];
    repeat (apply semax_extract_PROP; intro);
    try fwd_skip
   ].
*)

Definition In_the_previous_forward_call'__use_intropatterns_to_intro_values_of_these_types := Stuck.

Ltac complain_intros :=
 first [let x := fresh "x" in intro x; complain_intros; revert x
         | stuckwith In_the_previous_forward_call'__use_intropatterns_to_intro_values_of_these_types
         ].

Tactic Notation "uniform_intros" simple_intropattern_list(v) :=
 (((assert True by (intros v; apply I);
  assert (forall a: unit, True)
   by (intros v; apply I);
  fail 1) || intros v) || idtac).

Tactic Notation "forward_call'" constr(witness) simple_intropattern_list(v) :=
    check_canonical_call;
    check_Delta;
    fwd_call' witness;
  [ .. 
  | first 
      [ (* body of uniform_intros tactic *)
         (((assert True by (intros v; apply I);
            assert (forall a: unit, True) by (intros v; apply I);
            fail 1)
          || intros v) 
        || idtac);
        (* end body of uniform_intros tactic *)
        match goal with
        | |- semax _ _ _ _ => idtac 
        | |- unit -> semax _ _ _ _ => intros _ 
        end;
        repeat (apply semax_extract_PROP; intro);
       abbreviate_semax;
       try fwd_skip
     | complain_intros
     ]  
  ].

Lemma seq_assoc2:
  forall (Espec: OracleKind)  Delta P c1 c2 c3 c4 Q,
  semax Delta P (Ssequence (Ssequence c1 c2) (Ssequence c3 c4)) Q ->
  semax Delta P (Ssequence (Ssequence (Ssequence c1 c2) c3) c4) Q.
Proof.
intros.
 rewrite <- seq_assoc. auto.
Qed.

Lemma semax_call_id1_x_alt:
 forall Espec Delta P Q R ret ret' id (paramty: typelist) (retty retty': type) (bl: list expr)
                  (argsig: list (ident * type)) A (Pre Post: A -> environ -> mpred)
             (witness: A) (Frame: list (LiftEnviron mpred))
   (GLBL: (var_types Delta) ! id = None),
   (glob_specs Delta) ! id = Some (mk_funspec (argsig,retty') A Pre Post) ->
   (glob_types Delta) ! id = Some (type_of_funspec (mk_funspec (argsig,retty') A Pre Post)) ->
   typeof_temp Delta ret = Some retty -> 
   match retty with Tvoid => False | Tcomp_ptr _ _ => False | Tarray _ _ _ => False | _ => True end ->
   paramty = type_of_params argsig ->
   (temp_types Delta) ! ret' = Some (retty', false) ->
   is_neutral_cast retty' retty = true ->
   forall (CLOSQ: Forall (closed_wrt_vars (eq ret')) Q),
   PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
    PROP () LOCAL (tc_exprlist Delta (argtypes argsig) bl) 
                (SEPx (`(Pre witness)  (make_args' (argsig, retty)
                               (eval_exprlist (argtypes argsig) bl)) :: Frame)) ->
  forall
   (CLOSR: Forall (closed_wrt_vars (eq ret')) Frame),
   @semax Espec Delta (PROPx P (LOCALx Q (SEPx R)))
    (Ssequence (Scall (Some ret')
             (Evar id (Tfunction paramty retty' cc_default))
             bl)
      (Sset ret (Etempvar ret' retty')))
    (normal_ret_assert 
       (EX old:val, 
          PROPx P (LOCALx (map (subst ret (`old)) Q) 
             (SEPx (`(Post witness) (get_result1 ret) :: map (subst ret (`old)) Frame))))).
Proof.
 intros until 1. intro Hspec. intros ? ? ? ?.
 pose proof I. intros.
subst paramty.
eapply semax_pre; [ | apply semax_call_id1_x with retty; try eassumption].
rewrite <- (insert_local (tc_exprlist Delta (argtypes argsig) bl)).
apply andp_right.
eapply derives_trans; [apply H6 |].
apply andp_left2; apply andp_left1.
go_lowerx. intros [? _]; apply prop_right; auto.
apply andp_right.
apply andp_left1; auto.
apply andp_right.
rewrite <- insert_local.
apply andp_left2.
apply andp_left2.
 apply andp_left1. auto.
eapply derives_trans; [ apply H6 |].
apply andp_left2; apply andp_left2; auto.
clear - H5; destruct retty,retty'; inv H5; simpl; auto.
clear - H0. unfold typeof_temp in H0.
destruct((temp_types Delta) ! ret); inv H0.
destruct p; inv H1. apply eqb_type_refl.
Qed.

(* END HORRIBLE1 *)


Ltac do_compute_lvalue Delta P Q R e v H :=
  let rho := fresh "rho" in
  assert (PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
    local (`(eq v) (eval_lvalue e))) as H by
  (first [ assumption |
    eapply derives_trans; [| apply msubst_eval_lvalue_eq];
    [apply derives_refl'; apply local2ptree_soundness; try assumption;
     let HH := fresh "H" in
     construct_local2ptree (tc_environ Delta :: Q) HH;
     exact HH |
     unfold v;
     simpl;
     try unfold force_val2; try unfold force_val1;
     autorewrite with norm;
     simpl;
     reflexivity]
  ]).

Ltac do_compute_expr Delta P Q R e v H :=
  let rho := fresh "rho" in
  assert (PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
    local (`(eq v) (eval_expr e))) as H by
  (first [ assumption |
    eapply derives_trans; [| apply msubst_eval_expr_eq];
    [apply derives_refl'; apply local2ptree_soundness; try assumption;
     let HH := fresh "H" in
     construct_local2ptree (tc_environ Delta :: Q) HH;
     exact HH |
     unfold v;
     simpl;
     try unfold force_val2; try unfold force_val1;
     autorewrite with norm;
     simpl;
     reflexivity]
  ]).

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
try rewrite canonicalize.canon9.

Lemma quick_typecheck1: 
 forall (P B: environ -> mpred), 
    P |-- B ->
   P |-- local (`True) && B.
Proof.
intros; apply andp_right; auto.
 intro rho; apply TT_right.
Qed.

Lemma quick_typecheck2: 
 forall (P A: environ -> mpred), 
    P |-- A ->
   P |-- A && local (`True).
Proof.
intros; apply andp_right; auto.
 intro rho; apply TT_right.
Qed.

Ltac quick_typecheck :=
     first [ apply quick_typecheck1; try apply local_True_right
            | apply quick_typecheck2
            | apply local_True_right
            | idtac ].

Ltac do_compute_expr_helper Delta Q v :=
   try assumption;
   eapply derives_trans; [| apply msubst_eval_expr_eq];
    [apply derives_refl'; apply local2ptree_soundness; try assumption;
     let HH := fresh "H" in
     construct_local2ptree (tc_environ Delta :: Q) HH;
     exact HH |
     unfold v;
     simpl;
     try unfold force_val2; try unfold force_val1;
     autorewrite with norm;
     simpl;
     reflexivity].

Ltac do_compute_expr1 Delta Pre e :=
 match Pre with
 | @exp _ _ ?A ?Pre1 =>
  let P := fresh "P" in let Q := fresh "Q" in let R := fresh "R" in
  let H8 := fresh "DCE" in let H9 := fresh "DCE" in
  evar (P: A -> list Prop);
  evar (Q: A -> list (environ -> Prop));
  evar (R: A -> list (environ -> mpred));
  assert (H8: Pre1 =  (fun a => PROPx (P a) (LOCALx (Q a) (SEPx (R a)))))
    by (extensionality; unfold P,Q,R; reflexivity);
  let v := fresh "v" in evar (v: A -> val);
  assert (H9: forall a, PROPx (P a) (LOCALx (tc_environ Delta :: (Q a)) (SEPx (R a))) |--
                       local (`(eq (v a)) (eval_expr e)))
     by (let a := fresh "a" in intro a; do_compute_expr_helper Delta (Q a) v)
 | PROPx ?P (LOCALx ?Q (SEPx ?R)) =>
  let H9 := fresh "H" in
  let v := fresh "v" in evar (v: val);
  assert (H9:  PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R))|-- 
                     local (`(eq v) (eval_expr e)))
   by (do_compute_expr_helper Delta Q v) 
 end.

Lemma typed_true_nullptr3:
  forall p, 
  typed_true tint (force_val (sem_cmp_pp Ceq true2 p nullval)) ->
  p=nullval.
Proof.
intros.
hnf in H.
destruct p; inversion H.
destruct (Int.eq i Int.zero) eqn:?; inv H1.
apply int_eq_e in Heqb. subst; reflexivity.
Qed.

Lemma typed_false_nullptr3:
  forall p, 
  typed_false tint (force_val (sem_cmp_pp Ceq true2 p nullval)) ->
  p<>nullval.
Proof.
intros.
hnf in H.
destruct p; inversion H.
destruct (Int.eq i Int.zero) eqn:?; inv H1.
apply int_eq_false_e in Heqb. contradict Heqb. inv Heqb; auto.
unfold nullval; congruence.
Qed.

Lemma typed_true_nullptr4:
  forall p, 
  typed_true tint (force_val (sem_cmp_pp Cne true2 p nullval)) ->
  p <> nullval.
Proof.
intros.
hnf in H.
destruct p; inversion H.
destruct (Int.eq i Int.zero) eqn:?; inv H1.
apply int_eq_false_e in Heqb. unfold nullval; congruence.
intro Hx; inv Hx.
Qed.

Lemma typed_false_nullptr4:
  forall p, 
  typed_false tint (force_val (sem_cmp_pp Cne true2 p nullval)) ->
  p=nullval.
Proof.
intros.
hnf in H.
destruct p; inversion H.
destruct (Int.eq i Int.zero) eqn:?; inv H1.
apply int_eq_e in Heqb. subst; reflexivity.
Qed.


Lemma ltu_inv:
 forall x y, Int.ltu x y = true -> Int.unsigned x < Int.unsigned y.
Proof.
intros.
apply Int.ltu_inv in H; destruct H; auto.
Qed.

Lemma ltu_false_inv:
 forall x y, Int.ltu x y = false -> Int.unsigned x >= Int.unsigned y.
Proof.
intros.
unfold Int.ltu in H. if_tac in H; inv H; auto.
Qed.

Lemma lt_repr:
     forall i j : Z,
       repable_signed i ->
       repable_signed j ->
       Int.lt (Int.repr i) (Int.repr j) = true -> (i < j)%Z.
Proof.
intros.
unfold Int.lt in H1. if_tac in H1; inv H1.
normalize in H2.
Qed.

Lemma lt_repr_false:
     forall i j : Z,
       repable_signed i ->
       repable_signed j ->
       Int.lt (Int.repr i) (Int.repr j) = false -> (i >= j)%Z.
Proof.
intros.
unfold Int.lt in H1. if_tac in H1; inv H1.
normalize in H2.
Qed.

Lemma lt_inv:
 forall i j,
   Int.lt i j = true -> (Int.signed i < Int.signed j)%Z.
Proof.
intros.
unfold Int.lt in H. if_tac in H; inv H. auto.
Qed.

Lemma lt_false_inv:
 forall i j,
   Int.lt i j = false -> (Int.signed i >= Int.signed j)%Z.
Proof.
intros.
unfold Int.lt in H. if_tac in H; inv H. auto.
Qed.

Ltac cleanup_repr H :=
match type of H with
 | _ (Int.signed (Int.repr ?A)) (Int.signed (Int.repr ?B)) => 
    try (rewrite (Int.signed_repr A) in H by repable_signed);
    try (rewrite (Int.signed_repr B) in H by repable_signed)
 | _ (Int.unsigned (Int.repr ?A)) (Int.unsigned (Int.repr ?B)) => 
    try (rewrite (Int.unsigned_repr A) in H by repable_signed);
    try (rewrite (Int.unsigned_repr B) in H by repable_signed)
 | context [Int.signed (Int.repr ?A)] =>
    try (rewrite (Int.signed_repr A) in H by repable_signed)
 | context [Int.unsigned (Int.repr ?A)] =>
    try (rewrite (Int.unsigned_repr A) in H by repable_signed)
end.

Lemma typed_true_ptr_e:
 forall t v, typed_true (tptr t) v -> isptr v.
Proof.
 intros. destruct v; inv H; try apply I.
 destruct (Int.eq i Int.zero); inv H1.
Qed.

Lemma typed_false_ptr_e:
 forall t v, typed_false (tptr t) v -> v=nullval.
Proof.
 intros. destruct v; inv H; try apply I.
 destruct (Int.eq i Int.zero) eqn:?; inv H1.
apply int_eq_e in Heqb. subst; reflexivity.
Qed.

Ltac do_repr_inj H :=
   simpl typeof in H;
  try first [apply typed_true_of_bool in H
               |apply typed_false_of_bool in H
               | apply typed_true_ptr_e in H
               | apply typed_false_ptr_e in H
               ];
   repeat (rewrite -> negb_true_iff in H || rewrite -> negb_false_iff in H);
   try apply int_eq_e in H;
   match type of H with
          | _ <> _ => apply int_eq_false_e in H 
          | Int.eq _ _ = false => apply int_eq_false_e in H 
          | _ => idtac 
  end;
  first [ simple apply repr_inj_signed in H; [ | repable_signed | repable_signed ]
         | simple apply repr_inj_unsigned in H; [ | repable_signed | repable_signed ]
         | simple apply repr_inj_signed' in H; [ | repable_signed | repable_signed ]
         | simple apply repr_inj_unsigned' in H; [ | repable_signed | repable_signed ]
         | match type of H with
            | typed_true _  (force_val (sem_cmp_pp Ceq true2 _ _)) =>
                                    apply typed_true_nullptr3 in H
            | typed_true _  (force_val (sem_cmp_pp Cne true2 _ _)) =>
                                    apply typed_true_nullptr4 in H
            | typed_false _  (force_val (sem_cmp_pp Ceq true2 _ _)) =>
                                    apply typed_false_nullptr3 in H
            | typed_false _  (force_val (sem_cmp_pp Cne true2 _ _)) =>
                                    apply typed_false_nullptr4 in H
          end
         | apply typed_false_nullptr4 in H
         | simple apply ltu_repr in H; [ | repable_signed | repable_signed]
         | simple apply ltu_repr_false in H; [ | repable_signed | repable_signed]
         | simple apply ltu_inv in H; cleanup_repr H
         | simple apply ltu_false_inv in H; cleanup_repr H
         | simple apply lt_repr in H; [ | repable_signed | repable_signed]
         | simple apply lt_repr_false in H; [ | repable_signed | repable_signed]
         | simple apply lt_inv in H; cleanup_repr H
         | simple apply lt_false_inv in H; cleanup_repr H
         | idtac
         ].

Ltac simpl_fst_snd := 
repeat match goal with 
| |- context [fst (?a,?b)] => change (fst (a,b)) with a 
| |- context [snd (?a,?b)] => change (snd (a,b)) with b 
end.

Tactic Notation "forward_while" constr(Inv) constr (Postcond) :=
  check_Delta;
  repeat (apply -> seq_assoc; abbreviate_semax);
  first [ignore (Inv: environ->mpred) 
         | fail 1 "Invariant (first argument to forward_while) must have type (environ->mpred)"];
  first [ignore (Postcond: environ->mpred)
         | fail 1 "Postcondition (second argument to forward_while) must have type (environ->mpred)"];
  apply semax_pre with Inv;
    [  unfold_function_derives_right 
    | apply semax_seq with Postcond;
      [repeat match goal with
       | |- semax _ (exp _) _ _ => fail 1
       | |- semax _ (PROPx _ _) _ _ => fail 1
       | |- semax _ ?Pre _ _ => match Pre with context [ ?F ] => unfold F end
       end;
       match goal with |- semax _ ?Pre _ _ =>
          let p := fresh "Pre" in let Hp := fresh "HPre" in 
          remember Pre as p eqn:Hp;
          repeat rewrite exp_uncurry in Hp; subst p
       end;
       match goal with |- semax ?Delta ?Pre (Swhile ?e _) _ =>
        first [eapply semax_while'_new | eapply semax_while'_new1]; 
        simpl typeof;
       [ reflexivity 
       | no_intros || idtac
       | do_compute_expr1 Delta Pre e; eassumption
       | no_intros || (autorewrite with ret_assert;
         let HRE := fresh "HRE" in apply derives_extract_PROP; intro HRE;
         repeat (apply derives_extract_PROP; intro); 
         do_repr_inj HRE; normalize in HRE)
       | no_intros || (let HRE := fresh "HRE" in apply semax_extract_PROP; intro HRE;
          repeat (apply semax_extract_PROP; intro); 
          do_repr_inj HRE; normalize in HRE)
        ]
       end
       | simpl update_tycon 
       ]
     ]; abbreviate_semax; autorewrite with ret_assert.


Tactic Notation "forward_while" constr(Inv) constr (Postcond) 
     simple_intropattern(pat) :=
  repeat (apply -> seq_assoc; abbreviate_semax);
  first [ignore (Inv: environ->mpred) 
         | fail 1 "Invariant (first argument to forward_while) must have type (environ->mpred)"];
  first [ignore (Postcond: environ->mpred)
         | fail 1 "Postcondition (second argument to forward_while) must have type (environ->mpred)"];
  apply semax_pre with Inv;
    [  unfold_function_derives_right 
    | apply semax_seq with Postcond;
      [repeat match goal with
       | |- semax _ (exp _) _ _ => fail 1
       | |- semax _ (PROPx _ _) _ _ => fail 1
       | |- semax _ ?Pre _ _ => match Pre with context [ ?F ] => unfold F end
       end;
       match goal with |- semax _ ?Pre _ _ =>
          let p := fresh "Pre" in let Hp := fresh "HPre" in 
          remember Pre as p eqn:Hp;
          repeat rewrite exp_uncurry in Hp; subst p
       end;
       match goal with |- semax ?Delta ?Pre (Swhile ?e _) _ =>
        first [eapply semax_while'_new | eapply semax_while'_new1]; 
        simpl typeof;
       [ reflexivity 
       | intros pat; simpl_fst_snd
       | do_compute_expr1 Delta Pre e; eassumption
       | intros pat; simpl_fst_snd; 
         autorewrite with ret_assert;
         let HRE := fresh "HRE" in apply derives_extract_PROP; intro HRE;
         repeat (apply derives_extract_PROP; intro); 
         do_repr_inj HRE; normalize in HRE
       | intros pat; simpl_fst_snd;
          let HRE := fresh "HRE" in apply semax_extract_PROP; intro HRE;
          repeat (apply semax_extract_PROP; intro); 
          do_repr_inj HRE; normalize in HRE
        ]
       end
       | simpl update_tycon 
       ]
     ]; abbreviate_semax; autorewrite with ret_assert.

Ltac forward_for_simple_bound n Pre :=
  check_Delta;
 repeat match goal with |-
      semax _ _ (Ssequence (Ssequence (Ssequence _ _) _) _) _ =>
      apply -> seq_assoc; abbreviate_semax
 end;
 first [ 
     simple eapply semax_seq'; 
    [forward_for_simple_bound' n Pre 
    | cbv beta; simpl update_tycon; abbreviate_semax  ]
  | eapply semax_post_flipped'; 
     [forward_for_simple_bound' n Pre 
     | ]
  ].

Ltac forward_for Inv PreIncr Postcond :=
  check_Delta;
  repeat (apply -> seq_assoc; abbreviate_semax);
  first [ignore (Inv: environ->mpred) 
         | fail 1 "Invariant (first argument to forward_for) must have type (environ->mpred)"];
  first [ignore (Postcond: environ->mpred)
         | fail 1 "Postcondition (last argument to forward_for) must have type (environ->mpred)"];
  apply semax_pre with Inv;
    [  unfold_function_derives_right 
    | (apply semax_seq with Postcond;
       [ first 
          [ apply semax_for' with PreIncr
          | apply semax_for with PreIncr
          ]; 
          [ compute; auto 
          | unfold_and_local_derives
          | unfold_and_local_derives
          | unfold_and_local_semax
          | unfold_and_local_semax
          ] 
       | simpl update_tycon 
       ])
    ]; abbreviate_semax; autorewrite with ret_assert.


Ltac forward_if' := 
  check_Delta;
match goal with 
| |- @semax _ ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) 
                                 (Sifthenelse ?e _ _) _ => 
 (apply semax_ifthenelse_PQR; [ reflexivity | quick_typecheck | | ])
  || fail 2 "semax_ifthenelse_PQR did not match"
end.

Ltac forward_if'_new := 
  check_Delta;
match goal with |- semax ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) (Sifthenelse ?e ?c1 ?c2) _ =>
   let HRE := fresh "H" in let v := fresh "v" in
    evar (v: val);
    do_compute_expr Delta P Q R e v HRE;
    simpl in v;
    apply semax_ifthenelse_PQR' with (v:=v);
     [ reflexivity | entailer | assumption 
     | clear HRE; subst v; apply semax_extract_PROP; intro HRE; 
       do_repr_inj HRE
     | clear HRE; subst v; apply semax_extract_PROP; intro HRE; 
       do_repr_inj HRE
     ]
end.

Ltac forward_if_tac post :=
  check_Delta;
  repeat (apply -> seq_assoc; abbreviate_semax);
first [ignore (post: environ->mpred) 
      | fail 1 "Invariant (first argument to forward_if) must have type (environ->mpred)"];
match goal with
 | |- semax _ _ (Sifthenelse _ _ _) (overridePost post _) =>
       forward_if'_new 
 | |- semax _ _ (Sifthenelse _ _ _) ?P =>
      apply (semax_post_flipped (overridePost post P)); 
      [ forward_if'_new
      | try solve [normalize]
      ]
   | |- semax _ _ (Ssequence (Sifthenelse _ _ _) _) _ =>
     apply semax_seq with post;
      [forward_if'_new | abbreviate_semax; autorewrite with ret_assert]
end.

Tactic Notation "forward_if" constr(post) :=
  forward_if_tac post.

Tactic Notation "forward_if" :=
  forward_if'_new.

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
         | extract_prop_from_LOCAL
         | move_from_SEP
         ]; cbv beta; msl.log_normalize.normalize)
  | |- _  => 
    floyd.client_lemmas.normalize
  end.

Tactic Notation "forward_intro" simple_intropattern(v) :=
 match goal with |- _ -> _ => idtac | |- _ => normalize end;
 first [apply extract_exists_pre | apply exp_left | idtac];
 intros v.

Lemma eqb_ident_true: forall i, eqb_ident i i = true.
Proof.
intros; apply Pos.eqb_eq. auto.
Qed.

Lemma eqb_ident_false: forall i j, i<>j -> eqb_ident i j = false.
Proof.
intros; destruct (eqb_ident i j) eqn:?; auto.
apply Pos.eqb_eq in Heqb. congruence.
Qed.

Hint Rewrite eqb_ident_true : subst.
Hint Rewrite eqb_ident_false using solve [auto] : subst.

Lemma subst_temp_special:
  forall i e (f: val -> Prop) j,
   i <> j -> subst i e (`f (eval_id j)) = `f (eval_id j).
Proof.
 intros.
 autorewrite with subst; auto.
Qed.
Hint Rewrite subst_temp_special using safe_auto_with_closed: subst.

Ltac do_subst_eval_expr :=
 change (@map (environ->Prop) (environ->Prop))
   with (fun f: (environ->Prop)->(environ->Prop) =>
              fix map l := match l with nil => nil | a::t => f a :: map t end);
 change (@map (environ->mpred) (environ->mpred))
   with (fun f: (environ->mpred)->(environ->mpred) =>
              fix map l := match l with nil => nil | a::t => f a :: map t end);
  cbv beta iota;
  autorewrite with subst; 
  unfold subst_eval_expr, subst_eval_lvalue, sem_cast;
  simpl eqb_ident; cbv iota;
  fold sem_cast; fold eval_expr; fold eval_lvalue;
  simpl typeof.

Lemma forward_setx_aux1:
  forall P (X Y: environ -> Prop),
  (forall rho, X rho) ->
  (forall rho, Y rho) ->
   P |-- local X && local Y.
Proof.
intros; intro rho; rewrite andp_unfold; apply andp_right; apply prop_right; auto.
Qed.
(*
Ltac forward_setx_wow :=
 eapply forward_setx_wow;
 [ solve [auto 50 with closed]
 | solve [repeat constructor; auto with closed]
 | simpl; first [apply I | reflexivity]
 | simpl; simpl_lift; reflexivity
 | quick_typecheck
 ].

Ltac forward_setx_wow_seq :=
eapply forward_setx_wow_seq;
 [ solve [auto 50 with closed]
 | solve [repeat constructor; auto with closed]
 | simpl; first [apply I | reflexivity]
 | simpl; simpl_lift; reflexivity
 | unfold initialized; simpl; reflexivity
 | quick_typecheck
 | abbreviate_semax
 ].
*)

Ltac intro_old_var' id :=
  match goal with 
  | Name: name id |- _ => 
        let x := fresh Name in
        intro x; do_subst_eval_expr; try clear x
  | |- _ => let x := fresh "x" in 
        intro x; do_subst_eval_expr; try clear x  
  end.

Ltac intro_old_var c :=
  match c with 
  | Sset ?id _ => intro_old_var' id
  | Scall (Some ?id) _ _ => intro_old_var' id
  | Ssequence _ (Sset ?id _) => intro_old_var' id
  | _ => intro x; do_subst_eval_expr; try clear x
  end.

Ltac intro_old_var'' id :=
  match goal with 
  | Name: name id |- _ => 
        let x := fresh Name in
        intro x
  | |- _ => let x := fresh "x" in 
        intro x
  end.

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
Ltac get_global_fun_def Delta f fsig A Pre Post :=
    let VT := fresh "VT" in let GT := fresh "GT" in
      assert (VT: (var_types Delta) ! f = None) by 
               (reflexivity || fail 1 "Variable " f " is not a function, it is an addressable local variable");
      assert (GT: (glob_specs Delta) ! f = Some (mk_funspec fsig A Pre Post))
                    by ((unfold fsig, Pre, Post; try unfold A; simpl; reflexivity) || 
                          fail 1 "Function " f " has no specification in the type context");
     clear VT GT.

Definition This_is_a_warning := tt.

Inductive Warning: unit -> unit -> Prop :=
    ack : forall s s', Warning s s'.
Definition IGNORE_THIS_WARNING_USING_THE_ack_TACTIC_IF_YOU_WISH := tt.

Ltac ack := apply ack.

Ltac all_closed R :=
 match R with 
  | @liftx (LiftEnviron mpred) _ :: ?R' => all_closed R'  
  | @liftx (Tarrow val (LiftEnviron mpred)) _ (eval_var _ _) :: ?R' => all_closed R'
  | nil => idtac
  end.

Definition WARNING__in_your_SEP_clauses_there_is_at_least_one_that_is_not_closed_Use_the_lemma__remember_value__before_moving_forward_through_a_function_call := tt.

Ltac assert_ P :=
  let H := fresh in assert (H: P); [ | clear H].

Ltac warn s := 
   assert_ (Warning s
               IGNORE_THIS_WARNING_USING_THE_ack_TACTIC_IF_YOU_WISH).

Ltac complain_open_sep_terms :=
 match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
    first [all_closed R;  assert_ True
            | warn WARNING__in_your_SEP_clauses_there_is_at_least_one_that_is_not_closed_Use_the_lemma__remember_value__before_moving_forward_through_a_function_call
            ]
 end.

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

Lemma semax_post_flipped3: 
  forall R' Espec Delta P c R,
    @semax Espec Delta P c (normal_ret_assert R') ->
    local (tc_environ (update_tycon Delta c)) && R' |-- R ->
    @semax Espec Delta P c (normal_ret_assert R) .
Proof.
intros; eapply semax_post3; eauto.
Qed.

Ltac forward_call_complain' Delta id ty W :=
     (assert ((var_types Delta) ! id = None) by reflexivity
         || fail 4 "The function-identifier " id " is not a global variable");
    match type of W with ?Wty =>
    assert (match (glob_specs Delta) ! id with
               | Some (mk_funspec fsig t _ _) => Some (type_of_funsig fsig, t)
               | _ => None
               end = Some (ty, Wty)); [
     unfold type_of_funsig; simpl; 
     match goal with
     | |- None = _ => fail 4 "The function identifier " id " is not a function"
     | |- Some (?fsig, ?A) = _ => 
             (assert (ty=fsig) by reflexivity
              || fail 5 "The declared parameter/result types in the funspec for " id " are 
" fsig "which does not match the C program which has" ty);
            (assert (Wty=A) by reflexivity || fail 5 "Use forward_call W, where W is a witness of type " A ";
your witness has type " Wty ".
");
           fail
     | |- _ => fail 4 "Undiagnosed error in forward_call"
     end | ] end.
 
Ltac forward_call_complain W :=
 match goal with 
 | |- semax ?Delta _ (Ssequence (Scall _ (Evar ?id ?ty) _) _) _ =>
       forward_call_complain' Delta id ty W
 | |- semax ?Delta _ (Scall _ (Evar ?id ?ty) _) _ =>
       forward_call_complain' Delta id ty W
  end.

Lemma elim_useless_retval:
 forall Espec Delta P Q (F: val -> Prop) (G: mpred) R c Post,
  @semax Espec Delta (PROPx P (LOCALx Q (SEPx (`G :: R)))) c Post ->
  @semax Espec Delta (PROPx P (LOCALx Q 
    (SEPx 
    (`(fun x : environ => local (`F retval) x && `G x) (make_args nil nil)
      :: R)))) c Post.
Proof.
intros.
eapply semax_pre0; [ | apply H].
apply andp_derives; auto.
apply andp_derives; auto.
apply sepcon_derives; auto.
unfold_lift. unfold local, lift1.
intro rho. apply andp_left2; auto.
Qed.

Definition  DO_THE_after_call_TACTIC_NOW (x: Prop) := x.
Arguments DO_THE_after_call_TACTIC_NOW {x}.

Ltac after_call :=  
  match goal with |- @DO_THE_after_call_TACTIC_NOW _ =>
   unfold DO_THE_after_call_TACTIC_NOW;
   match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx (ifvoid ?A ?B ?C :: _)))) _ _ =>
      first [change (ifvoid A B C) with B | change (ifvoid A B C) with C]
   | _ => idtac
   end;
   autorewrite with subst; normalize;
   clean_up_app_carefully;
   match goal with 
   | |- forall x:val, _ => intros ?retval0; normalize
   | _ => idtac
   end
  end.

Ltac say_after_call :=
 match goal with |- ?x => 
 change (@DO_THE_after_call_TACTIC_NOW x)
 end.

Lemma focus_make_args:
  forall A Q R R' Frame,
    R = R' ->
    A |-- PROPx nil (LOCALx Q (SEPx (R' :: Frame)))  ->
    A |-- PROPx nil (LOCALx Q (SEPx (R :: Frame))) .
Proof.
intros; subst; auto.
Qed.

Lemma subst_make_args1:
  forall i e j v,
    subst i e (make_args (j::nil) (v::nil)) = make_args (j::nil) (v::nil).
Proof. reflexivity. Qed.
Hint Rewrite subst_make_args1 : norm.
Hint Rewrite subst_make_args1 : subst.

Ltac normalize_make_args :=
 cbv beta iota;
 repeat rewrite subst_make_args1;
 let R' := fresh "R" in evar (R': environ->mpred);
   apply focus_make_args with R';
  [norm_rewrite; unfold R'; reflexivity
  | unfold R'; clear R'].

Ltac forward_call W := 
  check_Delta;
 let witness := fresh "witness" in
 pose (witness := W);   (* faster this way, for some reason *)
match goal with
| |- semax _ _ (Ssequence (Ssequence (Scall (Some ?i') _ _) 
                                          (Sset ?i (Etempvar ?i' _))) _) _ =>
   let Frame := fresh "Frame" in evar (Frame: list (environ->mpred));
   eapply semax_seq';
    [eapply (semax_call_id1_x_alt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ witness Frame);
      [reflexivity | reflexivity | reflexivity | reflexivity | apply I | reflexivity | reflexivity 
      | (*reflexivity |*) reflexivity | auto 50 with closed | | unfold Frame; clear Frame ]
    | simpl update_tycon; abbreviate_semax; apply extract_exists_pre; 
      intro_old_var' i; autorewrite with subst; unfold Frame; clear Frame;
     say_after_call ]
| |- semax _ _ (Ssequence (Scall (Some ?i') _ _) 
                                          (Sset ?i (Etempvar ?i' _))) _ =>
   normalize_postcondition;
   let Frame := fresh "Frame" in evar (Frame: list (environ->mpred));
   eapply semax_post_flipped3;
    [eapply (semax_call_id1_x_alt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ witness Frame);
      [reflexivity | reflexivity | reflexivity | reflexivity | apply I | reflexivity | reflexivity 
      | (*reflexivity |*) reflexivity | auto 50 with closed | | unfold Frame; clear Frame ]
    | simpl update_tycon; abbreviate_semax; apply extract_exists_pre; 
      intro_old_var' i; autorewrite with subst; unfold Frame; clear Frame;
     say_after_call ]
| |- semax _ _ (Ssequence (Ssequence _ _) _) _ => 
     apply -> seq_assoc; abbreviate_semax; forward_call witness
| |- semax _ _ (Ssequence (Scall None _ _) _) _ =>
  let Frame := fresh "Frame" in evar (Frame: list (environ->mpred));
  eapply semax_seq';
  [eapply (semax_call_id0_alt _ _ _ _ _ _ _ _ _ _ _ witness Frame);
         [reflexivity | reflexivity | reflexivity | reflexivity | normalize_make_args ]
  | cbv beta iota; try simple apply elim_useless_retval;
    simpl update_tycon; abbreviate_semax; unfold Frame; clear Frame;
    say_after_call ]
| |- semax _ _ (Scall None _ _) _ =>
   normalize_postcondition;
  let Frame := fresh "Frame" in evar (Frame: list (environ->mpred));
   eapply semax_post_flipped3;
  [eapply (semax_call_id0_alt _ _ _ _ _ _ _ _ _ _ _ witness Frame);
         [reflexivity | reflexivity | reflexivity | reflexivity | normalize_make_args ]
  | cbv beta iota; try simple apply elim_useless_retval;
    try rewrite exp_andp2;
    try rewrite insert_local; unfold Frame; clear Frame;
    say_after_call ]
| |- semax _ _ (Ssequence (Scall (Some ?i) _ _) _) _ =>
   let Frame := fresh "Frame" in evar (Frame: list (environ->mpred));
   eapply semax_seq';
    [eapply (semax_call_id1_alt _ _ _ _ _ _ _ _ _ _ _ _ _ _ witness Frame);
            [reflexivity | reflexivity | reflexivity | apply I 
            | simpl; first [apply I | reflexivity]
            |reflexivity | normalize_make_args ]
    | simpl update_tycon; abbreviate_semax; apply extract_exists_pre; 
      intro_old_var' i; autorewrite with subst; unfold Frame; clear Frame;
     say_after_call ]
| |- semax _ _ (Scall (Some ?i) _ _) _ =>
   normalize_postcondition;
   let Frame := fresh "Frame" in evar (Frame: list (environ->mpred));
   eapply semax_post_flipped3;
    [eapply (semax_call_id1_alt _ _ _ _ _ _ _ _ _ _ _ _ _ _ witness Frame);
            [reflexivity | reflexivity | reflexivity | apply I 
            | simpl; first [apply I | reflexivity]
            | reflexivity | normalize_make_args ]
    | try rewrite exp_andp2;
               try (apply exp_left; intro_old_var' i);
               try rewrite insert_local;
               autorewrite with subst; unfold Frame; clear Frame;
               say_after_call ]
 | |- _ => forward_call_complain W
end; 
 unfold witness; try clear witness; simpl argtypes.

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
  check_Delta;
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

Ltac forward_setx :=
first [(*forward_setx_wow
       |*) 
         ensure_normal_ret_assert;
         hoist_later_in_pre;
         match goal with
         | |- semax ?Delta (|> (PROPx ?P (LOCALx ?Q (SEPx ?R)))) (Sset _ ?e) _ =>
                let v := fresh "v" in evar (v : val);
                let HRE := fresh "H" in
                do_compute_expr Delta P Q R e v HRE;
                eapply semax_SC_set;
                  [reflexivity | reflexivity | exact HRE 
                  | try solve [entailer!]; try (clear HRE; subst v)]
         end
       | apply forward_setx_closed_now;
            [solve [auto 50 with closed] | solve [auto 50 with closed] | solve [auto 50 with closed]
            | try apply local_True_right
            | try apply local_True_right
            |  ]
        | apply forward_setx; quick_typecheck
        ].

Ltac forward_setx_with_pcmp e :=
tac_if (ptr_compare e) ltac:forward_ptr_cmp ltac:forward_setx.

(* BEGIN new semax_load and semax_store tactics *************************)

Lemma solve_legal_nested_field_in_entailment_aux: forall (P: environ -> mpred) Q R, (Q <-> R) -> P |-- !!R -> P |-- !!Q.
Proof.
  intros.
  eapply derives_trans; eauto.
  normalize.
  tauto.
Qed.

Ltac solve_legal_nested_field_in_entailment' :=
  first
  [ solve [(apply prop_right; apply legal_nested_field_nil_lemma)]
  | eapply solve_legal_nested_field_in_entailment_aux; [apply legal_nested_field_cons_lemma |];
    rewrite prop_and; apply andp_right; [solve_legal_nested_field_in_entailment' | try solve [entailer!]]].

Ltac solve_legal_nested_field_in_entailment :=
match goal with
| |- _ |-- !! legal_nested_field ?t_root (?gfs1 ++ ?gfs0) =>
  unfold t_root, gfs0, gfs1
end;
match goal with 
| |- _ |-- !! ?M => simpl M
end;
solve_legal_nested_field_in_entailment'.

Ltac construct_nested_efield e e1 efs tts :=
  let pp := fresh "pp" in
    pose (compute_nested_efield e) as pp;
    simpl in pp;
    pose (fst (fst pp)) as e1;
    pose (snd (fst pp)) as efs;
    pose (snd pp) as tts;
    simpl in e1, efs, tts;
    change e with (nested_efield e1 efs tts);
    clear pp.

Lemma efield_denote_cons_array: forall P efs gfs ei i,
  P |-- efield_denote efs gfs ->
  P |-- local (`(eq (Vint (Int.repr i))) (eval_expr ei)) ->
  match typeof ei with
  | Tint _ _ _ => True
  | _ => False
  end ->
  P |-- efield_denote (eArraySubsc ei :: efs) (ArraySubsc i :: gfs).
Proof.
  intros.
  simpl efield_denote.
  intro rho.
  repeat apply andp_right; auto.
  apply prop_right, H1.
Qed.

Lemma efield_denote_cons_struct: forall P efs gfs i,
  P |-- efield_denote efs gfs ->
  P |-- efield_denote (eStructField i :: efs) (StructField i :: gfs).
Proof.
  intros.
  simpl efield_denote.
  eapply derives_trans; [exact H |].
  normalize.
Qed.

Lemma efield_denote_cons_union: forall P efs gfs i,
  P |-- efield_denote efs gfs ->
  P |-- efield_denote (eUnionField i :: efs) (UnionField i :: gfs).
Proof.
  intros.
  simpl efield_denote.
  eapply derives_trans; [exact H |].
  normalize.
Qed.

Ltac test_legal_nested_efield SE TY e gfs tts lr H_LEGAL :=
  assert (legal_nested_efield SE TY e gfs tts lr = true) as H_LEGAL by reflexivity.

Ltac sc_try_instantiate P Q R0 Delta e gfs tts p sh t_root gfs0 v n N H SH GFS TY V:=
      assert (PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx (R0 :: nil))) 
         |-- `(field_at sh t_root gfs0 v p)) as H;
      [unfold sh, t_root, gfs0, v, p;
       try rewrite !(data_at_field_at SH);
       try rewrite !(data_at__field_at_ SH);
       instantiate (2 := GFS);
       instantiate (2 := TY);
       assert (GFS = skipn (length gfs - length GFS) gfs) as _ by reflexivity;
       simpl skipn; subst e gfs tts;
       instantiate (2 := SH);
       instantiate (1 := V);
       try unfold field_at_;
       generalize V;
       intro;
       solve [
         first [apply remove_PROP_LOCAL_left'; apply derives_refl
               | entailer!; cancel]
       ]
      | pose N as n ].

Ltac sc_new_instantiate SE P Q R Rnow Delta e gfs tts lr p sh t_root gfs0 v n N H H_LEGAL:=
  match Rnow with
  | ?R0 :: ?Rnow' => 
    match R0 with
    | `(data_at ?SH ?TY ?V _) => 
      test_legal_nested_efield SE TY e gfs tts lr H_LEGAL;
      sc_try_instantiate P Q R0 Delta e gfs tts p sh t_root gfs0 v n N H SH (@nil gfield) TY V
    | `(data_at_ ?SH ?TY _) => 
      test_legal_nested_efield SE TY e gfs tts lr H_LEGAL;
      sc_try_instantiate P Q R0 Delta e gfs tts p sh t_root gfs0 v n N H SH (@nil gfield) TY
      (default_val (nested_field_type2 TY nil))
    | `(field_at ?SH ?TY ?GFS ?V _) =>
      test_legal_nested_efield SE TY e gfs tts lr H_LEGAL;
      sc_try_instantiate P Q R0 Delta e gfs tts p sh t_root gfs0 v n N H SH GFS TY V
    | `(field_at_ ?SH ?TY ?GFS _) =>
      test_legal_nested_efield SE TY e gfs tts lr H_LEGAL;
      sc_try_instantiate P Q R0 Delta e gfs tts p sh t_root gfs0 v n N H SH GFS TY
      (default_val (nested_field_type2 TY GFS))
    | _ => sc_new_instantiate SE P Q R Rnow' Delta e gfs tts lr p sh t_root gfs0 v n (S N) H H_LEGAL
    end
  end.

Ltac solve_efield_denote Delta P Q R efs gfs H :=
  evar (gfs : list gfield);
  assert (PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- efield_denote efs gfs) as H; 
  [
    unfold efs, gfs;
    match goal with
    | efs := nil |- _ =>
      instantiate (1 := nil);
      simpl efield_denote;
      intro rho;
      apply prop_right, I
    | efs := ?ef :: ?efs' |- _ =>
      let efs0 := fresh "efs" in
      let gfs0 := fresh "gfs" in
      let H0 := fresh "H" in
      pose efs' as efs0;
      solve_efield_denote Delta P Q R efs0 gfs0 H0;
      match goal with
      | gfs0 := ?gfs0' |- _ =>
        match ef with
        | eArraySubsc ?ei => 

          let HA := fresh "H" in
          let vi := fresh "vi" in evar (vi: val);
          do_compute_expr Delta P Q R ei vi HA;

          revert vi HA;
          let vvvv := fresh "vvvv" in
          let HHHH := fresh "HHHH" in
            match goal with
            | |- let vi := ?V in _ => remember V as vvvv eqn:HHHH
            end;
          autorewrite with norm in HHHH;
      
          match type of HHHH with
          | _ = Vint (Int.repr _) => idtac
          | _ = Vint (Int.sub _ _) => unfold Int.sub in HHHH
          | _ = Vint (Int.add _ _) => unfold Int.add in HHHH
          | _ = Vint (Int.mul _ _) => unfold Int.mul in HHHH
          | _ = Vint (Int.and _ _) => unfold Int.and in HHHH
          | _ = Vint (Int.or _ _) => unfold Int.or in HHHH
          | _ = Vint ?V =>
            replace V with (Int.repr (Int.unsigned V)) in HHHH
              by (rewrite (Int.repr_unsigned V); reflexivity)
          end;
          subst vvvv; intros vi HA;

          match goal with
          | vi := Vint (Int.repr ?i) |- _ => instantiate (1 := ArraySubsc i :: gfs0')
          end;
          
          let HB := fresh "H" in
          assert (match typeof ei with | Tint _ _ _ => True | _ => False end) as HB by (simpl; auto);
          
          apply (efield_denote_cons_array _ _ _ _ _ H0 HA HB)

        | eStructField ?i =>
          instantiate (1 := StructField i :: gfs0');
          apply efield_denote_cons_struct, H0
        | eUnionField ?i =>
          instantiate (1 := StructField i :: gfs0');
          apply efield_denote_cons_struct, H0
        end
      end
    end
  |].

Ltac try_instantiate_load P Q R0 Delta e ids tts sh ids0 v n N H SH IDS V:=
      assert (PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx (R0 :: nil))) 
         |-- (`(field_at sh (typeof e) ids0 v) (eval_lvalue e))) as H;
      [unfold sh, ids0, v;
       try rewrite !(data_at_field_at SH);
       instantiate (2 := IDS);
       assert (IDS = skipn (length ids - length IDS) ids) as _ by reflexivity;
       simpl skipn; subst e ids tts;
       instantiate (2 := SH);
       instantiate (1 := V);
       try unfold field_at_;
       generalize V;
       intro;
       solve [(entailer!; cancel)]
      | pose N as n ].

Ltac new_instantiate_load P Q R Rnow Delta e ids tts sh ids0 v n N H:=
  match Rnow with
  | ?R0 :: ?Rnow' => 
    match R0 with
    | `(data_at ?SH _ ?V _) => 
      try_instantiate_load P Q R0 Delta e ids tts sh ids0 v n N H SH (@nil ident) V
    | `(data_at ?SH _ ?V) _ => 
      try_instantiate_load P Q R0 Delta e ids tts sh ids0 v n N H SH (@nil ident) V
    | `(data_at_ ?SH ?TY _) => 
      try_instantiate_load P Q R0 Delta e ids tts sh ids0 v n N H SH (@nil ident)
      (default_val (nested_field_type2 TY nil))
    | `(data_at_ ?SH ?TY) _ => 
      try_instantiate_load P Q R0 Delta e ids tts sh ids0 v n N H SH (@nil ident)
      (default_val (nested_field_type2 TY nil))
    | `(field_at ?SH _ ?IDS ?V _) =>
      try_instantiate_load P Q R0 Delta e ids tts sh ids0 v n N H SH IDS V
    | `(field_at ?SH _ ?IDS ?V) _ => 
      try_instantiate_load P Q R0 Delta e ids tts sh ids0 v n N H SH IDS V
    | `(field_at_ ?SH ?TY ?IDS _) =>
      try_instantiate_load P Q R0 Delta e ids tts sh ids0 v n N H SH IDS 
      (default_val (nested_field_type2 TY IDS))
    | `(field_at_ ?SH ?TY ?IDS) _ => 
      try_instantiate_load P Q R0 Delta e ids tts sh ids0 v n N H SH IDS 
      (default_val (nested_field_type2 TY IDS))
    | _ => new_instantiate_load P Q R Rnow' Delta e ids tts sh ids0 v n (S N) H
    end
  end.

Ltac try_instantiate_store P Q R0 Delta e ids tts sh ids0 v n N H SH TY IDS V:=
      assert (PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx (R0 :: nil))) 
         |-- (`(field_at sh (typeof e) ids0) v (eval_lvalue e))) as H;
      [unfold sh, ids0, v;
       try rewrite !data_at_field_at; (* move to somewhere later? *)
       instantiate (2 := IDS);
       assert (IDS = skipn (length ids - length IDS) ids) as _ by reflexivity;
       simpl skipn; subst e ids tts;
       instantiate (2 := SH);
       instantiate (1 := V);
       try unfold field_at_;
       try rewrite <- (@liftx1_liftx0 val mpred);
       try rewrite <- (@liftx2_liftx1 (reptype (nested_field_type2 TY IDS)) val mpred);
       simpl typeof;
       simpl reptype;
       generalize V;
       intro;
       solve [(entailer!; cancel)]
      | pose N as n ].

Ltac new_instantiate_store P Q R Rnow Delta e ids tts sh ids0 v n N H:=
  match Rnow with
  | ?R0 :: ?Rnow' => 
    match R0 with
    | `(data_at ?SH ?TY ?V _) => 
      try_instantiate_store P Q R0 Delta e ids tts sh ids0 v n N H SH TY (@nil ident) (` V)
    | `(data_at ?SH ?TY ?V) _ => 
      try_instantiate_store P Q R0 Delta e ids tts sh ids0 v n N H SH TY (@nil ident) (` V)
    | `(data_at ?SH ?TY) ?V _ => 
      try_instantiate_store P Q R0 Delta e ids tts sh ids0 v n N H SH TY (@nil ident) V
    | `(data_at_ ?SH ?TY _) => 
      try_instantiate_store P Q R0 Delta e ids tts sh ids0 v n N H SH TY (@nil ident)
      (`(default_val (nested_field_type2 TY nil)))
    | `(data_at_ ?SH ?TY) _ => 
      try_instantiate_store P Q R0 Delta e ids tts sh ids0 v n N H SH TY (@nil ident)
      (`(default_val (nested_field_type2 TY nil)))
    | `(field_at ?SH ?TY ?IDS ?V _) =>
      try_instantiate_store P Q R0 Delta e ids tts sh ids0 v n N H SH TY IDS (` V)
    | `(field_at ?SH ?TY ?IDS ?V) _ => 
      try_instantiate_store P Q R0 Delta e ids tts sh ids0 v n N H SH TY IDS (` V)
    | `(field_at ?SH ?TY ?IDS) ?V _ => 
      try_instantiate_store P Q R0 Delta e ids tts sh ids0 v n N H SH TY IDS V
    | `(field_at_ ?SH ?TY ?IDS _) =>
      try_instantiate_store P Q R0 Delta e ids tts sh ids0 v n N H SH TY IDS 
      (`(default_val (nested_field_type2 TY IDS)))
    | `(field_at_ ?SH ?TY ?IDS) _ => 
      try_instantiate_store P Q R0 Delta e ids tts sh ids0 v n N H SH TY IDS 
      (`(default_val (nested_field_type2 TY IDS)))
    | _ => new_instantiate_store P Q R Rnow' Delta e ids tts sh ids0 v n (S N) H
    end
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

Ltac new_load_tac :=   (* matches:  semax _ _ (Sset _ (Efield _ _ _)) _  *)
 ensure_normal_ret_assert;
 hoist_later_in_pre;
 match goal with
 | Struct_env := @abbreviate type_id_env _ |- _ => idtac
 | |- _ => let Struct_env := fresh "Struct_env" in
     pose (Struct_env := @abbreviate _ empty_ti)
 end; 
 match goal with   
| SE := @abbreviate type_id_env _ 
    |- semax ?Delta (|> (PROPx ?P (LOCALx ?Q (SEPx ?R)))) (Sset _ (Ecast ?e _)) _ =>
 (* Super canonical cast load *)
    let e1 := fresh "e" in
    let efs := fresh "efs" in
    let tts := fresh "tts" in
      construct_nested_efield e e1 efs tts;

    let lr := fresh "lr" in
      pose (compute_lr e1 efs) as lr;
      vm_compute in lr;

    let HLE := fresh "H" in
    let p := fresh "p" in evar (p: val);
      match goal with
      | lr := LLLL |- _ => do_compute_lvalue Delta P Q R e1 p HLE
      | lr := RRRR |- _ => do_compute_expr Delta P Q R e1 p HLE
      end;

    let H_Denote := fresh "H" in
    let gfs := fresh "gfs" in
      solve_efield_denote Delta P Q R efs gfs H_Denote;

    let sh := fresh "sh" in evar (sh: share);
    let t_root := fresh "t_root" in evar (t_root: type);
    let gfs0 := fresh "gfs" in evar (gfs0: list gfield);
    let v := fresh "v" in evar (v: reptype (nested_field_type2 t_root gfs0));
    let n := fresh "n" in
    let H := fresh "H" in
    let H_LEGAL := fresh "H" in
    sc_new_instantiate SE P Q R R Delta e1 gfs tts lr p sh t_root gfs0 v n (0%nat) H H_LEGAL;
    
    let gfs1 := fresh "gfs" in
    let len := fresh "len" in
    pose ((length gfs - length gfs0)%nat) as len;
    simpl in len;
    match goal with
    | len := ?len' |- _ =>
      pose (firstn len' gfs) as gfs1
    end;
    clear len;
    unfold gfs in gfs0, gfs1;
    simpl firstn in gfs1;
    simpl skipn in gfs0;

    change gfs with (gfs1 ++ gfs0) in *;
    subst gfs p;

    let Heq := fresh "H" in
    match type of H with
    | (PROPx _ (LOCALx _ (SEPx (?R0 :: nil))) 
           |-- _) => assert (nth_error R n = Some R0) as Heq by reflexivity
    end;
    eapply (semax_SC_field_cast_load Delta sh SE n) with (lr0 := lr) (t_root0 := t_root) (gfs2 := gfs0) (gfs3 := gfs1);
    [reflexivity | reflexivity | reflexivity
    | reflexivity | exact Heq | exact HLE | exact H_Denote 
    | exact H | reflexivity
    | unfold tc_efield; try solve [entailer!]; try (clear Heq HLE H_Denote H H_LEGAL;
      subst e1 gfs0 gfs1 efs tts t_root v sh lr n; simpl app; simpl typeof)
    | solve_legal_nested_field_in_entailment; try clear Heq HLE H_Denote H H_LEGAL;
      subst e1 gfs0 gfs1 efs tts t_root v sh lr n]

| SE := @abbreviate type_id_env.type_id_env _ 
    |- semax ?Delta (|> (PROPx ?P (LOCALx ?Q (SEPx ?R)))) (Sset _ ?e) _ =>
 (* Super canonical load *)
    let e1 := fresh "e" in
    let efs := fresh "efs" in
    let tts := fresh "tts" in
      construct_nested_efield e e1 efs tts;

    let lr := fresh "lr" in
      pose (compute_lr e1 efs) as lr;
      vm_compute in lr;

    let HLE := fresh "H" in
    let p := fresh "p" in evar (p: val);
      match goal with
      | lr := LLLL |- _ => do_compute_lvalue Delta P Q R e1 p HLE
      | lr := RRRR |- _ => do_compute_expr Delta P Q R e1 p HLE
      end;

    let H_Denote := fresh "H" in
    let gfs := fresh "gfs" in
      solve_efield_denote Delta P Q R efs gfs H_Denote;

    let sh := fresh "sh" in evar (sh: share);
    let t_root := fresh "t_root" in evar (t_root: type);
    let gfs0 := fresh "gfs" in evar (gfs0: list gfield);
    let v := fresh "v" in evar (v: reptype (nested_field_type2 t_root gfs0));
    let n := fresh "n" in
    let H := fresh "H" in
    let H_LEGAL := fresh "H" in
    sc_new_instantiate SE P Q R R Delta e1 gfs tts lr p sh t_root gfs0 v n (0%nat) H H_LEGAL;
    
    let gfs1 := fresh "gfs" in
    let len := fresh "len" in
    pose ((length gfs - length gfs0)%nat) as len;
    simpl in len;
    match goal with
    | len := ?len' |- _ =>
      pose (firstn len' gfs) as gfs1
    end;

    clear len;
    unfold gfs in gfs0, gfs1;
    simpl firstn in gfs1;
    simpl skipn in gfs0;

    change gfs with (gfs1 ++ gfs0) in *;
    subst gfs p;

    let Heq := fresh "H" in
    match type of H with
    | (PROPx _ (LOCALx _ (SEPx (?R0 :: nil))) 
           |-- _) => assert (nth_error R n = Some R0) as Heq by reflexivity
    end;

    eapply (semax_SC_field_load Delta sh SE n) with (lr0 := lr) (t_root0 := t_root) (gfs2 := gfs0) (gfs3 := gfs1);
    [reflexivity | reflexivity | reflexivity
    | reflexivity | exact Heq | exact HLE | exact H_Denote 
    | exact H | reflexivity
    | unfold tc_efield; try solve [entailer!]; try (clear Heq HLE H_Denote H H_LEGAL;
      subst e1 gfs0 gfs1 efs tts t_root v sh lr n; simpl app; simpl typeof)
    | solve_legal_nested_field_in_entailment; try clear Heq HLE H_Denote H H_LEGAL;
      subst e1 gfs0 gfs1 efs tts t_root v sh lr n]

 | |- _ => eapply semax_cast_load_37';
   [reflexivity 
   |entailer;
    try (apply andp_right; [apply prop_right | solve [cancel] ];
           do 2 eexists; split; reflexivity)
    ]
 | |- _ => eapply semax_load_37';
   [reflexivity | reflexivity
   | entailer;
    try (apply andp_right; [apply prop_right | solve [cancel] ];
           do 2 eexists; split; reflexivity)
    ]
 end.

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
| Struct_env := @abbreviate type_id_env _ |- _ => idtac
| |- _ => let Struct_env := fresh "Struct_env" in
   pose (Struct env := @abbreviate _ empty_ti)
end; 
match goal with
| SE := @abbreviate type_id_env.type_id_env _ 
    |- semax ?Delta (|> (PROPx ?P (LOCALx ?Q (SEPx ?R)))) (Sassign ?e ?e2) _ =>
  (* Super canonical field store *)
    let e1 := fresh "e" in
    let efs := fresh "efs" in
    let tts := fresh "tts" in
      construct_nested_efield e e1 efs tts;

    let lr := fresh "lr" in
      pose (compute_lr e1 efs) as lr;
      vm_compute in lr;

    let HLE := fresh "H" in
    let p := fresh "p" in evar (p: val);
      match goal with
      | lr := LLLL |- _ => do_compute_lvalue Delta P Q R e1 p HLE
      | lr := RRRR |- _ => do_compute_expr Delta P Q R e1 p HLE
      end;

    let HRE := fresh "H" in
    let v0 := fresh "v" in evar (v0: val);
      do_compute_expr Delta P Q R (Ecast e2 (typeof (nested_efield e1 efs tts))) v0 HRE;

    let H_Denote := fresh "H" in
    let gfs := fresh "gfs" in
      solve_efield_denote Delta P Q R efs gfs H_Denote;

    let sh := fresh "sh" in evar (sh: share);
    let t_root := fresh "t_root" in evar (t_root: type);
    let gfs0 := fresh "gfs" in evar (gfs0: list gfield);
    let v := fresh "v" in evar (v: reptype (nested_field_type2 t_root gfs0));
    let n := fresh "n" in
    let H := fresh "H" in
    let H_LEGAL := fresh "H" in
    sc_new_instantiate SE P Q R R Delta e1 gfs tts lr p sh t_root gfs0 v n (0%nat) H H_LEGAL;

    let gfs1 := fresh "gfs" in
    let len := fresh "len" in
    pose ((length gfs - length gfs0)%nat) as len;
    simpl in len;
    match goal with
    | len := ?len' |- _ =>
      pose (firstn len' gfs) as gfs1
    end;

    clear len;
    unfold gfs in gfs0, gfs1;
    simpl firstn in gfs1;
    simpl skipn in gfs0;

    change gfs with (gfs1 ++ gfs0) in *;
    subst gfs p;

    let Heq := fresh "H" in
    match type of H with
    | (PROPx _ (LOCALx _ (SEPx (?R0 :: nil))) 
           |-- _) => assert (nth_error R n = Some R0) as Heq by reflexivity
    end;

    match type of H with
    | (PROPx _ (LOCALx _ (SEPx (?R0 :: nil))) |-- _) =>
      match R0 with
      | appcontext [field_at] =>
        eapply (semax_SC_field_store Delta sh SE n) 
          with (lr0 := lr) (t_root0 := t_root) (gfs2 := gfs0) (gfs3 := gfs1);
        [reflexivity | reflexivity | reflexivity
        | reflexivity | exact Heq | exact HLE
        | exact HRE | exact H_Denote | exact H | auto
        | unfold tc_efield; try solve[entailer!]; try (clear Heq HLE HRE H_Denote H H_LEGAL;
          subst e1 gfs0 gfs1 efs tts t_root sh v0 lr n; simpl app; simpl typeof)
        | solve_legal_nested_field_in_entailment; try clear Heq HLE HRE H_Denote H H_LEGAL;
          subst e1 gfs0 gfs1 efs tts t_root sh v0 lr n ]
      | appcontext [field_at_] =>
        eapply (semax_SC_field_store Delta sh SE n)
          with (lr0 := lr) (t_root0 := t_root) (gfs2 := gfs0) (gfs3 := gfs1);
        [reflexivity | reflexivity | reflexivity
        | reflexivity | exact Heq | exact HLE
        | exact HRE | exact H_Denote | exact H | auto 
        | unfold tc_efield; try solve[entailer!]; try (clear Heq HLE HRE H_Denote H H_LEGAL;
          subst e1 gfs0 gfs1 efs tts t_root sh v0 lr n; simpl app; simpl typeof)
        | solve_legal_nested_field_in_entailment; try clear Heq HLE HRE H_Denote H H_LEGAL;
          subst e1 gfs0 gfs1 efs tts t_root sh v0 lr n ]
      | _ =>
        eapply semax_post'; [ |
          eapply (semax_SC_field_store Delta sh SE n)
            with (lr0 := lr) (t_root0 := t_root) (gfs2 := gfs0) (gfs3 := gfs1);
            [reflexivity | reflexivity | reflexivity
            | reflexivity | exact Heq | exact HLE 
            | exact HRE | exact H_Denote | exact H | auto | | ]];
        [ match goal with
          | |- appcontext [replace_nth _ _ ?M] => 
            let EQ := fresh "EQ" in
            let MM := fresh "MM" in
               remember M as MM eqn:EQ;
               try rewrite <- data_at__field_at_ in EQ;
               try rewrite <- data_at_field_at in EQ;
               subst MM;
               apply derives_refl
          end
        | unfold tc_efield; try solve[entailer!]; try (clear Heq HLE HRE H_Denote H H_LEGAL;
          subst e1 gfs0 gfs1 efs tts t_root sh v0 lr n; simpl app; simpl typeof)
        | solve_legal_nested_field_in_entailment; try clear Heq HLE HRE H_Denote H H_LEGAL;
          subst e1 gfs0 gfs1 efs tts t_root sh v0 lr n ]
      end
    end

  | |- @semax ?Espec ?Delta (|> PROPx ?P (LOCALx ?Q (SEPx ?R))) 
                     (Sassign ?e ?e2) _ =>

 let n := fresh "n" in evar (n: nat); 
  let sh := fresh "sh" in evar (sh: share);
  assert (PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx (number_list O R))) 
     |-- (`(numbd n (mapsto_ sh (typeof e))) (eval_lvalue e)) * TT) as _;
  [ unfold number_list, n, sh; 
   repeat rewrite numbd_lift1; repeat rewrite numbd_lift2;
   unfold at_offset; solve [entailer; cancel]
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
     (eapply semax_pre; [  | apply semax_return ]; 
      entailer_for_return).

Ltac forward_ifthenelse :=
           semax_logic_and_or 
           ||  fail 2 "Use this tactic:  forward_if POST, where POST is the post condition".

Ltac forward_while_complain :=
           fail 2 "Use this tactic:  forward_while INV POST,
    where INV is the loop invariant and POST is the postcondition".

Ltac forward_for_complain := 
           fail 2 "Use this tactic:  forward_for INV PRE_INCR POST,
      where INV is the loop invariant, PRE_INCR is the invariant at the increment,
      and POST is the postcondition".

(* The forward_compound_call tactic is needed because CompCert clightgen
 produces the following AST for function call:
  (Ssequence (Scall (Some id') ... ) (Sset id (Etempvar id' _)))
instead of the more natural
   (Scall id ...)
Our general tactics are powerful enough to reason about the sequence,
one statement at a time, but it is not nice to burden the user with knowing
about id'.  So we handle it all in one gulp.
 See also BEGIN HORRIBLE1 in forward_lemmas.v
*)
Ltac forward_compound_call :=
  complain_open_sep_terms; [auto |
  ensure_open_normal_ret_assert;
   match goal with |-  @semax ?Espec ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) 
               (Ssequence (Scall (Some ?id') (Evar ?f _) ?bl)
                       (Sset ?id (Etempvar ?id' _))) _ =>

         let fsig:=fresh "fsig" in let A := fresh "A" in let Pre := fresh "Pre" in let Post := fresh"Post" in
         evar (fsig: funsig); evar (A: Type); evar (Pre: A -> environ->mpred); evar (Post: A -> environ->mpred);
         get_global_fun_def Delta f fsig A Pre Post;
    let x := fresh "witness" in let F := fresh "Frame" in
      evar (x:A); evar (F: list (environ->mpred)); 
      apply semax_pre with (PROPx P
                (LOCALx (tc_exprlist Delta (argtypes (fst fsig)) bl :: Q)
                 (SEPx (`(Pre x)  (make_args' fsig (eval_exprlist (argtypes (fst fsig)) bl)) ::
                            F))));
       [
       | apply (semax_call_id1_x Espec Delta P Q F id id' f 
                   (snd fsig) bl (fst fsig) A x Pre Post 
                      (eq_refl _) (eq_refl _) I) ; 
               [ (solve[ simpl; auto with closed]  || solve [auto with closed]) (* FIXME!*)
               | unfold F (*solve[simpl; auto with closed] PREMATURELY INSTANTIATES FRAME *) 
               | reflexivity | reflexivity | reflexivity | reflexivity ]]
               ;
  unfold fsig, A, Pre, Post in *; clear fsig A Pre Post
end ].


Ltac forward_skip := apply semax_skip.

Ltac no_loads_expr e as_lvalue enforce :=
 match e with
 | Econst_int _ _ => idtac
 | Econst_float _ _ => idtac
 | Econst_long _ _ => idtac
 | Evar _ _ => match as_lvalue with true => idtac end
 | Etempvar _ _ => idtac
 | Eaddrof ?e1 _ => no_loads_expr e1 true enforce
 | Eunop _ ?e1 _ => no_loads_expr e1 as_lvalue enforce
 | Ebinop _ ?e1 ?e2 _ => no_loads_expr e1 as_lvalue enforce; no_loads_expr e2 as_lvalue enforce
 | Ecast ?e1 _ => no_loads_expr e1 as_lvalue enforce
 | Efield ?e1 _ _ => match as_lvalue with true =>
                              no_loads_expr e1 true enforce
                              end
 | _ => match enforce with false =>
            let r := fresh "The_expression_or_parameter_list_must_not_contain_any_loads_but_the_following_subexpression_is_an_implicit_or_explicit_load_Please_refactor_this_stament_of_your_program" 
           in pose (r:=e) 
            end
end.

Ltac no_loads_exprlist e enforce :=
 match e with
 | ?e1::?er => no_loads_expr e1 false enforce; no_loads_exprlist er enforce
 | nil => idtac
 end.

Definition Undo__Then_do__forward_call_W__where_W_is_a_witness_whose_type_is_given_above_the_line_now := False.

Ltac advise_forward_call := 
try eapply semax_seq';
 [match goal with 
  | |- @semax ?Espec ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) (Scall (Some ?id) (Evar ?f _) ?bl) _ =>

      let fsig:=fresh "fsig" in let A := fresh "Witness_Type" in let Pre := fresh "Pre" in let Post := fresh"Post" in
      evar (fsig: funsig); evar (A: Type); evar (Pre: A -> environ->mpred); evar (Post: A -> environ->mpred);
      get_global_fun_def Delta f fsig A Pre Post;
     clear fsig Pre Post;
      assert Undo__Then_do__forward_call_W__where_W_is_a_witness_whose_type_is_given_above_the_line_now
 end
 | .. ].

Ltac forward1 s :=  (* Note: this should match only those commands that
                                     can take a normal_ret_assert *)
  lazymatch s with 
  | Sassign _ _ => new_store_tac
  | Sset _ (Efield ?e _ ?t)  => 
      no_loads_expr e true false;
      first [unify true (match t with Tarray _ _ _ => true | _ => false end);
               forward_setx
              |new_load_tac]
  | Sset _ (Ecast (Efield ?e _ ?t) _) => 
      no_loads_expr e true false;
      first [unify true (match t with Tarray _ _ _ => true | _ => false end);
               forward_setx
              |new_load_tac]
  | Sset _ (Ederef ?e _) => 
         no_loads_expr e true false; new_load_tac
  | Sset _ (Ecast (Ederef ?e _) ?t) => 
         no_loads_expr e true false; 
      first [unify true (match t with Tarray _ _ _ => true | _ => false end);
               forward_setx
              |new_load_tac]
  | Sset _ (Evar _ ?t)  => 
      first [unify true (match t with Tarray _ _ _ => true | _ => false end);
               forward_setx
              |new_load_tac]
  | Sset _ (Ecast (Evar _ _) _) => new_load_tac
  | Sset _ ?e => no_loads_expr e false false; (bool_compute e; forward_ptr_cmp) || forward_setx
  | Sifthenelse ?e _ _ => no_loads_expr e false false; forward_ifthenelse
  | Swhile _ _ => forward_while_complain
  | Sloop (Ssequence (Sifthenelse _ Sskip Sbreak) _) _ => forward_for_complain
  | Ssequence (Scall (Some ?id') (Evar _ _) ?el) (Sset _ (Etempvar ?id' _)) => 
          no_loads_exprlist el false; forward_compound_call
  | Scall _ (Evar _ _) _ =>  advise_forward_call
  | Sskip => forward_skip
  end.

Ltac derives_after_forward :=
             first [ simple apply derives_refl 
                     | simple apply drop_tc_environ
                     | simple apply normal_ret_assert_derives'' 
                     | simple apply normal_ret_assert_derives'
                     | idtac].

Ltac forward_break :=
eapply semax_pre; [ | apply semax_break ];
  unfold_abbrev_ret;
  autorewrite with ret_assert.

Ltac simpl_first_temp :=
try match goal with
| |- semax _ (PROPx _ (LOCALx (temp _ ?v :: _) _)) _ _ =>
  let x := fresh "x" in set (x:=v); 
         simpl in x; unfold x; clear x
| |- (PROPx _ (LOCALx (temp _ ?v :: _) _)) |-- _ =>
  let x := fresh "x" in set (x:=v); 
         simpl in x; unfold x; clear x
end.

Ltac forward_with F1 :=
 match goal with 
(*  | |- semax _ _ (Ssequence (Sset _ ?e) _) _ =>
         no_loads_expr e false true;
         forward_setx_wow_seq*)
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
               simpl_first_temp;
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
               simpl_first_temp;
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
*)

Ltac forward' := forward_with forward1; try unfold repinject.

Ltac fwd_result :=
  unfold replace_nth, repinject; cbv beta;
  first
   [ simple apply extract_exists_pre;
     let v := fresh "v" in intros v;
     autorewrite with subst;
     simpl_first_temp;
     repeat extract_prop_from_LOCAL;
     revert v
   | apply revert_unit
   ].

Ltac fwd' :=
 match goal with
 | |- semax _ _ (Ssequence (Ssequence _ _) _) _ => 
             rewrite <- seq_assoc; fwd'
 | |- semax _ _ (Ssequence ?c _) _ => 
      eapply semax_seq'; [forward1 c | fwd_result]
 | |- semax _ _ ?c _ =>
      rewrite -> semax_seq_skip; 
      eapply semax_seq'; [ forward1 c | fwd_result]
 end.

Ltac fwd_last :=
  try rewrite <- seq_assoc;
  match goal with 
  | |- semax _ _ (Ssequence (Sreturn _) _) _ =>
            apply semax_seq with FF; [ | apply semax_ff];
            forward_return
  | |- semax _ _ (Sreturn _) _ =>  forward_return
  | |- semax _ _ (Ssequence Sbreak _) _ =>
            apply semax_seq with FF; [ | apply semax_ff];
            forward_break
  | |- semax _ _ Sbreak _ => forward_break
  end.

Tactic Notation "forward" :=
  check_Delta;
 repeat simple apply seq_assoc2;
 first
 [ fwd_last
 | fwd_skip
 | fwd';
  [ .. |
  first [intros _ | no_intros ];
   repeat (apply semax_extract_PROP; intro);
   abbreviate_semax;
   try fwd_skip]
 ].

Tactic Notation "forward" simple_intropattern(v1) :=
  check_Delta;
  fwd';
  [ .. 
  | intros v1;
  repeat (apply semax_extract_PROP; intro);
  abbreviate_semax;
  try fwd_skip].

Lemma start_function_aux1:
  forall Espec Delta R1 P Q R c Post,
   @semax Espec Delta (PROPx P (LOCALx Q (SEPx (R1::R)))) c Post ->
   @semax Espec Delta ((PROPx P (LOCALx Q (SEPx R))) * R1) c Post.
Proof.
intros.
rewrite sepcon_comm. rewrite insert_SEP. apply H.
Qed.

Lemma semax_stackframe_emp:
 forall Espec Delta P c R,
 @semax Espec Delta P c R ->
  @semax Espec Delta (P * emp) c (frame_ret_assert R emp) .
Proof. intros. 
            rewrite sepcon_emp;
            rewrite frame_ret_assert_emp;
   auto.
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

Fixpoint quickflow (c: statement) (ok: exitkind->bool) : bool :=
 match c with
 | Sreturn _ => ok EK_return
 | Ssequence c1 c2 => 
     quickflow c1 (fun ek => match ek with
                          | EK_normal => quickflow c2 ok
                          | _ => ok ek
                          end)
 | Sifthenelse e c1 c2 => 
     andb (quickflow c1 ok) (quickflow c2 ok) 
 | Sloop body incr => 
     quickflow body (fun ek => match ek with 
                              | EK_normal => true 
                              | EK_break => ok EK_normal
                              | EK_continue => true
                              | EK_return => ok EK_return
                              end)
 | Sbreak => ok EK_break
 | Scontinue => ok EK_continue
 | Sswitch _ _ => false   (* this could be made more generous *)
 | Slabel _ c => quickflow c ok
 | Sgoto _ => false
 | _ => ok EK_normal
 end.

Definition must_return (ek: exitkind) : bool :=
  match ek with EK_return => true | _ => false end.

Lemma eliminate_extra_return:
  forall Espec Delta P c ty Q Post,
  quickflow c must_return = true ->
  Post = (function_body_ret_assert ty Q) ->
  @semax Espec Delta P c Post ->
  @semax Espec Delta P (Ssequence c (Sreturn None)) Post.
Proof.
intros.
apply semax_seq with FF; [  | apply semax_ff].
replace (overridePost FF Post) with Post; auto.
subst; clear.
extensionality ek vl rho.
unfold overridePost, frame_ret_assert, function_body_ret_assert.
destruct ek; normalize.
Qed.

Lemma eliminate_extra_return':
  forall Espec Delta P c ty Q F Post,
  quickflow c must_return = true ->
  Post = (frame_ret_assert (function_body_ret_assert ty Q) F) ->
  @semax Espec Delta P c Post ->
  @semax Espec Delta P (Ssequence c (Sreturn None)) Post.
Proof.
intros.
apply semax_seq with FF; [  | apply semax_ff].
replace (overridePost FF Post) with Post; auto.
subst; clear.
extensionality ek vl rho.
unfold overridePost, frame_ret_assert, function_body_ret_assert.
destruct ek; normalize.
Qed.

Ltac start_function' :=
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
 repeat match goal with 
 | |- context [Sloop (Ssequence (Sifthenelse ?e Sskip Sbreak) ?s) Sskip] =>
       fold (Swhile e s)
 | |- context [Ssequence ?s1 (Sloop (Ssequence (Sifthenelse ?e Sskip Sbreak) ?s2) ?s3)] =>
      match s3 with
      | Sset ?i _ => match s1 with Sset ?i' _ => unify i i' | Sskip => idtac end
      end;
      fold (Sfor s1 e s2 s3)
 end;
 try expand_main_pre;
 try match goal with |- context [stackframe_of ?F] => 
            change (stackframe_of F) with (@emp (environ->mpred) _ _);
            rewrite frame_ret_assert_emp;
            try rewrite sepcon_emp;  delete_emp_in_SEP
          end;
 try apply start_function_aux1;
 match goal with
  | |- @semax _ _ (PROPx _ _) _ _ => idtac 
  | _ => canonicalize_pre 
 end;
 repeat (apply semax_extract_PROP; intro);
 first [ eapply eliminate_extra_return'; [ reflexivity | reflexivity | ]
        | eapply eliminate_extra_return; [ reflexivity | reflexivity | ]
        | idtac];
 abbreviate_semax.


Ltac start_function := 
 match goal with |- semax_body _ _ _ ?spec =>
          try unfold spec 
 end;
 match goal with
 | |- semax_body _ _ _ (DECLARE _ WITH u : unit
               PRE  [] main_pre _ u
               POST [ tint ] main_post _ u) => idtac
 | |- semax_body _ _ _ ?spec => 
        check_canonical_funspec spec
 end;
 match goal with |- semax_body _ _ _ _ => start_function' 
   | _ => idtac
 end.

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
     |-- (`(numbd n (field_at_ sh (typeof e) fld)) (eval_lvalue e)) * TT);
  [unfold number_list;
   repeat rewrite numbd_lift1; repeat rewrite numbd_lift2;
   gather_entail
  |  ]
end.

Ltac debug_store := (forward0; [debug_store' | ]) || debug_store'.
