Require Import floyd.base2.
Require Import floyd.client_lemmas.
Require Import floyd.go_lower.
Require Import floyd.closed_lemmas.
Require Import floyd.forward_lemmas floyd.call_lemmas.
Require Import floyd.extcall_lemmas.
Require Import floyd.nested_field_lemmas.
Require Import floyd.efield_lemmas.
Require Import floyd.type_induction.
Require Import floyd.mapsto_memory_block.
Require Import floyd.data_at_rec_lemmas.
Require Import floyd.field_at.
Require Import floyd.loadstore_mapsto.
Require Import floyd.loadstore_field_at.
Require Import floyd.nested_loadstore.
Require Import floyd.sc_set_load_store.
Require Import floyd.stronger.
Require Import floyd.local2ptree_denote.
Require Import floyd.local2ptree_eval.
Require Import floyd.reptype_lemmas.
Require Import floyd.proj_reptype_lemmas.
Require Import floyd.replace_refill_reptype_lemmas.
Require Import floyd.aggregate_type.
Require Import floyd.entailer.
Require Import floyd.globals_lemmas.
Require Import floyd.semax_tactics.
Require Import floyd.for_lemmas.
Require Import floyd.diagnosis.
Require Import floyd.simpl_reptype.
Require Import floyd.nested_pred_lemmas.
Import Cop.

(* Done in this tail-recursive style so that "hnf" fully reduces it *)
Fixpoint mk_varspecs' (dl: list (ident * globdef fundef type)) (el: list (ident * type)) :
     list (ident * type) :=
 match dl with
 | (i,Gvar v)::dl' => mk_varspecs' dl' ((i, gvar_info v) :: el)
 | (i, _) :: dl' => mk_varspecs' dl' el
 | nil => rev_append el nil
end.

Definition mk_varspecs prog := mk_varspecs' (prog_defs prog) nil.

Ltac unfold_varspecs al :=
 match al with
 | context [gvar_info ?v] =>
      let b := eval lazy beta zeta iota delta [gvar_info v] in al
      in unfold_varspecs b
 | _ => exact al
 end.

Ltac mk_varspecs prog :=
  let a := constr:(mk_varspecs prog)
   in let a := eval hnf in a
   in unfold_varspecs a.


Hint Resolve field_address_isptr : norm.

Lemma field_address_eq_offset':
 forall {cs: compspecs} t path v ofs,
    field_compatible t path v ->
    ofs = nested_field_offset t path ->
    field_address t path v = offset_val ofs v.
Proof.
intros. subst. apply field_compatible_field_address; auto.
Qed.

Hint Resolve field_address_eq_offset' : prove_it_now.

Hint Rewrite <- @prop_and using solve [auto with typeclass_instances]: norm1.

Local Open Scope logic.


Lemma var_block_lvar2:
 forall {cs: compspecs} {Espec: OracleKind} id t Delta P Q R Vs c Post,
   (var_types Delta) ! id = Some t ->
   legal_alignas_type t = true ->
   legal_cosu_type t = true ->
   complete_type cenv_cs t = true ->
   sizeof t < Int.modulus ->
  (forall v,
   semax Delta ((PROPx P (LOCALx (lvar id t v :: Q) (SEPx (data_at_ Tsh t v :: R))))
                      * fold_right sepcon emp Vs)
               c Post) ->
 semax Delta ((PROPx P (LOCALx Q (SEPx R)))
                      * fold_right sepcon emp (var_block Tsh (id,t) :: Vs))
               c Post.
Proof.
intros.
assert (Int.unsigned Int.zero + sizeof t <= Int.modulus)
 by (rewrite Int.unsigned_zero; omega).
eapply semax_pre_post; [ | intros; apply andp_left2; apply derives_refl | ].
instantiate (1 := EX v:val, (PROPx P (LOCALx (lvar id t v :: Q) (SEPx (data_at_ Tsh t v :: R))))
                      * fold_right sepcon emp Vs).
unfold var_block,  eval_lvar.
go_lowerx. unfold lvar_denote.
normalize.
unfold Map.get.
destruct (ve_of rho id) as [[? ?] | ] eqn:?.
destruct (eqb_type t t0) eqn:?.
apply eqb_type_true in Heqb0.
subst t0.
apply exp_right with (Vptr b Int.zero).
unfold size_compatible.
rewrite prop_true_andp. rewrite TT_andp.
rewrite memory_block_data_at_.
cancel.
split3; auto. apply Coq.Init.Logic.I.
split3; auto.
split3; auto.
split; auto.
red. exists 0. rewrite Z.mul_0_l. apply Int.unsigned_zero.
apply Coq.Init.Logic.I.
split; auto.
rewrite memory_block_isptr; normalize.
rewrite memory_block_isptr; normalize.
apply extract_exists_pre.  apply H4.
Qed.

Lemma lvar_eval_lvar {cs: compspecs}:
  forall i t v rho, locald_denote (lvar i t v) rho -> eval_lvar i t rho = v.
Proof.
unfold eval_lvar; intros. hnf in H.
destruct (Map.get (ve_of rho) i) as [[? ?]|]; try contradiction.
destruct H; subst. rewrite eqb_type_refl; auto.
Qed.

Lemma var_block_lvar0
     : forall {cs: compspecs} (id : positive) (t : type) (Delta : tycontext)  v rho,
       (var_types Delta) ! id = Some t ->
       legal_alignas_type t = true ->
       legal_cosu_type t = true ->
       complete_type cenv_cs t = true ->
       sizeof t < Int.modulus ->
       tc_environ Delta rho ->
       locald_denote (lvar id t v) rho ->
       data_at_ Tsh t v |-- var_block Tsh (id, t) rho.
Proof.
intros.
hnf in H5.
assert (Int.unsigned Int.zero + sizeof t <= Int.modulus)
 by (rewrite Int.unsigned_zero; omega).
unfold var_block.
simpl @fst; simpl @snd.
rewrite prop_true_andp
  by (change (Int.max_unsigned) with (Int.modulus-1); omega).
unfold_lift.
rewrite (lvar_eval_lvar _ _ _ _ H5).
rewrite memory_block_data_at_; auto.
hnf in H5.
destruct ( Map.get (ve_of rho) id); try contradiction.
destruct p.
destruct H5; subst.
repeat split; auto.
exists 0. rewrite Z.mul_0_l. reflexivity.
Qed.

Lemma postcondition_var_block:
  forall {cs: compspecs} {Espec: OracleKind} Delta Pre c S1 S2 i t vbs,
       (var_types  Delta) ! i = Some t ->
       legal_alignas_type t = true ->
       legal_cosu_type t = true ->
       complete_type cenv_cs t = true ->
       sizeof t < Int.modulus ->
   semax Delta Pre c (frame_ret_assert S1
     (S2 *  (EX  v : val, local (locald_denote (lvar i t v)) && `(data_at_ Tsh t v))
      * fold_right sepcon emp vbs)) ->
  semax Delta Pre c (frame_ret_assert S1
     (S2 * fold_right sepcon emp (var_block Tsh (i,t) :: vbs))).
Proof.
intros.
eapply semax_post; [ | eassumption].
intros.
unfold frame_ret_assert.
go_lowerx.
apply sepcon_derives; auto.
rewrite <- !sepcon_assoc.
apply sepcon_derives; auto.
apply sepcon_derives; auto.
apply exp_left; intro v.
normalize.
eapply var_block_lvar0; try apply H; try eassumption.
clear - H5.
destruct ek; simpl in *; auto.
unfold tc_environ in *.
apply expr_lemmas.typecheck_environ_update in H5; auto.
Qed.

Ltac process_stackframe_of :=
 match goal with |- semax _ (_ * stackframe_of ?F) _ _ =>
   let sf := fresh "sf" in set (sf:= stackframe_of F);
     unfold stackframe_of in sf; simpl map in sf; subst sf
  end;
 repeat
   match goal with |- semax _ (_ * fold_right sepcon emp (var_block _ (?i,_) :: _)) _ _ =>
     match goal with
     | n: name i |- _ => simple apply var_block_lvar2;
       [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | clear n; intro n ]
     | |- _ =>    simple apply var_block_lvar2;
       [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | intros ?lvar0 ]
     end
    end;
  match goal with |- semax _ ?Pre _ _ =>
     let p := fresh "p" in set (p := Pre);
     rewrite <- (@emp_sepcon (environ->mpred) _ _ _ (fold_right _ _ _));
     subst p
  end;
  repeat (simple apply postcondition_var_block;
   [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity |  ]);
 change (fold_right sepcon emp (@nil (environ->mpred))) with
   (@emp (environ->mpred) _ _);
 rewrite ?sepcon_emp, ?emp_sepcon.

Definition tc_option_val' (t: type) : option val -> Prop :=
 match t with Tvoid => fun v => match v with None => True | _ => False end | _ => fun v => tc_val t (force_val v) end.
Lemma tc_option_val'_eq: tc_option_val = tc_option_val'.
Proof. extensionality t v. destruct t as [ | | | [ | ] |  | | | | ] eqn:?,v eqn:?; simpl; try reflexivity.
Qed.
Hint Rewrite tc_option_val'_eq : norm.

Lemma emp_make_ext_rval:
  forall ge v, @emp (environ->mpred) _ _ (make_ext_rval ge v) = emp.
Proof. reflexivity. Qed.
Hint Rewrite emp_make_ext_rval : norm2.

Ltac semax_func_cons_ext_tc :=
  repeat match goal with
  | |- (forall x: (?A * ?B), _) =>
      intros [? ?];  match goal with a1:_ , a2:_ |- _ => revert a1 a2 end
  | |- forall x:?T, _ => let t := fresh "t" in set (t:=T); progress simpl in t; subst t
  | |- forall x, _ => intro
  end;
  normalize; simpl tc_option_val' .

(*
Ltac semax_func_skipn :=
  repeat first [apply semax_func_nil'
                     | apply semax_func_skip1;
                       [clear; solve [auto with closed] | ]].
*)

Ltac semax_func_cons L :=
 repeat (apply semax_func_cons_ext_vacuous; [reflexivity | reflexivity | ]);
 first [apply semax_func_cons;
           [ reflexivity
           | repeat apply Forall_cons; try apply Forall_nil; computable
           | unfold var_sizes_ok; repeat constructor | reflexivity | precondition_closed | apply L |
           ]
        | eapply semax_func_cons_ext;
             [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
             | semax_func_cons_ext_tc | apply L |
             ]
        ];
 repeat (apply semax_func_cons_ext_vacuous; [reflexivity | reflexivity | ]);
 try apply semax_func_nil.

(* This is a better way of finding an element in a long list. *)
Lemma from_elements_In : forall {A} l i (v : A), (pTree_from_elements l) ! i = Some v ->
  In (i, v) l.
Proof.
  induction l; simpl; intros.
  - rewrite PTree.gempty in H; discriminate.
  - destruct a as (i', v'); destruct (eq_dec i' i).
    + subst; rewrite PTree.gss in H; inv H; auto.
    + rewrite PTree.gso in H; auto.
Qed.

Lemma typecheck_return_value:
  forall (f: val -> Prop)  (v: val) (gx: genviron) (ret: option val),
 f v -> 
 (PROP ( )
  LOCAL (temp ret_temp v)
  SEP ()) (make_ext_rval gx ret) |-- !! f (force_val ret).
Proof.
intros.
 rewrite <- insert_local.
 rewrite lower_andp.
 apply derives_extract_prop; intro.
 hnf in H0. rewrite retval_ext_rval in H0. rewrite <- H0.
 apply prop_right; auto.
Qed.

Ltac semax_func_cons_ext :=
  eapply semax_func_cons_ext;
    [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
    | semax_func_cons_ext_tc;
      try (apply typecheck_return_value; auto)
    | solve[ first [eapply semax_ext;
          [ (*repeat first [reflexivity | left; reflexivity | right]*) apply from_elements_In; reflexivity
          | apply compute_funspecs_norepeat_e; reflexivity
          | reflexivity
          | reflexivity ]]]
      || fail "Try 'eapply semax_func_cons_ext.'"
              "To solve [semax_external] judgments, do 'eapply semax_ext.'"
              "Make sure that the Espec declared using 'Existing Instance'
               is defined as 'add_funspecs NullExtension.Espec Gprog.'"
    |
    ].

Ltac forward_seq :=
  first [eapply semax_seq'; [  | abbreviate_semax ]
         | eapply semax_post_flipped' ].

(* end of "stuff to move elsewhere" *)

Lemma local_True_right:
 forall (P: environ -> mpred),
   P |-- local (`True).
Proof. intros. intro rho; apply TT_right.
Qed.

Lemma lvar_isptr:
  forall i t v rho, locald_denote (lvar i t v) rho -> isptr v.
Proof.
intros. hnf in H.
destruct (Map.get (ve_of rho) i) as [[? ?]|]; try contradiction.
destruct H; subst; apply Coq.Init.Logic.I.
Qed.

Lemma gvar_isptr:
  forall i v rho, locald_denote (gvar i v) rho -> isptr v.
Proof.
intros. hnf in H.
destruct (Map.get (ve_of rho) i) as [[? ?]|]; try contradiction.
destruct (ge_of rho i); try contradiction.
subst; apply Coq.Init.Logic.I.
Qed.

Lemma sgvar_isptr:
  forall i v rho, locald_denote (sgvar i v) rho -> isptr v.
Proof.
intros. hnf in H.
destruct (ge_of rho i); try contradiction.
subst; apply Coq.Init.Logic.I.
Qed.

Lemma lvar_eval_var:
 forall i t v rho, locald_denote (lvar i t v) rho -> eval_var i t rho = v.
Proof.
intros.
unfold eval_var. hnf in H.
destruct (Map.get (ve_of rho) i) as [[? ?]|]; try contradiction.
destruct H; subst. rewrite eqb_type_refl; auto.
Qed.

Lemma lvar_isptr_eval_var :
 forall i t v rho, locald_denote (lvar i t v) rho -> isptr (eval_var i t rho).
Proof.
intros.
erewrite lvar_eval_var; eauto.
eapply lvar_isptr; eauto.
Qed.

Hint Extern 1 (isptr (eval_var _ _ _)) => (eapply lvar_isptr_eval_var; eassumption) : norm2.


Lemma force_val_sem_cast_neutral_isptr:
  forall v,
  isptr v ->
  Some (force_val (sem_cast_neutral v)) = Some v.
Proof.
intros.
 destruct v; try contradiction; reflexivity.
Qed.

Lemma force_val_sem_cast_neutral_lvar :
  forall i t v rho,
  locald_denote (lvar i t v) rho ->
  Some (force_val (sem_cast_neutral v)) = Some v.
Proof.
intros.
 apply lvar_isptr in H; destruct v; try contradiction; reflexivity.
Qed.

Lemma force_val_sem_cast_neutral_gvar:
  forall i v rho,
  locald_denote (gvar i v) rho ->
  Some (force_val (sem_cast_neutral v)) = Some v.
Proof.
intros.
 apply gvar_isptr in H; destruct v; try contradiction; reflexivity.
Qed.

Lemma force_val_sem_cast_neutral_sgvar:
  forall i v rho,
  locald_denote (sgvar i v) rho ->
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
normalize.
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
 unfold PTree.elements; simpl PTree.xelements;
 go_lower;
 repeat (( simple apply derives_extract_prop
                || simple apply derives_extract_prop');
                fancy_intros true);
 autorewrite with gather_prop;
 repeat (( simple apply derives_extract_prop
                || simple apply derives_extract_prop');
                fancy_intros true);
   repeat erewrite unfold_reptype_elim in * by reflexivity;
   try autorewrite with entailer_rewrite in *;
   repeat first
   [ apply prop_Forall_cons1;
     [unfold check_one_temp_spec, check_one_var_spec;
     simpl; auto;
     normalize;
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
 simpl PTree.get.

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

Ltac change_compspecs' cs cs' :=
  match goal with
  | |- context [?A cs'] => change (A cs') with (A cs)
  | |- context [?A cs' ?B] => change (A cs' B) with (A cs B)
  | |- context [?A cs' ?B ?C] => change (A cs' B C) with (A cs B C)
  | |- context [?A cs' ?B ?C ?D] => change (A cs' B C D) with (A cs B C D)
  | |- context [?A cs' ?B ?C ?D ?E] => change (A cs' B C D E) with (A cs B C D E)
  | |- context [?A cs' ?B ?C ?D ?E ?F] => change (A cs' B C D E F) with (A cs B C D E F)
 end.

Ltac change_compspecs cs :=
 match goal with |- context [?cs'] =>
   match type of cs' with compspecs =>
     try (constr_eq cs cs'; fail 1);
     change_compspecs' cs cs';
     repeat change_compspecs' cs cs'
   end
end.


Definition Warning_perhaps_funspec_postcondition_needs_EX_outside_PROP_LOCAL_SEP (p: Prop) := p.
Ltac give_EX_warning :=
     match goal with |- ?A => change
                 (Warning_perhaps_funspec_postcondition_needs_EX_outside_PROP_LOCAL_SEP A)
             end.

Ltac check_parameter_types :=
   first [reflexivity | elimtype  Parameter_types_in_funspec_different_from_call_statement].

Ltac check_result_type :=
   first [reflexivity | elimtype  Result_type_in_funspec_different_from_call_statement].

Inductive Cannot_find_function_spec_in_Delta (id: ident) := .
Inductive Global_function_name_shadowed_by_local_variable := .

Ltac check_function_name :=
   first [reflexivity | elimtype Global_function_name_shadowed_by_local_variable].

Inductive Actual_parameters_cannot_be_coerced_to_formal_parameter_types := .

Ltac check_cast_params :=
   first [reflexivity | elimtype Actual_parameters_cannot_be_coerced_to_formal_parameter_types].

Inductive Witness_type_of_forward_call_does_not_match_witness_type_of_funspec:
    Type -> Type -> Prop := .

Ltac find_spec_in_globals' :=
   match goal with |- ?X = _ => let x := fresh "x" in set (x:=X); hnf in x; subst x end;
   try reflexivity.

Inductive Cannot_analyze_LOCAL_definitions : Prop := .

Ltac check_prove_local2ptree :=
   first [prove_local2ptree | elimtype Cannot_analyze_LOCAL_definitions].

Inductive Funspec_precondition_is_not_in_PROP_LOCAL_SEP_form := .

Ltac check_funspec_precondition :=
   first [reflexivity | elimtype  Funspec_precondition_is_not_in_PROP_LOCAL_SEP_form].

Ltac lookup_spec_and_change_compspecs CS id :=
 tryif apply f_equal_Some
 then
   (match goal with |- ?A = ?B =>
      let x := fresh "x" in set (x := A);
      let y := fresh "y" in set (y := B);
      hnf in x; subst x; try change_compspecs CS; subst y
   end;
   match goal with
   | |- ?fs = _ => check_canonical_funspec (id,fs);
      first [reflexivity |
      match goal with
       | |- mk_funspec _ _ ?t1 _ _ = mk_funspec _ _ ?t2 _ _ =>
         first [unify t1 t2
           | elimtype False; elimtype (Witness_type_of_forward_call_does_not_match_witness_type_of_funspec
      t2 t1)]
      end]
   end)
 else elimtype  (Cannot_find_function_spec_in_Delta id).

Inductive Function_arguments_include_a_memory_load_of_type (t:type) := .

Ltac goal_has_evars :=
 match goal with |- ?A => has_evar A end.

Ltac check_typecheck :=
 first [goal_has_evars; idtac |
 try apply local_True_right;
 entailer!;
 match goal with
 | |- typecheck_error (deref_byvalue ?T) =>
       elimtype (Function_arguments_include_a_memory_load_of_type T)
 | |- _ => idtac
 end].

Ltac prove_delete_temp := match goal with |- ?A = _ =>
  let Q := fresh "Q" in set (Q:=A); hnf in Q; subst Q; reflexivity
end.

Ltac cancel_for_forward_call := cancel.
Ltac default_cancel_for_forward_call := cancel.

Ltac unfold_post := match goal with |- ?Post = _ => let A := fresh "A" in let B := fresh "B" in first
  [evar (A : Type); evar (B : A -> environ -> mpred); unify Post (@exp _ _ ?A ?B);
     change Post with (@exp _ _ A B); subst A B |
   evar (A : list Prop); evar (B : environ -> mpred); unify Post (PROPx ?A ?B);
     change Post with (PROPx A B); subst A B | idtac] end.


Lemma PROP_LOCAL_SEP_ext :
  forall P P' Q Q' R R', P=P' -> Q=Q' -> R=R' -> 
     PROPx P (LOCALx Q (SEPx R)) = PROPx P' (LOCALx Q' (SEPx R')).
Proof.
intros; subst; auto.
Qed.

Ltac match_postcondition := 
cbv beta iota zeta; unfold_post;  extensionality rho; 
   repeat rewrite exp_uncurry;
   try rewrite no_post_exists; repeat rewrite exp_unfold;
tryif apply exp_congr
 then (intros ?vret;
          apply equal_f; 
          apply PROP_LOCAL_SEP_ext; [reflexivity | | reflexivity];
          (reflexivity || fail "The funspec of the function has a POSTcondition
that is ill-formed.  The LOCALS part of the postcondition
should be (temp ret_temp ...), but it is not"))
 else fail "The funspec of the function should have a POSTcondition that starts
with an existential, that is,  EX _:_, PROP...LOCAL...SEP".
(*
Ltac match_postcondition := 
cbv beta iota zeta; unfold_post; extensionality rho;
   repeat rewrite exp_uncurry;
   try rewrite no_post_exists; repeat rewrite exp_unfold;
   first [apply exp_congr; intros ?vret; reflexivity
           | give_EX_warning
           ].
*)
Ltac  forward_call_id1_wow := 
let H := fresh in intro H;
eapply (semax_call_id1_wow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H); 
 clear H; 
 lazymatch goal with Frame := _ : list mpred |- _ => try clear Frame end;
 [check_result_type
 |apply Logic.I
 | match_postcondition
 | prove_delete_temp
 | unify_postcondition_exps
 | unfold fold_right_and; repeat rewrite and_True; auto
 ].

Ltac forward_call_id1_x_wow :=
let H := fresh in intro H;
eapply (semax_call_id1_x_wow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H); 
 clear H;
 lazymatch goal with Frame := _ : list mpred |- _ => try clear Frame end;
 [ check_result_type | check_result_type
 | apply Coq.Init.Logic.I | apply Coq.Init.Logic.I | reflexivity
 | (clear; let H := fresh in intro H; inversion H)
 | match_postcondition
 | prove_delete_temp
 | prove_delete_temp
 | unify_postcondition_exps
 | unfold fold_right_and; repeat rewrite and_True; auto
 ].


Ltac forward_call_id1_y_wow :=
let H := fresh in intro H;
eapply (semax_call_id1_y_wow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H); 
 clear H;
 lazymatch goal with Frame := _ : list mpred |- _ => try clear Frame end;
 [ check_result_type | check_result_type
 | apply Coq.Init.Logic.I | apply Coq.Init.Logic.I | reflexivity
 | (clear; let H := fresh in intro H; inversion H)
 | match_postcondition
 | prove_delete_temp
 | prove_delete_temp
 | unify_postcondition_exps
 | unfold fold_right_and; repeat rewrite and_True; auto
 ].

Ltac forward_call_id01_wow :=
let H := fresh in intro H;
eapply (semax_call_id01_wow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H); 
 clear H;
 lazymatch goal with Frame := _ : list mpred |- _ => try clear Frame end;
 [ apply Coq.Init.Logic.I 
 | match_postcondition
 | unify_postcondition_exps
 | unfold fold_right_and; repeat rewrite and_True; auto
 ].

Ltac forward_call_id00_wow  :=
let H := fresh in intro H;
eapply (semax_call_id00_wow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H); 
 clear H;
 lazymatch goal with Frame := _ : list mpred |- _ => try clear Frame end;
 [ check_result_type 
 | cbv beta iota zeta; unfold_post; (* extensionality rho; *)
    repeat rewrite exp_uncurry;
    try rewrite no_post_exists0;
    (* apply equal_f; *)
    apply exp_congr; intros ?vret;
    apply PROP_LOCAL_SEP_ext; [reflexivity | | reflexivity];
    (reflexivity || fail "The funspec of the function has a POSTcondition
that is ill-formed.  The LOCALS part of the postcondition
should be empty, but it is not")
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

Ltac unfold_app :=
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

Ltac fwd_skip :=
 match goal with |- semax _ _ Sskip _ =>
   normalize_postcondition;
   first [eapply semax_pre | eapply semax_pre_simple];
      [ | apply semax_skip]
 end.

Definition BINDER_NAME := tt.
Ltac find_postcond_binder_names :=
  match goal with |- semax ?Delta _ ?c _ =>
     match c with context [Scall _ (Evar ?id _) _] =>
     let x := constr:((glob_specs Delta) ! id) in
     let x' := eval hnf in x in
     match x' with
     | Some (mk_funspec _ _ _ _ (fun _ => exp (fun y1 => exp (fun y2 => exp (fun y3 => exp (fun y4 => _)))))) =>
         let y4' := fresh y4 in  pose (y4' := BINDER_NAME);
         let y3' := fresh y3 in  pose (y3' := BINDER_NAME);
         let y2' := fresh y2 in  pose (y2' := BINDER_NAME);
         let y1' := fresh y1 in  pose (y1' := BINDER_NAME)
     | Some (mk_funspec _ _ _ _ (fun _ => exp (fun y1 => exp (fun y2 => exp (fun y3 => _))))) =>
         let y3' := fresh y3 in  pose (y3' := BINDER_NAME);
         let y2' := fresh y2 in  pose (y2' := BINDER_NAME);
         let y1' := fresh y1 in  pose (y1' := BINDER_NAME)
     | Some (mk_funspec _ _ _ _ (fun _ => exp (fun y1 => exp (fun y2 => _)))) =>
         let y2' := fresh y2 in  pose (y2' := BINDER_NAME);
         let y1' := fresh y1 in  pose (y1' := BINDER_NAME)
     | Some (mk_funspec _ _ _ _ (fun _ => exp (fun y1 => _))) =>
         let y1' := fresh y1 in  pose (y1' := BINDER_NAME)
     | _ => idtac
     end
   end
 end.

Ltac after_forward_call_binders :=
 repeat match goal with
 | r := BINDER_NAME |- _ =>
    clear r; apply extract_exists_pre; intro r
 | |- _ => apply extract_exists_pre; intros ?vret
 end.

Ltac cleanup_no_post_exists :=
 match goal with |-  context[eq_no_post] =>
  let vret := fresh "vret" in let H := fresh in
  apply extract_exists_pre; intro vret;
  apply semax_extract_PROP; intro H;
  change (eq_no_post vret) with (eq vret) in H;
  subst vret
 end
 || unfold eq_no_post.

Ltac after_forward_call :=
    cbv beta iota delta [remove_localdef_temp];
    simpl ident_eq; cbv beta iota zeta;
    repeat match goal with |- context [eq_rec_r ?A ?B ?C] =>
              change (eq_rec_r A B C) with B; cbv beta iota zeta
            end;
    unfold_app;
    try (apply extract_exists_pre; intros _);
    match goal with
        | |- semax _ _ _ _ => idtac
        | |- unit -> semax _ _ _ _ => intros _
    end;
    repeat (apply semax_extract_PROP; intro);
    cleanup_no_post_exists;
    abbreviate_semax;
    try fwd_skip.

Ltac clear_MORE_POST :=
 try match goal with POSTCONDITION := @abbreviate ret_assert _ |- _ =>
        clear POSTCONDITION
      end;
 try match goal with MORE_COMMANDS := @abbreviate statement _ |- _ =>
        clear MORE_COMMANDS
      end.

Inductive Ridiculous: Type := .

Ltac check_witness_type A witness :=
  (unify A (rmaps.ConstType Ridiculous); (* because [is_evar A] doesn't seem to work *)
             elimtype False)
 ||
 let TA := constr:(functors.MixVariantFunctor._functor
     (rmaps.dependent_type_functor_rec nil A) mpred) in
  let TA' := eval cbv 
     [functors.MixVariantFunctor._functor
      functors.MixVariantFunctorGenerator.fpair
      functors.MixVariantFunctorGenerator.fconst
      functors.MixVariantFunctorGenerator.fidentity
      rmaps.dependent_type_functor_rec
      functors.GeneralFunctorGenerator.CovariantBiFunctor_MixVariantFunctor_compose
      functors.CovariantFunctorGenerator.fconst
      functors.CovariantFunctorGenerator.fidentity
      functors.CovariantBiFunctor._functor
      functors.CovariantBiFunctorGenerator.Fpair
      functors.GeneralFunctorGenerator.CovariantFunctor_MixVariantFunctor
      functors.CovariantFunctor._functor
      functors.MixVariantFunctor.fmap
      ] in TA
 in let TA'' := eval simpl in TA'
  in match type of witness with ?T => 
       unify T TA''
      + (fail "Type of witness does not match type required by funspec WITH clause.
Witness value: " witness "
Witness type: " T "
Funspec type: " TA'')
     end.

Ltac prove_call_setup1 :=
match goal with |- @semax ?CS _ ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) ?c _ =>
 lazymatch c with
 | context [Scall _ (Evar ?id ?ty) ?bl] =>
    exploit (call_setup1_i2 CS Delta P Q R id ty bl);
    [check_prove_local2ptree
    | apply can_assume_funcptr2;
      [ check_function_name
      | lookup_spec_and_change_compspecs CS id
      | find_spec_in_globals'
      | reflexivity  (* function-id type in AST matches type in funspec *)
      ]
    | reflexivity  (* function-id type in AST matches type in funspec *)
    |check_typecheck
    |check_typecheck
    |check_cast_params
    |reflexivity
    | ..
    ]
 | context [Scall _ ?a ?bl] =>
 exploit (call_setup1_i CS Delta P Q R a bl);
 [check_prove_local2ptree
 |reflexivity
 |prove_func_ptr
 |check_parameter_types
 |check_typecheck
 |check_typecheck
 |check_cast_params
 |reflexivity
 | ]
 end
end.

Ltac prove_call_setup witness :=
 prove_call_setup1;
 [ .. | 
 match goal with |- call_setup1 _ _ _ _ _ _ _ _ _ _ _ ?A _ _ _ _ _ _ _ -> _ =>
      check_witness_type A witness
 end;
 let H := fresh in
 intro H;
 let Frame := fresh "Frame" in evar (Frame: list mpred);
 exploit (call_setup2_i _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H witness Frame); clear H;
 [ reflexivity
 | check_prove_local2ptree
 | Forall_pTree_from_elements
 | Forall_pTree_from_elements
 | unfold fold_right_sepcon at 1 2; cancel_for_forward_call
 | 
 ]].

Ltac fwd_call' witness :=
lazymatch goal with
| |- semax _ _ (Ssequence (Scall _ _ _) _) _ =>
  eapply semax_seq';
    [prove_call_setup witness;
     clear_Delta_specs; clear_MORE_POST;
     [ .. | 
      lazymatch goal with
      | |- _ -> semax _ _ (Scall (Some _) _ _) _ =>
         forward_call_id1_wow
      | |- call_setup2 _ _ _ _ _ _ _ _ _ ?retty _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> 
                semax _ _ (Scall None _ _) _ =>
        tryif (unify retty Tvoid)
        then forward_call_id00_wow
        else forward_call_id01_wow
     end]
   | after_forward_call ]
| |- semax _ _ (Ssequence (Ssequence (Scall (Some ?ret') _ _)
                                       (Sset _ (Ecast (Etempvar ?ret'2 _) _))) _) _ =>
       unify ret' ret'2;
       eapply semax_seq';
         [prove_call_setup witness;
          clear_Delta_specs; clear_MORE_POST;
             [ .. | forward_call_id1_x_wow ]
         |  after_forward_call ]
| |- semax _ _ (Ssequence (Ssequence (Scall (Some ?ret') _ _)
                                       (Sset _ (Etempvar ?ret'2 _))) _) _ =>
       unify ret' ret'2;
       eapply semax_seq';
         [prove_call_setup witness;
          clear_Delta_specs; clear_MORE_POST;
             [ .. | forward_call_id1_y_wow ]
         |  after_forward_call ]
| |- _ => rewrite <- seq_assoc; fwd_call' witness
end.


Ltac fwd_call witness :=
 try lazymatch goal with
      | |- semax _ _ (Scall _ _ _) _ => rewrite -> semax_seq_skip
      end;
 repeat lazymatch goal with
  | |- semax _ _ (Ssequence (Ssequence (Ssequence _ _) _) _) _ =>
      rewrite <- seq_assoc
 end;
lazymatch goal with |- @semax ?CS _ ?Delta _ (Ssequence ?C _) _ =>
  lazymatch C with context [Scall _ _ _] =>
         fwd_call' witness
    end
end.

Tactic Notation "forward_call" constr(witness) := fwd_call witness.

Lemma seq_assoc2:
  forall (Espec: OracleKind) {cs: compspecs}  Delta P c1 c2 c3 c4 Q,
  semax Delta P (Ssequence (Ssequence c1 c2) (Ssequence c3 c4)) Q ->
  semax Delta P (Ssequence (Ssequence (Ssequence c1 c2) c3) c4) Q.
Proof.
intros.
 rewrite <- seq_assoc. auto.
Qed.

Ltac do_compute_lvalue Delta P Q R e v H :=
  let rho := fresh "rho" in
  assert (ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
    local (`(eq v) (eval_lvalue e))) as H by
  (first [ assumption |
    eapply derives_trans; [| apply msubst_eval_lvalue_eq];
    [apply andp_left2; apply derives_refl'; apply local2ptree_soundness; try assumption;
     let HH := fresh "H" in
     construct_local2ptree Q HH;
     exact HH |
     unfold v;
     simpl;
     cbv beta iota zeta delta [force_val2 force_val1];
     rewrite ?isptr_force_ptr, <- ?offset_val_force_ptr by auto;
     reflexivity]
  ]).

Ltac do_compute_expr Delta P Q R e v H :=
  let rho := fresh "rho" in
  assert (ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
    local (`(eq v) (eval_expr e))) as H by
  (assumption || (
    eapply derives_trans; [| apply msubst_eval_expr_eq];
    [apply andp_left2; apply derives_refl'; apply local2ptree_soundness; try assumption;
     let HH := fresh "H" in
     construct_local2ptree Q HH;
     exact HH |
     unfold v;
     match goal with
     | |- ?E = Some _ => let E' := eval hnf in E in change E with E'
     end;
     match goal with
     | |- Some ?E = Some _ => let E' := eval hnf in E in
       match E' with
       | (match ?E'' with
         | Some _ => _
         | None => Vundef
         end)
         => change E with (force_val E'')
       | (match ?E'' with
         | Vundef => Vundef
         | Vint _ => Vundef
         | Vlong _ => Vundef
         | Vfloat _ => Vundef
         | Vsingle _ => Vundef
         | Vptr _ _ => Vptr _ (Int.add _ (Int.repr ?ofs))
         end)
         => change E with (offset_val ofs E'')
       | _ => change E with E'
       end
     | |- ?NotSome = Some _ => fail 1000 "Please make sure hnf can simplify"
                                         NotSome "to an expression of the form (Some _)"
     end;
     reflexivity]
  )).

(* solve msubst_eval_expr, msubst_eval_lvalue, msubst_eval_LR *)
Ltac solve_msubst_eval :=
     match goal with
     | |- ?E = Some _ => let E' := eval hnf in E in change E with E'
     end;
     match goal with
     | |- Some ?E = Some _ => let E' := eval hnf in E in
       match E' with
       | (match ?E'' with
         | Some _ => _
         | None => Vundef
         end)
         => change E with (force_val E'')
       | (match ?E'' with
         | Vundef => Vundef
         | Vint _ => Vundef
         | Vlong _ => Vundef
         | Vfloat _ => Vundef
         | Vsingle _ => Vundef
         | Vptr _ _ => Vptr _ (Int.add _ (Int.repr ?ofs))
         end)
         => change E with (offset_val ofs E'')
       | _ => change E with E'
       end
     | |- ?NotSome = Some _ => fail 1000 "Please make sure hnf can simplify"
                                         NotSome "to an expression of the form (Some _)"
     end.

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
repeat (try rewrite andp_assoc; rewrite insert_local).

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
try rewrite insert_local.

Ltac do_compute_expr_helper Delta Q v :=
   try assumption;
   apply andp_left2;
   eapply derives_trans; [| apply msubst_eval_expr_eq];
    [apply derives_refl'; apply local2ptree_soundness; try assumption;
     let HH := fresh "H" in
     construct_local2ptree Q HH;
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
  evar (Q: A -> list localdef);
  evar (R: A -> list mpred);
  assert (H8: Pre1 =  (fun a => PROPx (P a) (LOCALx (Q a) (SEPx (R a)))))
    by (extensionality; unfold P,Q,R; reflexivity);
  let v := fresh "v" in evar (v: A -> val);
  assert (H9: forall a, ENTAIL Delta, PROPx (P a) (LOCALx (Q a) (SEPx (R a))) |--
                       local (`(eq (v a)) (eval_expr e)))
     by (let a := fresh "a" in intro a; do_compute_expr_helper Delta (Q a) v)
 | PROPx ?P (LOCALx ?Q (SEPx ?R)) =>
  let H9 := fresh "H" in
  let v := fresh "v" in evar (v: val);
  assert (H9:  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R))|--
                     local (`(eq v) (eval_expr e)))
   by (do_compute_expr_helper Delta Q v)
 end.

Lemma typed_true_nullptr3:
  forall p,
  typed_true tint (force_val (sem_cmp_pp Ceq p nullval)) ->
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
  typed_false tint (force_val (sem_cmp_pp Ceq p nullval)) ->
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
  typed_true tint (force_val (sem_cmp_pp Cne p nullval)) ->
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
  typed_false tint (force_val (sem_cmp_pp Cne p nullval)) ->
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
rewrite ?mul_repr, ?add_repr, ?sub_repr in H;
match type of H with
 | _ (Int.signed (Int.repr ?A)) (Int.signed (Int.repr ?B)) =>
    try (rewrite (Int.signed_repr A) in H by repable_signed);
    try (rewrite (Int.signed_repr B) in H by repable_signed)
 | _ (Int.unsigned (Int.repr ?A)) (Int.unsigned (Int.repr ?B)) =>
    try (rewrite (Int.unsigned_repr A) in H by repable_signed);
    try (rewrite (Int.unsigned_repr B) in H by repable_signed)
 | context [Int.signed (Int.repr ?A) ] =>
    try (rewrite (Int.signed_repr A) in H by repable_signed)
 | context [Int.unsigned (Int.repr ?A) ] =>
    try (rewrite (Int.unsigned_repr A) in H by repable_signed)
end.

Lemma typed_true_ptr_e:
 forall t v, typed_true (tptr t) v -> isptr v.
Proof.
 intros. destruct v; inv H; try apply Coq.Init.Logic.I.
 destruct (Int.eq i Int.zero); inv H1.
Qed.

Lemma typed_false_ptr_e:
 forall t v, typed_false (tptr t) v -> v=nullval.
Proof.
 intros. destruct v; inv H; try apply Coq.Init.Logic.I.
 destruct (Int.eq i Int.zero) eqn:?; inv H1.
apply int_eq_e in Heqb. subst; reflexivity.
Qed.

Ltac do_repr_inj H :=
   simpl typeof in H;
  try first [apply typed_true_of_bool in H
               |apply typed_false_of_bool in H
               | apply typed_true_ptr in H
               | apply typed_false_ptr_e in H
               | unfold nullval in H; simple apply typed_true_tint_Vint in H
               | unfold nullval in H; simple apply typed_false_tint_Vint in H
(*               | simple apply typed_true_tint in H *)
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
            | typed_true _  (force_val (sem_cmp_pp Ceq _ _)) =>
                                    apply typed_true_nullptr3 in H
            | typed_true _  (force_val (sem_cmp_pp Cne _ _)) =>
                                    apply typed_true_nullptr4 in H
            | typed_false _  (force_val (sem_cmp_pp Ceq _ _)) =>
                                    apply typed_false_nullptr3 in H
            | typed_false _  (force_val (sem_cmp_pp Cne _ _)) =>
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
| |- context [fst (?a,?b) ] => change (fst (a,b)) with a
| |- context [snd (?a,?b) ] => change (snd (a,b)) with b
end.

Definition EXP_NAME := tt.
Definition MARKED_ONE {A} (z: A) := z.
Definition EXP_UNIT := tt.

Ltac special_intros_EX :=
   match goal with
   | z := EXP_UNIT |- _ => clear z; cbv beta; intros _
   | z := EXP_NAME |- _ =>
         intro;
         match goal with a : ?x |- _ =>
             change x with (MARKED_ONE x) in a
         end;
         repeat match goal with
         | w := EXP_NAME, v := EXP_NAME, a: MARKED_ONE _ |- _ =>
           clear v; unfold MARKED_ONE in a;
           destruct a as [a v];
           match type of a with ?x =>
             change x with (MARKED_ONE x) in a
           end
         | v := EXP_NAME, a: MARKED_ONE _ |- _ =>
           clear v; unfold MARKED_ONE in a; rename a into v
         end;
         simpl_fst_snd
   end.

Lemma trivial_exp:
 forall P: environ -> mpred,
 P = exp (fun x: unit => P).
Proof.
intros. apply pred_ext. Exists tt. auto. Intros u; auto.
Qed.

Tactic Notation "forward_while" constr(Inv) :=
  repeat (apply -> seq_assoc; abbreviate_semax);
  lazymatch goal with |- semax _ _ (Ssequence _ _) _ => idtac | _ => apply <- semax_seq_skip end;
  first [ignore (Inv: environ->mpred)
         | fail 1 "Invariant (first argument to forward_while) must have type (environ->mpred)"];
  apply semax_pre with Inv;
    [ unfold_function_derives_right
    | repeat match goal with
       | |- semax _ (exp _) _ _ => fail 1
       | |- semax _ (PROPx _ _) _ _ => fail 1
       | |- semax _ ?Pre _ _ => match Pre with context [ ?F ] => unfold F end
       end;
       match goal with
       | |- semax _ (exp (fun a1 => _)) _ _ =>
             let a := fresh a1 in pose (a := EXP_NAME)
       | |- semax _ (PROPx ?P ?QR) _ _ =>
             let a := fresh "u" in pose (a := EXP_UNIT);
                  rewrite (trivial_exp (PROPx P QR))
       end;
       repeat match goal with |- semax _ (exp (fun a1 => (exp (fun a2 => _)))) _ _ =>
          let a := fresh a2 in pose (a := EXP_NAME);
          rewrite exp_uncurry
      end;
      eapply semax_seq;
      [match goal with |- semax ?Delta ?Pre (Swhile ?e _) _ =>
        (* the following line was before: eapply semax_while_3g1; *)
        match goal with [ |- semax _ (@exp _ _ ?A _) _ _ ] => eapply (@semax_while_3g1 _ _ A) end;
        (* check if we can revert back to the previous version with coq 8.5.
           (as of December 2015 with compcert 2.6 the above fix is still necessary)
           The bug happens when we destruct the existential variable of the loop invariant:

             (* example.c program: *)
             int main(){int i=0; while(i);}

             (* verif_example.v file (+you have to Require Import the example.v file produced by clightgen) *)
             Require Import floyd.proofauto.
             Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
             Local Open Scope logic.

             Lemma body_main : semax_body [] [] f_main
               (DECLARE _main WITH u : unit
                PRE  [] main_pre prog u
                POST [ tint ] main_post prog u).
             start_function.
             forward.
             pose (Inv := (EX b : bool, PROP () LOCAL (temp _i (Vint (Int.repr (if b then 1 else 0)))) SEP ())).
             forward_while Inv. (** FAILS WITH THE FORMER VERSION OF forward_while **)
         *)
        simpl typeof;
       [ reflexivity
       | special_intros_EX
       | (do_compute_expr1 Delta Pre e; eassumption) ||
         fail "The loop invariant is not strong enough to guarantee evaluation of the loop-test expression.
Loop invariant:" Pre
"
Loop test expression:" e
       | special_intros_EX;
         let HRE := fresh "HRE" in apply semax_extract_PROP; intro HRE;
         do_repr_inj HRE;
         repeat (apply semax_extract_PROP; intro);
         normalize in HRE
        ]
       end
       | simpl update_tycon;
         apply extract_exists_pre; special_intros_EX;
         let HRE := fresh "HRE" in apply semax_extract_PROP; intro HRE;
         do_repr_inj HRE;
         repeat (apply semax_extract_PROP; intro);
         normalize in HRE
       ]
    ]; abbreviate_semax; autorewrite with ret_assert.


Inductive Type_of_invariant_in_forward_for_should_be_environ_arrow_mpred_but_is : Type -> Prop := .
Inductive Type_of_bound_in_forward_for_should_be_Z_but_is : Type -> Prop := .

Ltac forward_for_simple_bound n Pre :=
  check_Delta;
 repeat match goal with |-
      semax _ _ (Ssequence (Ssequence (Ssequence _ _) _) _) _ =>
      apply -> seq_assoc; abbreviate_semax
 end;
 first [
    match type of n with
      ?t => first [ unify t Z | elimtype (Type_of_bound_in_forward_for_should_be_Z_but_is t)]
    end;
    match type of Pre with
      ?t => first [unify t (environ -> mpred); fail 1 | elimtype (Type_of_invariant_in_forward_for_should_be_environ_arrow_mpred_but_is t)]
    end
  | simple eapply semax_seq';
    [forward_for_simple_bound' n Pre
    | cbv beta; simpl update_tycon; abbreviate_semax  ]
  | eapply semax_post_flipped';
     [forward_for_simple_bound' n Pre
     | ]
  ].

Ltac forward_for3 Inv PreInc Postcond :=
   apply semax_seq with Postcond;
       [ eapply semax_for_3g1 with (PQR:=PreInc);
        [ reflexivity
        |intro  
        | intro ;
          match goal with |- ENTAIL ?Delta, ?Pre |-- local (`(eq _) (eval_expr ?e)) =>
            do_compute_expr1 Delta Pre e;
            match goal with v := _ : val , H: ENTAIL _ , _ |-- _ |- _ => subst v; apply H end
          end
        | intro; let HRE := fresh in 
            apply semax_extract_PROP; intro HRE; 
            repeat (apply semax_extract_PROP; fancy_intro true);
            do_repr_inj HRE
        | intro; let HRE := fresh in 
            apply semax_extract_PROP; intro HRE; 
            repeat (apply semax_extract_PROP; fancy_intro true);
            do_repr_inj HRE 
        | intro; let HRE := fresh in 
            apply derives_extract_PROP; intro HRE; 
            repeat (apply derives_extract_PROP; fancy_intro true);
            do_repr_inj HRE;
         autorewrite with ret_assert ]        
       | abbreviate_semax;
         repeat (apply semax_extract_PROP; fancy_intro true)
      ].

Fixpoint no_breaks (s: statement) : bool :=
 match s with
 | Sbreak => false
 | Ssequence a b => andb (no_breaks a) (no_breaks b)
 | Sifthenelse _ a b => andb (no_breaks a) (no_breaks b)
 | Sloop _ _ => true (* breaks within the inner loop are OK *)
 | _ => true
 end.

Ltac forward_for2 Inv PreInc :=
 repeat  match goal with P := @abbreviate ret_assert _ |- semax _ _ _ ?P' =>
                         constr_eq P P'; unfold abbreviate in P; subst P
           end;
 match goal with |- semax _ _ (Sloop (Ssequence (Sifthenelse _ Sskip Sbreak) ?body) _) _ =>
   (tryif unify (no_breaks body) true 
          then idtac
      else fail "Since there is a break in the loop body, you need to supply an explicit postcondition using the 3-argument form of forward_for.");
   eapply semax_for_3g2 with (PQR:=PreInc);
        [ reflexivity 
        |intro  
        | intro ;
          match goal with |- ENTAIL ?Delta, ?Pre |-- local (`(eq _) (eval_expr ?e)) =>
            do_compute_expr1 Delta Pre e;
            match goal with v := _ : val , H: ENTAIL _ , _ |-- _ |- _ => subst v; apply H end
          end
        | intro; let HRE := fresh in 
            apply semax_extract_PROP; intro HRE; 
            repeat (apply semax_extract_PROP; fancy_intro true);
            do_repr_inj HRE
        | intro; let HRE := fresh in 
            apply semax_extract_PROP; intro HRE; 
            repeat (apply semax_extract_PROP; fancy_intro true);
            do_repr_inj HRE
        ]    
  end.

Lemma seq_assoc1: 
   forall (Espec: OracleKind) (CS : compspecs) (Delta : tycontext) (P : environ -> mpred)
         (s1 s2 s3 : statement) (R : ret_assert),
       semax Delta P (Ssequence s1 (Ssequence s2 s3)) R ->
       semax Delta P (Ssequence (Ssequence s1 s2) s3) R.
Proof. intros. apply -> seq_assoc; auto. Qed.

Tactic Notation "forward_for" constr(Inv) constr(PreInc) :=
  check_Delta;
  repeat simple apply seq_assoc1;
  lazymatch type of Inv with
  | _ -> environ -> mpred => idtac
  | _ => fail "Invariant (first argument to forward_for) must have type (_ -> environ -> mpred)"
  end;
  lazymatch type of PreInc with
  | _ -> environ -> mpred => idtac
  | _ => fail "PreInc (second argument to forward_for) must have type (_ -> environ -> mpred)"
  end;
  lazymatch goal with
  | |- semax _ _ (Ssequence (Sfor _ _ _ _) _) _ =>
      apply -> seq_assoc;
      apply semax_seq' with (exp Inv); abbreviate_semax;
      [  | eapply semax_seq; 
         [ forward_for2 Inv PreInc 
          | abbreviate_semax;
            apply extract_exists_pre; intro;
            let HRE := fresh in 
            apply semax_extract_PROP; intro HRE; 
            repeat (apply semax_extract_PROP; fancy_intro true);
            do_repr_inj HRE]
   ]
  | |- semax _ _ (Sfor _ _ _ _) ?Post =>
      apply semax_seq' with (exp Inv); abbreviate_semax;
      [  | forward_for3 Inv PreInc Post]
  | |- semax _ _ (Sloop (Ssequence (Sifthenelse _ Sskip Sbreak) _) _) ?Post =>
     apply semax_pre with (exp Inv);
      [  | forward_for3 Inv PreInc Post]
  | |- semax _ _ (Sloop (Ssequence (Sifthenelse _ Sskip Sbreak) _) _) _ =>
     apply semax_pre with (exp Inv);
      [ unfold_function_derives_right | forward_for2 Inv PreInc ]
  | |- _ => fail "forward_for2x cannot recognize the loop"
  end.

Tactic Notation "forward_for" constr(Inv) constr(PreInc) constr(Postcond) :=
  check_Delta;
  repeat simple apply seq_assoc1;
  lazymatch type of Inv with
  | _ -> environ -> mpred => idtac
  | _ => fail "Invariant (first argument to forward_for) must have type (_ -> environ -> mpred)"
  end;
  lazymatch type of PreInc with
  | _ -> environ -> mpred => idtac
  | _ => fail "PreInc (second argument to forward_for) must have type (_ -> environ -> mpred)"
  end;
  lazymatch type of Postcond with
  | environ -> mpred => idtac
  | _ => fail "Postcond (third argument to forward_for) must have type (environ -> mpred)"
  end;
  lazymatch goal with
  | |- semax _ _ (Ssequence (Sfor _ _ _ _) _) _ =>
      apply -> seq_assoc;
      apply semax_seq' with (exp Inv); abbreviate_semax;
      [  | forward_for3 Inv PreInc Postcond]
  | |- semax _ _ (Sloop (Ssequence (Sifthenelse _ Sskip Sbreak) _) _) _ =>
     apply semax_pre with (exp Inv);
      [ unfold_function_derives_right | forward_for3 Inv PreInc Postcond ]
  end.

Ltac process_cases := 
match goal with
| |- semax _ _ (seq_of_labeled_statement 
     match select_switch_case ?N (LScons (Some ?X) ?C ?SL)
      with Some _ => _ | None => _ end) _ =>
      change (select_switch_case N (LScons (Some X) C SL))
       with (if zeq X N then Some (LScons (Some X) C SL)
                 else select_switch_case N SL);
     let E := fresh "E" in let NE := fresh "NE" in 
     destruct (zeq N X) as [E|NE];
      [ rewrite if_true; [ unfold seq_of_labeled_statement at 1 | symmetry; apply E];
        try subst N
     | rewrite if_false; [ | contradict NE; symmetry; apply NE];
       process_cases
    ]
| |- semax _ _ (seq_of_labeled_statement 
     match select_switch_case ?N (LScons None ?C ?SL)
      with Some _ => _ | None => _ end) _ =>
      change (select_switch_case N (LScons None C SL))
       with (select_switch_case N SL);
     process_cases
| |- semax _ _ (seq_of_labeled_statement 
     match select_switch_case ?N LSnil
      with Some _ => _ | None => _ end) _ =>
      change (select_switch_case N LSnil)
           with (@None labeled_statements);
      cbv iota;
      unfold seq_of_labeled_statement at 1
end.

Ltac forward_switch' := 
match goal with
| |- semax ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) (Sswitch ?e _) _ =>
   let HRE := fresh "H" in let v := fresh "v" in
    evar (v: val);
    do_compute_expr Delta P Q R e v HRE;
    simpl in v;
    let n := fresh "n" in evar (n: int); 
    let H := fresh in assert (H: v=Vint n) by (unfold v,n; reflexivity);
    let A := fresh in 
    match goal with |- ?AA => set (A:=AA) end;
    revert n H; normalize; intros n H; subst A;
    let n' := fresh "n" in pose (n' := Int.unsigned n); 
    let H' := fresh in assert (H': n = Int.repr n');
       [try (symmetry; apply Int.repr_unsigned) 
       | rewrite H,H' in HRE; clear H H';
         subst n' n v; 
         rewrite (Int.repr_unsigned (Int.repr _)) in HRE;
         eapply semax_switch_PQR; 
           [reflexivity | check_typecheck | exact HRE 
           | clear HRE; try omega
           | clear HRE; unfold select_switch at 1; unfold select_switch_default at 1;
             try match goal with H := @abbreviate statement _ |- _ => clear H end;
             process_cases]
]
end.

Ltac forward_if'_new :=
  check_Delta;
match goal with
| |- semax ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) (Sifthenelse ?e ?c1 ?c2) _ =>
   let HRE := fresh "H" in let v := fresh "v" in
    evar (v: val);
    do_compute_expr Delta P Q R e v HRE;
    simpl in v;
    apply (semax_ifthenelse_PQR' _ v);
     [ reflexivity | entailer | assumption
     | clear HRE; subst v; apply semax_extract_PROP; intro HRE;
       do_repr_inj HRE;
       repeat (apply semax_extract_PROP; intro);
       try rewrite Int.signed_repr in HRE by repable_signed;
       abbreviate_semax
     | clear HRE; subst v; apply semax_extract_PROP; intro HRE;
       do_repr_inj HRE;
       repeat (apply semax_extract_PROP; intro);
       try rewrite Int.signed_repr in HRE by repable_signed;
       abbreviate_semax
     ]
| |- semax _ _ (Sswitch _ _) _ =>
  forward_switch'
end.

Ltac forward_if_tac post :=
  check_Delta;
  repeat (apply -> seq_assoc; abbreviate_semax);
first [ignore (post: environ->mpred)
      | fail 1 "Invariant (first argument to forward_if) must have type (environ->mpred)"];
match goal with
 | |- semax _ _ (Sifthenelse _ _ _) (overridePost post _) =>
       forward_if'_new
 | |- semax _ _ (Sswitch _ _) _ =>
       forward_switch'
 | |- semax _ _ (Sifthenelse _ _ _) ?P =>
      apply (semax_post_flipped (overridePost post P));
      [ forward_if'_new
      | try solve [normalize]
      ]
   | |- semax _ _ (Ssequence (Sifthenelse _ _ _) _) _ =>
     apply semax_seq with post;
      [forward_if'_new | abbreviate_semax; autorewrite with ret_assert]
   | |- semax _ _ (Ssequence (Sswitch _ _) _) _ =>
     apply semax_seq with post;
      [forward_switch' | abbreviate_semax; autorewrite with ret_assert]
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
  floyd.seplog_tactics.normalize;
  repeat
  (first [ simpl_tc_expr
         | simple apply semax_extract_PROP; fancy_intros true
         | extract_prop_from_LOCAL
         | move_from_SEP
         ]; cbv beta; msl.log_normalize.normalize)
  | |- _  =>
    floyd.seplog_tactics.normalize
  end.

Ltac renormalize :=
  progress (autorewrite with subst norm1 norm2); normalize;
 repeat (progress (autorewrite with subst norm1 norm2); normalize).

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

Ltac ensure_normal_ret_assert :=
 match goal with
 | |- semax _ _ _ (normal_ret_assert _) => idtac
 | |- semax _ _ _ _ => apply sequential
 end.

Lemma sequential': forall Espec {cs: compspecs} Delta Pre c R Post,
  @semax cs Espec Delta Pre c (normal_ret_assert R) ->
  @semax cs Espec Delta Pre c (overridePost R Post).
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

Ltac get_global_fun_def Delta f fsig cc A Pre Post :=
    let VT := fresh "VT" in let GT := fresh "GT" in
      assert (VT: (var_types Delta) ! f = None) by
               (reflexivity || fail 1 "Variable " f " is not a function, it is an addressable local variable");
      assert (GT: (glob_specs Delta) ! f = Some (mk_funspec fsig cc A Pre Post))
                    by ((unfold fsig, Pre, Post; try unfold A; simpl; reflexivity) ||
                          fail 1 "Function " f " has no specification in the type context");
     clear VT GT.

Definition This_is_a_warning := tt.

Inductive Warning: unit -> unit -> Prop :=
    ack : forall s s', Warning s s'.
Definition IGNORE_THIS_WARNING_USING_THE_ack_TACTIC_IF_YOU_WISH := tt.

Ltac ack := apply ack.

Ltac assert_ P :=
  let H := fresh in assert (H: P); [ | clear H].

Ltac warn s :=
   assert_ (Warning s
               IGNORE_THIS_WARNING_USING_THE_ack_TACTIC_IF_YOU_WISH).


Lemma semax_post3:
  forall R' Espec {cs: compspecs} Delta P c R,
    local (tc_environ (update_tycon Delta c)) && R' |-- R ->
    @semax cs Espec Delta P c (normal_ret_assert R') ->
    @semax cs Espec Delta P c (normal_ret_assert R) .
Proof.
 intros. eapply semax_post; [ | apply H0].
 intros. unfold local,lift1, normal_ret_assert.
 intro rho; normalize. renormalize.
 eapply derives_trans; [ | apply H].
 simpl; apply andp_right; auto. apply prop_right; auto.
Qed.

Lemma semax_post_flipped3:
  forall R' Espec {cs: compspecs} Delta P c R,
    @semax cs Espec Delta P c (normal_ret_assert R') ->
    local (tc_environ (update_tycon Delta c)) && R' |-- R ->
    @semax cs Espec Delta P c (normal_ret_assert R) .
Proof.
intros; eapply semax_post3; eauto.
Qed.

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
(*Hint Rewrite subst_make_args1 : norm2.*)
(*Hint Rewrite subst_make_args1 : subst.*)

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

(* move these two elsewhere, perhaps entailer.v *)
Hint Extern 1 (@sizeof _ ?A > 0) =>
   (let a := fresh in set (a:= sizeof A); hnf in a; subst a; computable)
  : valid_pointer.
Hint Resolve denote_tc_test_eq_split : valid_pointer.

Ltac pre_entailer :=
  try match goal with
  | H := @abbreviate statement _ |- _ => clear H
  end;
  try match goal with
  | H := @abbreviate ret_assert _ |- _ => clear H
  end.

Ltac forward_setx :=
  ensure_normal_ret_assert;
  hoist_later_in_pre;
 match goal with
 | |- semax ?Delta (|> (PROPx ?P (LOCALx ?Q (SEPx ?R)))) (Sset _ ?e) _ =>
        eapply semax_PTree_set;
        [ reflexivity
        | reflexivity
        | reflexivity
        | solve_msubst_eval; reflexivity
        | first [ quick_typecheck3
                | pre_entailer; try solve [entailer!]]
        ]
(*                
        
     let v := fresh "v" in evar (v : val);
     let HRE := fresh "H" in
     do_compute_expr Delta P Q R e v HRE;
     eapply semax_SC_set;
      [ reflexivity
      | reflexivity
      | exact HRE
      | first [quick_typecheck3
            | pre_entailer; clear HRE; subst v; try solve [entailer!]]
      ]
*)
 end.

(* BEGIN new semax_load and semax_store tactics *************************)

Ltac construct_nested_efield e e1 efs tts lr :=
  let pp := fresh "pp" in
    pose (compute_nested_efield e) as pp;
    simpl in pp;
    pose (fst (fst (fst pp))) as e1;
    pose (snd (fst (fst pp))) as efs;
    pose (snd (fst pp)) as tts;
    pose (snd pp) as lr;
    simpl in e1, efs, tts, lr;
    change e with (nested_efield e1 efs tts);
    clear pp.

Lemma efield_denote_cons_array: forall {cs: compspecs} P efs gfs ei i,
  P |-- local (efield_denote efs gfs) ->
  P |-- local (`(eq (Vint (Int.repr i))) (eval_expr ei)) ->
  is_int_type (typeof ei) = true ->
  P |-- local (efield_denote (eArraySubsc ei :: efs) (ArraySubsc i :: gfs)).
Proof.
  intros.
  rewrite (add_andp _ _ H), (add_andp _ _ H0), andp_assoc.
  apply andp_left2.
  intros rho; simpl; unfold local, lift1; unfold_lift; normalize.
  constructor; auto.
  constructor; auto.
Qed.

Lemma efield_denote_cons_struct: forall {cs: compspecs} P efs gfs i,
  P |-- local (efield_denote efs gfs) ->
  P |-- local (efield_denote (eStructField i :: efs) (StructField i :: gfs)).
Proof.
  intros.
  eapply derives_trans; [exact H |].
  intros rho; simpl; unfold local, lift1; unfold_lift; normalize.
  constructor; auto.
Qed.

Lemma efield_denote_cons_union: forall {cs: compspecs} P efs gfs i,
  P |-- local (efield_denote efs gfs) ->
  P |-- local (efield_denote (eUnionField i :: efs) (UnionField i :: gfs)).
Proof.
  intros.
  eapply derives_trans; [exact H |].
  intros rho; simpl; unfold local, lift1; unfold_lift; normalize.
  constructor; auto.
Qed.

(* Given gfs, gfs0, and a name for gfs1, instantiate gfs1 s.t. (gfs = gfs1 ++ gfs0).
   Called suffix because these paths are reversed lists. *)
Ltac calc_gfs_suffix gfs gfs0 gfs1 :=
  let len := fresh "len" in
  pose ((length gfs - length gfs0)%nat) as len;
  hnf in len;
  match goal with
  | len := ?len' |- _ =>
    pose (firstn len' gfs) as gfs1
  end;
  clear len;
  unfold gfs in gfs1;
  let gfs1' := (eval_list gfs1) in change gfs1' in (value of gfs1);
  let gfs0' := (eval_list gfs0) in change gfs0' in (value of gfs0);
  change gfs with (gfs1 ++ gfs0) in *.

Ltac find_load_result Hresult t_root gfs0 v gfs1 :=
  let result := fresh "result" in evar (result: val);
  assert (Hresult: JMeq (proj_reptype (nested_field_type t_root gfs0) gfs1 v) result);
  subst result;
  [ (solve_load_rule_evaluation || fail 1000 "solve_load_rule_evaluation' failed")
  | ].

Ltac solve_efield_denote Delta P Q R efs gfs H :=
  evar (gfs : list gfield);
  assert (ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- local (efield_denote efs gfs)) as H;
  [
    unfold efs, gfs;
    match goal with
    | efs := nil |- _ =>
      instantiate (1 := nil);
      intros rho; apply prop_right; constructor
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
          assert (is_int_type (typeof ei) = true) as HB by reflexivity;

          apply (efield_denote_cons_array _ _ _ _ _ H0 HA HB)

        | eStructField ?i =>
          instantiate (1 := StructField i :: gfs0');
          apply efield_denote_cons_struct, H0
        | eUnionField ?i =>
          instantiate (1 := UnionField i :: gfs0');
          apply efield_denote_cons_union, H0
        end
      end
    end
  |].

Lemma sem_add_ptr_int:
 forall {cs: compspecs} v t i,
   isptr v ->
   Cop2.sem_add (tptr t) tint v (Vint (Int.repr i)) = Some (add_ptr_int t v i).
Proof.
intros. destruct v; inv H; reflexivity.
Qed.
Hint Rewrite @sem_add_ptr_int using assumption : norm1.

Arguments field_type i m / .
Arguments nested_field_type {cs} t gfs / .

Ltac really_simplify A :=
  let aa := fresh "aa" in
  pose (aa := A); compute in aa; change A with aa; subst aa.

Lemma eq_rect_r_eq:
  forall (U: Type) (p: U) Q x h,
    @eq_rect_r U p Q x p h = x.
Proof.
 intros.
 unfold eq_rect_r. symmetry; apply eq_rect_eq.
Qed.

Lemma data_equal_congr {cs: compspecs}:
    forall T (v1 v2: reptype T),
   v1 = v2 ->
   data_equal v1 v2.
Proof. intros. subst. intro. reflexivity.
Qed.

Lemma pair_congr: forall (A B: Type) (x x': A) (y y': B),
  x=x' -> y=y' -> (x,y)=(x',y').
Proof.
intros; subst; auto.
Qed.

Ltac simple_value v :=
 match v with
 | Vundef => idtac
 | Vint _ => idtac
 | Vlong _ => idtac
 | Vfloat _ => idtac
 | Vsingle _ => idtac
 | Vptr _ _ => idtac
 | list_repeat (Z.to_nat _) ?v' => simple_value v'
 end.

Lemma cons_congr: forall {A} (a a': A) bl bl',
  a=a' -> bl=bl' -> a::bl = a'::bl'.
Proof.
intros; f_equal; auto.
Qed.

Ltac solve_store_rule_evaluation :=
  repeat match goal with
  | A : _ |- _ => clear A
  | A := _ |- _ => clear A
  end;
  apply data_equal_congr;
  match goal with A := ?gfs : list gfield |- upd_reptype _ _ ?v0 (valinject _ ?v1) = ?B =>
   let rhs := fresh "rhs" in set (rhs := B);
   lazy beta zeta iota delta [reptype reptype_gen] in rhs;
   simpl in rhs;
   let h0 := fresh "h0" in let h1 := fresh "h1" in
   set (h0:=v0); set (h1:=v1);
   remember_indexes gfs;
   let j := fresh "j" in match type of h0 with ?J => set (j := J) in h0 end;
   lazy beta zeta iota delta in j; subst j;
   lazy beta zeta iota delta - [rhs h0 h1 upd_Znth Zlength];
   subst rhs h0 h1;
   subst; apply eq_refl
  end.

Inductive undo_and_first__assert_PROP: Prop -> Prop := .

Ltac default_entailer_for_store_tac := try solve [entailer!].

Ltac entailer_for_store_tac := default_entailer_for_store_tac.

Ltac load_tac :=
 ensure_normal_ret_assert;
 hoist_later_in_pre;
 first [sc_set_load_store.cast_load_tac | sc_set_load_store.load_tac].

Ltac simpl_proj_reptype :=
progress
match goal with |- context [@proj_reptype ?cs ?t ?gfs ?v] =>
  let d := fresh "d" in let Hd := fresh "Hd" in
  remember (@proj_reptype cs t gfs v) as d eqn:Hd;
 unfold proj_reptype, proj_gfield_reptype, unfold_reptype,
   nested_field_type, nested_field_rec in Hd;
 rewrite ?eq_rect_r_eq, <- ?eq_rect_eq in Hd;
 simpl proj_struct in Hd;
 rewrite ?eq_rect_r_eq, <- ?eq_rect_eq in Hd;
  subst d
end.

Ltac store_tac_without_hint Delta P Q R gfs e_root efs tts p_root p_full sh t_SEP
                           gfs0 gfs1 v n Hroot Hnth H_Denote HRE lr :=
  tryif
    sc_new_instantiate P Q R R gfs p_root sh t_SEP gfs0 v n (0%nat) Hnth
  then (
    calc_gfs_suffix gfs gfs0 gfs1;
    refine (semax_SC_field_store Delta sh n _ _ _ _ _ _ _ _ efs gfs0 gfs1 gfs tts _ _ _ lr
      _ _ _ _ _ _ Hnth Hroot HRE H_Denote _ _ _ _);
    clear Hnth Hroot HRE H_Denote;
    subst p_root;
    [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
    | auto (* writable share *)
    | solve_store_rule_evaluation
    | subst gfs0 gfs1 efs tts lr n;
      pre_entailer;
      try quick_typecheck3;
      unfold tc_efield; entailer_for_store_tac;
      simpl app; simpl typeof
    | solve_legal_nested_field_in_entailment ]
  ) else (
    let path := fresh "path" in evar (path: list gfield);
    let a := fresh "a" in evar (a: val);
    let eq1 := eval unfold p_root, t_SEP, path, a in (p_root = field_address t_SEP path a) in
    let eq2 := eval unfold p_full, t_SEP, path, a in (p_full = field_address t_SEP path a) in
    fail "Please use assert_PROP to prove an equality of the form" eq1
         "or if this does not hold, prove an equality of the form" eq2
  ).

Ltac store_tac_with_root_path_hint Delta P Q R gfs sh e_full p_full t_SEP
                                   gfs0 gfs1 v n Hnth HRE :=
  let e_root := fresh "e_root" in
  let efs := fresh "efs" in
  let tts := fresh "tts" in
  let lr := fresh "lr" in
  construct_nested_efield e_full e_root efs tts lr;
  let p_root := fresh "p_root" in evar (p_root: val);
  let Hroot := fresh "Hroot" in
  match goal with
  | lr := LLLL |- _ => do_compute_lvalue Delta P Q R e_root p_root Hroot
  | lr := RRRR |- _ => do_compute_expr Delta P Q R e_root p_root Hroot
  end;
  simpl in p_root;

  let H_Denote := fresh "H_Denote" in
  let gfsB := fresh "gfsB" in
  solve_efield_denote Delta P Q R efs gfsB H_Denote;

  let gfsA := fresh "gfsA" in evar (gfsA: list gfield);
  let HNice := fresh "HNice" in
  let p_SEP := fresh "a" in
  tryif (
    evar (p_SEP: val);
    assert (ENTAIL Delta, PROPx P (LOCALx Q (SEPx R))
            |-- !! (p_root = field_address t_SEP gfsA p_SEP)) as HNice
    by (
      subst p_root t_SEP gfsA p_SEP;
      (eassumption || (apply prop_right; (eassumption || reflexivity)))
    )
  ) then (
    unify_var_or_evar gfs (gfsB ++ gfsA);
    cbv [app gfsB gfsA] in gfs;
    sc_new_instantiate P Q R R gfs p_SEP sh t_SEP gfs0 v n (0%nat) Hnth;
    calc_gfs_suffix gfs gfs0 gfs1;
    subst p_SEP;
    refine (semax_SC_field_store_with_nested_field_partial
      Delta sh n _ _ _ _ _ _ _ _ _ efs gfs0 gfs1 gfsA gfsB tts _ _ _ lr
      _ _ _ _ _ Hnth Hroot HNice HRE H_Denote _ _ _ _ _);
    clear Hnth Hroot HNice HRE H_Denote;
    [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
    | auto (* writable share *)
    | solve_store_rule_evaluation
    | subst gfs0 gfs1 n;
      pre_entailer;
      try quick_typecheck3;
      unfold tc_efield; entailer_for_store_tac;
      simpl app; simpl typeof
    | solve_legal_nested_field_in_entailment
    | reflexivity ]
  ) else (
    unify_var_or_evar gfs gfsB;
    unify_var_or_evar gfsA (@nil gfield);
    subst gfsB;
    store_tac_without_hint Delta P Q R gfs e_root efs tts p_root p_full sh t_SEP
                           gfs0 gfs1 v n Hroot Hnth H_Denote HRE lr
  );
  try subst e_root; try subst efs; try subst tts; try subst lr; try subst p_root;
  try subst gfsB; try subst gfsA.

Ltac store_tac_with_full_path_hint Delta P Q R gfs e_full p_full sh t_SEP gfs0 gfs1 v n Hfull Hnth HRE :=
  let p_SEP := fresh "a" in
  let HNice := fresh "HNice" in
  tryif (
    evar (p_SEP: val);
    assert (ENTAIL Delta, PROPx P (LOCALx Q (SEPx R))
            |-- !! (p_full = field_address t_SEP gfs p_SEP)) as HNice
    by (
      subst p_full t_SEP gfs p_SEP;
      (eassumption || (apply prop_right; (eassumption || reflexivity)))
    )
  ) then (
    (* if "assert" succeeded, the rest must succeed *)
    sc_new_instantiate P Q R R gfs p_SEP sh t_SEP gfs0 v n (0%nat) Hnth;
    try (unify v (default_val (nested_field_type t_SEP gfs0));
         lazy beta iota zeta delta - [list_repeat Z.to_nat] in v);
    calc_gfs_suffix gfs gfs0 gfs1;
    subst p_SEP;
    refine (semax_SC_field_store_without_nested_efield Delta sh n _ _ _ _ _ _ _ _ _ gfs0 gfs1 _ _ _ _
      _ _ _ _ _ Hnth Hfull HNice HRE _ _ _ _);
    clear Hnth Hfull HNice HRE;
    [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
    | subst sh; auto (* writable share *)
    | solve_store_rule_evaluation
    | subst gfs0 gfs1 sh n;
      pre_entailer;
      try quick_typecheck3; 
      unfold tc_efield; entailer_for_store_tac;
      simpl app; simpl typeof
    | solve_legal_nested_field_in_entailment ]
  ) else (
    store_tac_with_root_path_hint Delta P Q R gfs sh e_full p_full t_SEP gfs0 gfs1 v n Hnth HRE
  ).

Ltac store_tac := 
ensure_open_normal_ret_assert;
hoist_later_in_pre;
match goal with
| |- semax ?Delta (|> (PROPx ?P (LOCALx ?Q (SEPx ?R)))) (Sassign ?e_full ?e2) _ =>
    let HRE := fresh "HRE" in
    let v0 := fresh "v0" in evar (v0: val);
      do_compute_expr Delta P Q R (Ecast e2 (typeof e_full)) v0 HRE;

    let p_full := fresh "p_full" in evar (p_full: val);
    let Hfull := fresh "Hfull" in
    do_compute_lvalue Delta P Q R e_full p_full Hfull;
    simpl in p_full;

    let t_SEP := fresh "t" in evar (t_SEP: type);
    let gfs := fresh "gfs" in evar (gfs: list gfield);
    let sh := fresh "sh" in evar (sh: share);
    let gfs0 := fresh "gfs0" in evar (gfs0: list gfield);
    let gfs1 := fresh "gfs1" in
    let v := fresh "v" in evar (v: reptype (nested_field_type t_SEP gfs0));
    let n := fresh "n" in
    let Hnth := fresh "Hnth" in
    let HNice := fresh "HNice" in

    store_tac_with_full_path_hint Delta P Q R gfs e_full p_full sh t_SEP gfs0 gfs1 v n Hfull Hnth HRE;
    try clear HRE; try clear Hfull; try clear Hnth; try clear HNice;
    try subst v0; try subst p_full; try subst t_SEP; try subst gfs; try subst sh;
    try subst gfs0; try subst gfs1; try subst v; try subst n
end.

(* END new semax_load and semax_store tactics *************************)

Ltac forward0 :=  (* USE FOR DEBUGGING *)
  match goal with
  | |- @semax _ _ _ ?PQR (Ssequence ?c1 ?c2) ?PQR' =>
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

Lemma frame_ret_assert_derives P Q: P |-- Q -> frame_ret_assert P |-- frame_ret_assert Q.
Proof. intros.
 unfold frame_ret_assert. intros ? ? ?. apply sepcon_derives; trivial. apply H. Qed.

Lemma bind_ret_derives t P Q v: P|-- Q -> bind_ret v t P |-- bind_ret v t Q.
Proof. intros. destruct v. simpl; intros. entailer!. apply H.
  destruct t; trivial. simpl; intros. apply H.
Qed.

Lemma function_body_ret_assert_derives t P Q: P |-- Q ->
      function_body_ret_assert t P |-- function_body_ret_assert t Q.
Proof. intros. intros ek v.
  destruct ek; simpl; trivial.
  intros. apply bind_ret_derives; trivial.
Qed.

Ltac forward_return :=
     match goal with |- @semax ?CS _ _ _ _ _ =>
       eapply semax_pre; [  | apply semax_return ];
       try match goal with Post := _ : ret_assert |- _ => subst Post; unfold abbreviate end;
       try change_compspecs CS;
       entailer_for_return
     end.

Ltac test_simple_bound test incr :=
 match incr with
 |   Sset ?i (Ebinop Oadd (Etempvar ?j _) (Econst_int (Int.repr 1) _) _) =>
     constr_eq i j;
     match test with
     | Ebinop Olt (Etempvar ?k _) _ _ =>
       constr_eq i k
    end
 end.
(*
Ltac forward_if_complain :=
           (*semax_logic_and_or
           ||*)  fail 2 "Use this tactic:  forward_if POST, where POST is the post condition".

Ltac forward_while_complain :=
           fail 2 "Use this tactic:  forward_while INV, where INV is the loop invariant".

Ltac forward_for_complain :=
           fail 2 "Use this tactic:  forward_for INV PRE_INCR POST,
      where INV is the loop invariant, PRE_INCR is the invariant at the increment,
      and POST is the postcondition".
*)

Ltac forward_skip := apply semax_skip.

Ltac is_array_type t :=
 let t' := eval hnf in t in
 match t' with Tarray _ _ _ => idtac end.

Ltac no_loads_expr e as_lvalue :=
 match e with
 | Econst_int _ _ => idtac
 | Econst_float _ _ => idtac
 | Econst_single _ _ => idtac
 | Econst_long _ _ => idtac
 | Evar _ ?t => match as_lvalue with true => idtac | false => is_array_type t end
 | Etempvar _ _ => idtac
 | Ederef ?e1 ?t => constr_eq as_lvalue true; no_loads_expr e1 true
 | Eaddrof ?e1 _ => no_loads_expr e1 true
 | Eunop _ ?e1 _ => no_loads_expr e1 as_lvalue
 | Ebinop _ ?e1 ?e2 _ => no_loads_expr e1 as_lvalue ; no_loads_expr e2 as_lvalue
 | Ecast ?e1 _ => no_loads_expr e1 as_lvalue
 | Efield ?e1 _ ?t => match as_lvalue with true => idtac | false => is_array_type t end;
                               no_loads_expr e1 true 
 | Esizeof _ _ => idtac
 | Ealignof _ _ => idtac
end.

Definition Undo__Then_do__forward_call_W__where_W_is_a_witness_whose_type_is_given_above_the_line_now := False.

Ltac advise_forward_call :=
try eapply semax_seq';
 [match goal with
  | |- @semax _ ?Espec ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) (Scall (Some ?id) (Evar ?f _) ?bl) _ =>

      let fsig:=fresh "fsig" in let cc := fresh "cc" in let A := fresh "Witness_Type" in let Pre := fresh "Pre" in let Post := fresh"Post" in
      evar (fsig: funsig); evar (cc: calling_convention); evar (A: Type); evar (Pre: A -> environ->mpred); evar (Post: A -> environ->mpred);
      get_global_fun_def Delta f fsig cc A Pre Post;
     clear fsig cc Pre Post;
      assert Undo__Then_do__forward_call_W__where_W_is_a_witness_whose_type_is_given_above_the_line_now
 end
 | .. ].

Ltac advise_prepare_postcondition := 
 match goal with
 | Post' := @abbreviate ret_assert ?R |- semax _ _ _ ?Post =>
     tryif (constr_eq Post' Post) then (unfold abbreviate in Post'; subst Post') else idtac
 end;
 lazymatch goal with
 | Delta' := @abbreviate tycontext _ |- semax ?Delta _ _ _ =>
     tryif (constr_eq Delta' Delta)
       then idtac
       else fail "Please use abbreviate_semax to put your proof goal into standard form" 
(*  | Delta' := @abbreviate tycontext _ |- semax ?Delta _ _ _ => idtac *)
 | |- semax _ _ _ _ => fail "Please use abbreviate_semax to put your proof goal into standard form."
 | |- _ => fail "Proof goal is not (semax _ _ _ _)."
 end;
 repeat match goal with
 | MC := @abbreviate statement _ |- _ => subst MC; unfold abbreviate
 | |- _ => simple apply seq_assoc1
 end;
 try simple eapply semax_seq.

Ltac forward_advise_for :=
 lazymatch goal with
 | |- semax _ _ (Sfor _ _ ?body Sskip) ?R =>
       tryif unify (no_breaks body) true
       then fail "Use [forward_while Inv] to prove this loop, where Inv is a loop invariant of type (environ->mpred)"
       else tryif has_evar R
            then fail "Use [forward_for Inv Inv Post] to prove this loop, where Inv is a loop invariant of type (A -> environ -> mpred), and Post is a loop-postcondition. A is the type of whatever loop-varying quantity you have, such as the value of your loop iteration variable.  You can use the same Inv twice, before and after the for-loop-increment statement, because your for-loop-increment statement is trivial"
            else fail "Use [forward_for Inv Inv] to prove this loop, where Inv is a loop invariant of type (A -> environ -> mpred).  A is the type of whatever loop-varying quantity you have, such as your loop iteration variable.  You can use the same Inv twice, before and after the for-loop-increment statement, because your for-loop-increment statement is trivial"
  | |- semax _ _ (Sfor _ ?test ?body ?incr) ?R =>
       tryif has_evar R
       then tryif unify (no_breaks body) true
               then tryif test_simple_bound test incr
                  then fail "You can probably use [forward_for_simple_bound n Inv], provided that the upper bound of your loop can be expressed as a constant value (n:Z), and the loop invariant Inv can be expressed as (EX i:Z, ...).  Note that the Inv need not mention the LOCAL binding of the loop-count variable to the value i, and need not assert the PROP that i<=n; these will be inserted automatically.
Otherwise, you can use the general case:
Use [forward_for Inv PreInc] to prove this loop, where Inv is a loop invariant of type (A -> environ -> mpred), and PreInc is the invariant (of the same type) just before the for-loop-increment statement"
                  else fail "Use [forward_for Inv PreInc] to prove this loop, where Inv is a loop invariant of type (A -> environ -> mpred), and PreInc is the invariant (of the same type) just before the for-loop-increment statement"
               else fail "Use [forward_for Inv PreInc Post] to prove this loop, where Inv is a loop invariant of type (A -> environ -> mpred), PreInc is the invariant (of the same type) just before the for-loop-increment statement, and  Post is a loop-postcondition"
       else tryif test_simple_bound test incr
               then fail "You can probably use [forward_for_simple_bound n Inv], provided that the upper bound of your loop can be expressed as a constant value (n:Z), and the loop invariant Inv can be expressed as (EX i:Z, ...).  Note that the Inv need not mention the LOCAL binding of the loop-count variable to the value i, and need not assert the PROP that i<=n; these will be inserted automatically.
Otherwise, you can use the general case:
Use [forward_for Inv PreInc] to prove this loop, where Inv is a loop invariant of type (A -> environ -> mpred), and PreInc is the invariant (of the same type) for just before the for-loop-increment statement"
               else fail "Use [forward_for Inv PreInc] to prove this loop, where Inv is a loop invariant of type (A -> environ -> mpred), and PreInc is the invariant (of the same type) for just before the for-loop-increment statement"
  end.

Ltac forward_advise_if := 
  advise_prepare_postcondition;
 lazymatch goal with
   | |- semax _ _ (Sifthenelse _ _ _) ?R =>
       tryif has_evar R
       then fail "Use [forward_if Post] to prove this if-statement, where Post is the postcondition of both branches"
       else fail "Use [forward_if] to prove this if-statement; you don't need to supply a postcondition"
  end.

Ltac forward_advise_while := 
  advise_prepare_postcondition;
 lazymatch goal with
   | |- semax _ _ (Swhile _ _) _ =>
       fail "Use [forward_while Inv] to prove this loop, where Inv is the loop invariant"
  end.

Ltac forward_advise_call :=
 lazymatch goal with
   | |- semax ?Delta _ (Scall _ (Evar ?f _) ?bl) _ =>
      let fsig:=fresh "fsig" in let cc := fresh "cc" in let A := fresh "Witness_Type" in let Pre := fresh "Pre" in let Post := fresh"Post" in
      evar (fsig: funsig); evar (cc: calling_convention); evar (A: Type); evar (Pre: A -> environ->mpred); evar (Post: A -> environ->mpred);
      get_global_fun_def Delta f fsig cc A Pre Post;
      clear fsig cc Pre Post;
      assert Undo__Then_do__forward_call_W__where_W_is_a_witness_whose_type_is_given_above_the_line_now
end.

Ltac forward1 s :=  (* Note: this should match only those commands that
                                     can take a normal_ret_assert *)
    lazymatch s with
  | Sassign _ _ => clear_Delta_specs; store_tac
  | Sset _ ?e => clear_Delta_specs;
    first [no_loads_expr e false; forward_setx | load_tac]
  | Sifthenelse ?e _ _ => forward_advise_if
  | Swhile _ _ => forward_advise_while
  | Sfor _ _ _ _ => forward_advise_for
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

Ltac fwd_result :=
  repeat
   (let P := fresh "P" in
    match goal with
    | |- context[remove_localdef_temp ?A ?B] =>
         set (P := remove_localdef_temp A B);
         hnf in P;
         subst P
    end);
  unfold replace_nth, repinject; cbv beta iota zeta;
  repeat simpl_proj_reptype.

Ltac check_precondition :=
  lazymatch goal with
  | |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ => 
    lazymatch R with context [sepcon _ _] =>
        fail "The SEP clause of the precondition contains * (separating conjunction).
You must flatten the SEP clause, e.g. by doing [Intros],
or else hide the * by making a Definition or using a freezer"
       | _ => idtac
    end
  | |- _ => fail "Your precondition is not in canonical form (PROP (..) LOCAL (..) SEP (..))"
 end.

Ltac forward :=
  check_Delta;
  repeat rewrite <- seq_assoc;
  lazymatch goal with 
  | |- semax _ _ (Ssequence (Sreturn _) _) _ =>
    apply semax_seq with FF; [ | apply semax_ff];
    clear_Delta_specs; forward_return
  | |- semax _ _ (Sreturn _) _ =>  clear_Delta_specs; forward_return
  | |- semax _ _ (Ssequence Sbreak _) _ =>
    apply semax_seq with FF; [ | apply semax_ff];
    forward_break
  | |- semax _ _ Sbreak _ => forward_break
  | |- semax _ _ Sskip _ => fwd_skip
  | |- semax _ _ ?c0 _ =>
    match c0 with
    | Ssequence _ _ => idtac
    | _ => rewrite -> semax_seq_skip
    end;
    match goal with
    | |- semax _ _ (Ssequence ?c _) _ =>
      check_precondition;
      eapply semax_seq';
      [ forward1 c
      | fwd_result;
        Intros;
        abbreviate_semax;
        try fwd_skip ]
    end
  end.

Lemma start_function_aux1:
  forall (Espec: OracleKind) {cs: compspecs} Delta R1 P Q R c Post,
   semax Delta (PROPx P (LOCALx Q (SEPx (R1::R)))) c Post ->
   semax Delta ((PROPx P (LOCALx Q (SEPx R))) * `R1) c Post.
Proof.
intros.
rewrite sepcon_comm. rewrite insert_SEP. apply H.
Qed.

Lemma semax_stackframe_emp:
 forall Espec {cs: compspecs} Delta P c R,
 @semax cs Espec Delta P c R ->
  @semax cs Espec Delta (P * emp) c (frame_ret_assert R emp) .
Proof. intros.
            rewrite sepcon_emp;
            rewrite frame_ret_assert_emp;
   auto.
Qed.

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
  forall Espec {cs: compspecs} Delta P c ty Q Post,
  quickflow c must_return = true ->
  Post = (function_body_ret_assert ty Q) ->
  @semax cs Espec Delta P c Post ->
  @semax cs Espec Delta P (Ssequence c (Sreturn None)) Post.
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
  forall Espec {cs: compspecs} Delta P c ty Q F Post,
  quickflow c must_return = true ->
  Post = (frame_ret_assert (function_body_ret_assert ty Q) F) ->
  @semax cs Espec Delta P c Post ->
  @semax cs Espec Delta P (Ssequence c (Sreturn None)) Post.
Proof.
intros.
apply semax_seq with FF; [  | apply semax_ff].
replace (overridePost FF Post) with Post; auto.
subst; clear.
extensionality ek vl rho.
unfold overridePost, frame_ret_assert, function_body_ret_assert.
destruct ek; normalize.
Qed.

Ltac change_mapsto_gvar_to_data_at :=
match goal with |- semax _ (PROPx _ (LOCALx ?L (SEPx ?S))) _ _ =>
  match S with context [mapsto ?sh ?t (offset_val ?off ?g) ?v] =>
   match L with context [gvar _ g] =>
     assert_PROP (headptr (offset_val 0 g));
       [entailer!; apply <- headptr_offset_zero; auto |];
     erewrite (mapsto_data_at'' _ _ _ _ (offset_val _ g));
       [| reflexivity | now auto | assumption | apply JMeq_refl ];
     match goal with H: _ |- _ => clear H end;
     rewrite <- ? data_at_offset_zero
   end
  end
end.

Ltac clear_Delta_specs_if_leaf_function :=
 match goal with DS := @abbreviate (PTree.t funspec) _  |- semax _ _ ?S _ =>
   let S' := eval compute in S in
    match S' with 
    | appcontext [Scall] => idtac
    | _ => clearbody DS
    end
 end.

Ltac type_lists_compatible al bl :=
 match al with
 | Tcons ?a ?al' => match bl with Tcons ?b ?bl' => 
                 unify (classify_cast a b) cast_case_neutral;
                 type_lists_compatible al' bl'
                end
 | Tnil => match bl with Tnil => idtac end
 end.

Ltac function_types_compatible t1 t2 :=
 match t1 with
 | Tfunction ?al1 ?r1 _ =>
  match t2 with Tfunction ?al2 ?r2 _ =>
     type_lists_compatible al1 al2;
     first [unify r1 r2 | unify (classify_cast r1 r2) cast_case_neutral]
 end end.

Ltac start_function :=
 match goal with |- semax_body _ _ ?F ?spec =>
   let D := constr:(type_of_function F) in 
   let S := constr:(type_of_funspec (snd spec)) in
   let D := eval hnf in D in let D := eval simpl in D in 
   let S := eval hnf in S in let S := eval simpl in S in 
   tryif (unify D S) then idtac else
   tryif function_types_compatible D S then idtac else
   (fail "Function signature (param types, return type) from function-body does not match function signature from funspec
Function body: " D "
Function spec: " S)
 end;
 match goal with |- semax_body ?V ?G ?F ?spec =>
    let s := fresh "spec" in
    pose (s:=spec); hnf in s;
    match goal with
    | s :=  (DECLARE _ WITH u : unit
               PRE  [] main_pre _ nil u
               POST [ tint ] main_post _ nil u) |- _ => idtac
    | s := ?spec' |- _ => check_canonical_funspec spec'
   end;
   change (semax_body V G F s); subst s
 end;
 let DependedTypeList := fresh "DependedTypeList" in
 match goal with |- semax_body _ _ _ (pair _ (NDmk_funspec _ _ _ ?Pre _)) =>
   match Pre with
   | (fun x => match x with (a,b) => _ end) => intros Espec DependedTypeList [a b]
   | (fun i => _) => intros Espec DependedTypeList i
   end;
   simpl fn_body; simpl fn_params; simpl fn_return
 end;
 simpl functors.MixVariantFunctor._functor in *;
 simpl rmaps.dependent_type_functor_rec;
 clear DependedTypeList;
 repeat match goal with |- @semax _ _ _ (match ?p with (a,b) => _ end * _) _ _ =>
             destruct p as [a b]
           end;
 simplify_func_tycontext;
 repeat match goal with
 | |- context [Sloop (Ssequence (Sifthenelse ?e Sskip Sbreak) ?s) Sskip] =>
       fold (Swhile e s)
 | |- context [Ssequence ?s1 (Sloop (Ssequence (Sifthenelse ?e Sskip Sbreak) ?s2) ?s3) ] =>
      match s3 with
      | Sset ?i _ => match s1 with Sset ?i' _ => unify i i' | Sskip => idtac end
      end;
      fold (Sfor s1 e s2 s3)
 end;
 try expand_main_pre;
 process_stackframe_of;
 repeat change_mapsto_gvar_to_data_at;  (* should really restrict this to only in main,
                                  but it needs to come after process_stackframe_of *)
 repeat rewrite <- data_at__offset_zero;
 try apply start_function_aux1;
 repeat (apply semax_extract_PROP;
              match goal with
              | |- _ ?sh -> _ =>
                 match type of sh with
                 | share => intros ?SH
                 | Share.t => intros ?SH
                 | _ => intro
                 end
               | |- _ => intro
               end);
 first [ eapply eliminate_extra_return'; [ reflexivity | reflexivity | ]
        | eapply eliminate_extra_return; [ reflexivity | reflexivity | ]
        | idtac];
 abbreviate_semax;
 clear_Delta_specs_if_leaf_function.

Opaque sepcon.
Opaque emp.
Opaque andp.

Arguments overridePost Q R !ek !vl / _ .
Arguments eq_dec A EqDec / a a' .
Arguments EqDec_exitkind !a !a'.

(**** make_compspecs ****)

Fixpoint log_base_two_pos (x:positive) : nat :=
 match x with
 | xI y => S (log_base_two_pos y)
 | xO y => S (log_base_two_pos y)
 | xH => O
 end.

Definition log_base_two (x: Z) : nat :=
match x with Zpos y => log_base_two_pos y | _ => O end.

Ltac make_composite_env env c :=
 match c with
 | nil => refine (  {| cenv_cs := env;
    cenv_consistent := _;
    cenv_legal_alignas := _;
    cenv_legal_fieldlist := _ |})
 | Composite ?id ?su ?m ?a :: ?c' =>
 let t := constr: (PTree.get id env) in
 let t := eval hnf in t in
 constr_eq t (@None composite);
 let cm := constr: (complete_members env m) in
 let cm := eval hnf in cm in
 constr_eq cm true;
 let al := constr:(align_attr a (alignof_composite env m)) in
 let al := eval compute in al in
 let sz := constr:(align (sizeof_composite env su m) al) in
 let sz := eval compute in sz in
 let r := constr:(rank_members env m) in
 let r := eval compute in r in
 let szpos := constr:(Z.le_ge 0 sz (proj1 (Z.geb_le sz 0) (eq_refl _))) in
 let al_two_p := constr:(ex_intro (fun n : nat => al = two_power_nat n) (log_base_two al) (eq_refl _)) in
 let sz_al := constr:(ex_intro (fun z : Z => sz = (z * al)%Z) (sz / al) (eq_refl _)) in
 let c1 := constr:( {| co_su := su;
            co_members := m;
            co_attr := a;
            co_sizeof := sz;
            co_alignof := al;
            co_rank := r;
            co_sizeof_pos := szpos;
            co_alignof_two_p := al_two_p;
            co_sizeof_alignof := sz_al |}) in
 let env' := constr:(PTree.set id c1 env) in
 let env' := eval simpl in env' in
  make_composite_env env' c'
end.

Ltac make_composite_env0 prog :=
let p := constr:(prog_types prog) in
let c := eval hnf in p in
let e := constr:(@PTree.empty composite) in
let e := eval hnf in e in
make_composite_env e c.


Lemma composite_env_consistent_i':
  forall (f: composite -> Prop) (env: composite_env),
   Forall (fun idco => f (snd idco)) (PTree.elements env) ->
   (forall id co, env ! id = Some co -> f co).
Proof.
intros.
pose proof (Forall_ptree_elements_e _ (fun idco : positive * composite => f (snd idco))).
simpl in H1.
eapply H1; eassumption.
Qed.

Lemma composite_env_consistent_i:
  forall (f: composite_env -> composite -> Prop) (env: composite_env),
   Forall (fun idco => f env (snd idco)) (PTree.elements env) ->
   (forall id co, env ! id = Some co -> f env co).
Proof.
intros.
eapply composite_env_consistent_i'; eassumption.
Qed.

Ltac make_compspecs prog :=
 make_composite_env0 prog;
 [now (red; apply (composite_env_consistent_i composite_consistent);
          repeat constructor)
 |now (red; apply (composite_env_consistent_i composite_legal_alignas);
          repeat constructor)
 |now(red; apply (composite_env_consistent_i' composite_legal_fieldlist);
         repeat constructor)
 ].

Fixpoint missing_ids {A} (t: PTree.tree A) (al: list ident) :=
  match al with
  | a::al' => match PTree.get a t with None => a::nil | _ => nil end ++
                 missing_ids t al'
  | nil => nil
 end.

Ltac with_library' p G :=
  let g := eval hnf in G in
  let x := constr:(augment_funspecs' (prog_funct p) g) in
  let x := eval hnf in x in
  match x with
  | Some ?l => exact l
  | None => 
   let t := constr:(List.fold_right (fun i t => PTree.set i tt t) (PTree.empty _)
                           (map fst (prog_funct p))) in
   let t := eval compute in t in
   let missing := constr:(missing_ids t (map fst G)) in
   let missing := eval simpl in missing in
   match missing with
   | nil => fail "Superfluous funspecs?"
   | _ => fail  "The following names have funspecs but no function definitions: " missing
  end
 end.

Ltac with_library prog G := with_library' prog G.

Lemma mk_funspec_congr:
  forall a b c d e f g a' b' c' d' e' f' g',
   a=a' -> b=b' -> c=c' -> JMeq d d' -> JMeq e e' ->
 mk_funspec a b c d e f g = mk_funspec a' b' c' d' e' f' g'.
Proof.
intros.
subst a' b' c'.
apply JMeq_eq in H2.
apply JMeq_eq in H3.
subst d' e'.
f_equal; apply proof_irr.
Qed.
