Require Import floyd.base.
Require Import floyd.client_lemmas.
Require Import floyd.assert_lemmas.
Require Import floyd.closed_lemmas.
Require Import floyd.canonicalize floyd.forward_lemmas floyd.call_lemmas.
Require Import floyd.extcall_lemmas.
Require Import floyd.nested_field_lemmas.
Require Import floyd.efield_lemmas.
Require Import floyd.type_induction.
Require Import floyd.mapsto_memory_block.
Require Import floyd.data_at_lemmas.
Require Import floyd.field_at.
Require Import floyd.loadstore_mapsto.
Require Import floyd.loadstore_field_at.
Require Import floyd.nested_loadstore.
Require Import floyd.sc_set_load_store.
Require Import floyd.stronger.
Require Import floyd.local2ptree.
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

Hint Resolve field_address_isptr : norm.

Lemma field_address_eq_offset:
 forall {cs: compspecs} t path v,
  field_compatible t path v ->
  field_address t path v = offset_val (Int.repr (nested_field_offset2 t path)) v.
Proof.
intros. unfold field_address; rewrite if_true by auto; reflexivity.
Qed.

Lemma field_address_eq_offset':
 forall {cs: compspecs} t path v ofs,
    field_compatible t path v ->
    ofs = Int.repr (nested_field_offset2 t path) ->
    field_address t path v = offset_val ofs v.
Proof.
intros. subst. apply field_address_eq_offset; auto.
Qed.

Hint Resolve field_address_eq_offset' : prove_it_now.

Hint Rewrite <- @prop_and using solve [auto with typeclass_instances]: norm1.

Local Open Scope logic.

Lemma var_block_lvar1:  (* obsolete *)
 forall {cs: compspecs} id t Delta P Q R,
   (var_types Delta) ! id = Some t ->
   legal_alignas_type t = true ->
   legal_cosu_type t = true ->
   complete_type cenv_cs t = true ->
   sizeof cenv_cs t < Int.modulus ->
  PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx (var_block Tsh (id,t) :: R))) |--
  EX v:val, PROPx P (LOCALx (lvar id t v :: Q) (SEPx (`(data_at_ Tsh t v) :: R))).
Proof.
intros.
assert (Int.unsigned Int.zero + sizeof cenv_cs t <= Int.modulus)
 by (rewrite Int.unsigned_zero; omega).
unfold var_block, lvar, eval_lvar.
go_lowerx.
normalize.
unfold Map.get.
destruct (ve_of rho id) as [[? ?] | ] eqn:?.
destruct (eqb_type t t0) eqn:?.
apply eqb_type_true in Heqb0.
subst t0.
apply exp_right with (Vptr b Int.zero).
unfold size_compatible.
rewrite prop_true_andp. rewrite TT_andp.
apply sepcon_derives; auto.
rewrite memory_block_data_at_.
auto.
split3; auto. apply Coq.Init.Logic.I.
split3; auto.
split3; auto.
split; auto.
red. exists 0. rewrite Z.mul_0_l. apply Int.unsigned_zero.
apply Coq.Init.Logic.I.
split; auto.
rewrite memory_block_isptr; normalize.
rewrite memory_block_isptr; normalize.
Qed.

Ltac fixup_local_var := (* obsolete *)
match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
 match R with
 | context [var_block ?i ?t :: ?L] => 
   let n := eval compute in (length R - (S (length L)))%nat
    in rewrite (SEP_nth_isolate n R (var_block i t)) by reflexivity;
        unfold replace_nth;
        eapply semax_pre; [apply var_block_lvar1; now reflexivity 
                 | apply extract_exists_pre; intros ?lvar0 ]
 end
end.

Lemma var_block_lvar2:
 forall {cs: compspecs} {Espec: OracleKind} id t Delta P Q R Vs c Post,
   (var_types Delta) ! id = Some t ->
   legal_alignas_type t = true ->
   legal_cosu_type t = true ->
   complete_type cenv_cs t = true ->
   sizeof cenv_cs t < Int.modulus ->
  (forall v,
   semax Delta ((PROPx P (LOCALx (lvar id t v :: Q) (SEPx (`(data_at_ Tsh t v) :: R)))) 
                      * fold_right sepcon emp Vs)
               c Post) ->
 semax Delta ((PROPx P (LOCALx Q (SEPx R))) 
                      * fold_right sepcon emp (var_block Tsh (id,t) :: Vs))
               c Post.
Proof.
intros.
assert (Int.unsigned Int.zero + sizeof cenv_cs t <= Int.modulus)
 by (rewrite Int.unsigned_zero; omega).
eapply semax_pre_post; [ | intros; apply andp_left2; apply derives_refl | ].
instantiate (1 := EX v:val, (PROPx P (LOCALx (lvar id t v :: Q) (SEPx (`(data_at_ Tsh t v) :: R)))) 
                      * fold_right sepcon emp Vs).
unfold var_block, lvar, eval_lvar.
go_lowerx.
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
  forall i t v rho, lvar i t v rho -> eval_lvar i t rho = v.
Proof.
unfold lvar, eval_lvar; intros.
destruct (Map.get (ve_of rho) i) as [[? ?]|]; try contradiction.
destruct (eqb_type t t0); try contradiction.
destruct H; subst; auto.
Qed.

Lemma var_block_lvar0
     : forall {cs: compspecs} (id : positive) (t : type) (Delta : tycontext)  v rho,
       (var_types Delta) ! id = Some t ->
       legal_alignas_type t = true ->
       legal_cosu_type t = true ->
       complete_type cenv_cs t = true ->
       sizeof cenv_cs t < Int.modulus ->
       tc_environ Delta rho ->
       lvar id t v rho ->
       data_at_ Tsh t v |-- var_block Tsh (id, t) rho.
Proof.
intros.
assert (Int.unsigned Int.zero + sizeof cenv_cs t <= Int.modulus)
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
destruct p. destruct (eqb_type t t0); try contradiction.
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
       sizeof cenv_cs t < Int.modulus ->
   semax Delta Pre c (frame_ret_assert S1 
     (S2 *  (EX  v : val, local (lvar i t v) && `(data_at_ Tsh t v))
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
     rewrite <- (emp_sepcon (fold_right _ _ _)); subst p
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
           | unfold var_sizes_ok; repeat constructor | reflexivity | precondition_closed | apply L | 
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
  repeat fixup_local_var;
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


Lemma local_True_right:
 forall (P: environ -> mpred),
   P |-- local (`True).
Proof. intros. intro rho; apply TT_right.
Qed.

(*
Lemma normalize_lvar {cs: compspecs}:
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
*)

Lemma lvar_isptr {cs: compspecs}:
  forall i t v rho, lvar i t v rho -> isptr v.
Proof.
unfold lvar; intros.
destruct (Map.get (ve_of rho) i) as [[? ?]|]; try contradiction.
destruct (eqb_type t t0); try contradiction.
destruct H; subst; apply Coq.Init.Logic.I.
Qed.

Lemma gvar_isptr:
  forall i v rho, gvar i v rho -> isptr v.
Proof.
unfold gvar; intros.
destruct (Map.get (ve_of rho) i) as [[? ?]|]; try contradiction.
destruct (ge_of rho i); try contradiction.
subst; apply Coq.Init.Logic.I.
Qed.

Lemma sgvar_isptr:
  forall i v rho, sgvar i v rho -> isptr v.
Proof.
unfold sgvar; intros.
destruct (ge_of rho i); try contradiction.
subst; apply Coq.Init.Logic.I.
Qed.

(*
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
*)

Lemma lvar_eval_var {cs: compspecs}:
 forall i t v rho, lvar i t v rho -> eval_var i t rho = v.
Proof.
intros.
unfold eval_var. hnf in H. destruct (Map.get (ve_of rho) i) as [[? ?]|]; try inv H.
destruct (eqb_type t t0); try contradiction.
destruct H; auto.
Qed.

Lemma lvar_isptr_eval_var {cs: compspecs}:
 forall i t v rho, lvar i t v rho -> isptr (eval_var i t rho).
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

Lemma force_val_sem_cast_neutral_lvar {cs: compspecs}:
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
                fancy_intros);
 autorewrite with gather_prop;
 repeat (( simple apply derives_extract_prop 
                || simple apply derives_extract_prop');
                fancy_intros);
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

(* 
Ltac Forall_pTree_from_elements :=
   This older version can be much slower, because 
   it calls "ent_iter" instead of just picking the parts
   of ent_iter that it needs.  In particular, it avoids
   saturate_local, which is expensive these days. 
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
*)

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
 | apply Coq.Init.Logic.I | apply Coq.Init.Logic.I | reflexivity 
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
 | apply Coq.Init.Logic.I | apply Coq.Init.Logic.I | reflexivity 
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
 | apply Coq.Init.Logic.I | reflexivity
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
 [ reflexivity | reflexivity | reflexivity | apply Coq.Init.Logic.I | reflexivity
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

Definition In_the_previous_forward_call__use_intropatterns_to_intro_values_of_these_types := Stuck.

Ltac complain_intros :=
 first [let x := fresh "x" in intro x; complain_intros; revert x
         | stuckwith In_the_previous_forward_call__use_intropatterns_to_intro_values_of_these_types
         ].

Tactic Notation "uniform_intros" simple_intropattern_list(v) :=
 (((assert True by (intros v; apply Coq.Init.Logic.I);
  assert (forall a: unit, True)
   by (intros v; apply Coq.Init.Logic.I);
  fail 1) || intros v) || idtac).

Tactic Notation "forward_call" constr(witness) simple_intropattern_list(v) :=
    check_canonical_call; 
    try  (* BUG IN THIS LINE!  If check_canonical_call succeeds, but the
          rest of the tactic fails, then the whole tactic should fail,
         but the "try" makes it fail.  Can't simply delete the try, 
         in case check_canonical_call returns a diagnostic message.
         Need to handle the diagnostic the proper way *)
      match goal with |- semax _ _ _ _ =>
    check_Delta;
    fwd_call' witness;
  [ .. 
  | first 
      [ (* body of uniform_intros tactic *)
         (((assert True by (intros v; apply Coq.Init.Logic.I);
            assert (forall a: unit, True) by (intros v; apply Coq.Init.Logic.I);
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
  ] end.

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
| |- context [fst (?a,?b) ] => change (fst (a,b)) with a 
| |- context [snd (?a,?b) ] => change (snd (a,b)) with b 
end.

Tactic Notation "forward_while" constr(Inv) :=
  check_Delta;
  repeat (apply -> seq_assoc; abbreviate_semax);
  first [ignore (Inv: bool -> environ->mpred) 
         | fail 1 "Invariant (first argument to forward_while) must have type (bool -> environ->mpred)"];
  apply semax_pre with Inv;
    [  unfold_function_derives_right 
    | eapply semax_seq;
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
        eapply semax_while_3g; 
        simpl typeof;
       [ reflexivity 
       | no_intros || idtac
       | do_compute_expr1 Delta Pre e; eassumption
       | no_intros; simpl_fst_snd; 
         let HRE := fresh "HRE" in apply semax_extract_PROP; intro HRE;
         first [simple apply typed_true_of_bool in HRE
               | apply typed_true_tint_Vint in HRE
               | apply typed_true_tint in HRE
               | idtac ];
         repeat (apply semax_extract_PROP; intro); 
         do_repr_inj HRE; normalize in HRE
        ]
       end
       | simpl update_tycon; 
         apply extract_exists_pre; no_intros; simpl_fst_snd;
         let HRE := fresh "HRE" in apply semax_extract_PROP; intro HRE;
         first [simple apply typed_false_of_bool in HRE
               | apply typed_false_tint_Vint in HRE
               | apply typed_false_tint in HRE
               | idtac ];
         repeat (apply semax_extract_PROP; intro)
       ]
     ]; abbreviate_semax; autorewrite with ret_assert.

Tactic Notation "forward_while" constr(Inv)
     simple_intropattern(pat) :=
  repeat (apply -> seq_assoc; abbreviate_semax);
  first [ignore (Inv: environ->mpred) 
         | fail 1 "Invariant (first argument to forward_while) must have type (environ->mpred)"];
  apply semax_pre with Inv;
    [  unfold_function_derives_right 
    | eapply semax_seq;
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
        (* the following line was before: eapply semax_while_3g1; *)
        match goal with [ |- semax _ (@exp _ _ ?A _) _ _ ] => eapply (@semax_while_3g1 _ _ A) end;
        (* check if we can revert back to the old one with coq 8.5. 
           The bug happens when we destruct the existential variable of the loop invariant:
           
             (* .c program: *)
             int main(){int i=0; while(i);}
             
             (* .v file *)
             Require Import floyd.proofauto.
             Require Import c.
             Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
             Local Open Scope logic.
             
             Lemma body_main : semax_body [] [] f_main 
               (DECLARE _main WITH u : unit
                PRE  [] main_pre prog u
                POST [ tint ] main_post prog u).
             start_function.
             forward.
             pose (Inv := (EX b : bool, PROP () LOCAL (temp _i (Vint (Int.repr (if b then 1 else 0)))) SEP ())).
             forward_while Inv VAR. (** FAILS WITH THE FORMER VERSION OF forward_while **)
         *)
        simpl typeof;
       [ reflexivity 
       | intros pat; simpl_fst_snd
       | do_compute_expr1 Delta Pre e; eassumption
       | intros pat; simpl_fst_snd; 
         let HRE := fresh "HRE" in apply semax_extract_PROP; intro HRE;
         first [simple apply typed_true_of_bool in HRE
               | apply typed_true_tint_Vint in HRE
               | apply typed_true_tint in HRE
               | idtac ];
         repeat (apply semax_extract_PROP; intro); 
         do_repr_inj HRE; normalize in HRE
        ]
       end
       | simpl update_tycon; 
         apply extract_exists_pre; intros pat; simpl_fst_snd;
         let HRE := fresh "HRE" in apply semax_extract_PROP; intro HRE;
         first [simple apply typed_false_of_bool in HRE
               | apply typed_false_tint_Vint in HRE
               | apply typed_false_tint in HRE
               | idtac ];
         repeat (apply semax_extract_PROP; intro)
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
| |- @semax _ _ ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) 
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
    apply (semax_ifthenelse_PQR' _ v);
     [ reflexivity | entailer | assumption 
     | clear HRE; subst v; apply semax_extract_PROP; intro HRE; 
       do_repr_inj HRE; abbreviate_semax
     | clear HRE; subst v; apply semax_extract_PROP; intro HRE; 
       do_repr_inj HRE; abbreviate_semax
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
(*         | simple apply semax_extract_PROP_True; [solve [auto] | ]*)
         | simple apply semax_extract_PROP; fancy_intros
         | extract_prop_from_LOCAL
         | move_from_SEP
         ]; cbv beta; msl.log_normalize.normalize)
  | |- _  => 
    floyd.client_lemmas.normalize
  end.

Ltac renormalize := 
  progress (autorewrite with subst norm1 norm2); normalize;
 repeat (progress (autorewrite with subst norm1 norm2); normalize).

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
 | simpl; first [apply Coq.Init.Logic.I | reflexivity]
 | simpl; simpl_lift; reflexivity
 | quick_typecheck
 ].

Ltac forward_setx_wow_seq :=
eapply forward_setx_wow_seq;
 [ solve [auto 50 with closed]
 | solve [repeat constructor; auto with closed]
 | simpl; first [apply Coq.Init.Logic.I | reflexivity]
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
 forall Espec {cs: compspecs} Delta P Q (F: val -> Prop) (G: mpred) R c Post,
  @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx (`G :: R)))) c Post ->
  @semax cs Espec Delta (PROPx P (LOCALx Q 
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
Hint Rewrite subst_make_args1 : norm2.
Hint Rewrite subst_make_args1 : subst.

Ltac normalize_make_args :=
 cbv beta iota;
 repeat rewrite subst_make_args1;
 let R' := fresh "R" in evar (R': environ->mpred);
   apply focus_make_args with R';
  [norm_rewrite; unfold R'; reflexivity
  | unfold R'; clear R'].

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
                                | solve [subst;cancel]]) ]
          | reflexivity ]
       | eapply forward_ptr_compare'; try reflexivity; auto].

Ltac pre_entailer :=
  try match goal with
  | H := @abbreviate statement _ |- _ => clear H
  end;
  try match goal with
  | H := @abbreviate ret_assert _ |- _ => clear H
  end.

Ltac old_forward_setx :=
first [ ensure_normal_ret_assert;
         hoist_later_in_pre;
         match goal with
         | |- semax ?Delta (|> (PROPx ?P (LOCALx ?Q (SEPx ?R)))) (Sset _ ?e) _ =>
                let v := fresh "v" in evar (v : val);
                let HRE := fresh "H" in
                do_compute_expr Delta P Q R e v HRE;
                eapply semax_SC_set;
                  [reflexivity | reflexivity | exact HRE 
                  | pre_entailer; clear HRE; subst v; try solve [entailer!] ]
         end
(*       | apply forward_setx_closed_now;
            [solve [auto 50 with closed] | solve [auto 50 with closed] | solve [auto 50 with closed]
            | try apply local_True_right
            | try apply local_True_right
            |  ]
        | apply forward_setx; quick_typecheck
*)
        ].

Ltac forward_setx :=
  ensure_normal_ret_assert;
    hoist_later_in_pre;
 match goal with
 | |- semax ?Delta (|> (PROPx ?P (LOCALx ?Q (SEPx ?R)))) (Sset _ ?e) _ =>
     let v := fresh "v" in evar (v : val);
     let HRE := fresh "H" in
     do_compute_expr Delta P Q R e v HRE;
     eapply semax_SC_set1;
      [reflexivity | reflexivity 
      | solve [repeat econstructor]
      | unfold app at 1; reflexivity
      | solve [repeat econstructor]
      | exact HRE
      | pre_entailer; clear HRE; subst v; try solve [entailer!]
      ]
 end.

Ltac forward_setx_with_pcmp e :=
tac_if (ptr_compare e) ltac:forward_ptr_cmp ltac:forward_setx.

(* BEGIN new semax_load and semax_store tactics *************************)

Ltac solve_legal_nested_field_in_entailment :=
   match goal with
   | |- _ |-- !! ?A => try solve [apply prop_right; clear; compute; intuition congruence]
   | |- _ |-- !! legal_nested_field ?t_root (?gfs1 ++ ?gfs0) =>
    unfold t_root, gfs0, gfs1
  end;
  apply compute_legal_nested_field_spec;
  match goal with
  | |- Forall ?F _ =>
      let F0 := fresh "F" in
      remember F as F0;
      simpl;
      subst F0
  end;
  repeat constructor;
  try solve [entailer!].

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

Lemma efield_denote_cons_array: forall {cs: compspecs} P efs gfs ei i,
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
  intro rho. simpl.
  repeat apply andp_right; auto.
  apply prop_right, H1.
Qed.

Lemma efield_denote_cons_struct: forall {cs: compspecs} P efs gfs i,
  P |-- efield_denote efs gfs ->
  P |-- efield_denote (eStructField i :: efs) (StructField i :: gfs).
Proof.
  intros.
  eapply derives_trans; [exact H |].
  simpl; intros; normalize.
Qed.

Lemma efield_denote_cons_union: forall {cs: compspecs} P efs gfs i,
  P |-- efield_denote efs gfs ->
  P |-- efield_denote (eUnionField i :: efs) (UnionField i :: gfs).
Proof.
  intros.
  eapply derives_trans; [exact H |].
  simpl; intros; normalize.
Qed.

Ltac test_legal_nested_efield TY e gfs tts lr  :=
(*  assert (legal_nested_efield TY e gfs tts lr = true) as H_LEGAL by reflexivity. *)
   unify (legal_nested_efield TY e gfs tts lr) true.

Ltac sc_try_instantiate P Q R0 Delta e gfs tts p sh t_root gfs0 v n N H SH GFS TY V:=
      assert (PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx (R0 :: nil))) 
         |-- `(field_at sh t_root gfs0 v p)) as H;
      [instantiate (1:=GFS) in (Value of gfs0);
       instantiate (1:=TY) in (Value of t_root);
       instantiate (1:=SH) in (Value of sh);
       instantiate (1:=V) in (Value of v);
       unfold sh, t_root, gfs0, v, p;
       unfold data_at_;
       unfold data_at;
       unify GFS (skipn (length gfs - length GFS) gfs);
       simpl skipn; subst e gfs tts;
       try unfold field_at_;
       generalize V;
       intro;
       solve [
             go_lowerx; rewrite sepcon_emp, <- ?field_at_offset_zero; 
             apply derives_refl
(*
         first [apply remove_PROP_LOCAL_left'; apply derives_refl
               | entailer!; cancel]
*)
       ]
      | pose N as n ].

Ltac sc_new_instantiate P Q R Rnow Delta e gfs tts lr p sh t_root gfs0 v n N H:=
  match Rnow with
  | ?R0 :: ?Rnow' => 
    match R0 with
    | `(data_at ?SH ?TY ?V _) => 
      test_legal_nested_efield TY e gfs tts lr;
      sc_try_instantiate P Q R0 Delta e gfs tts p sh t_root gfs0 v n N H SH (@nil gfield) TY V
    | `(data_at_ ?SH ?TY _) => 
      test_legal_nested_efield TY e gfs tts lr;
      sc_try_instantiate P Q R0 Delta e gfs tts p sh t_root gfs0 v n N H SH (@nil gfield) TY
      (default_val (nested_field_type2 TY nil))
    | `(field_at ?SH ?TY ?GFS ?V _) =>
      test_legal_nested_efield TY e gfs tts lr;
      sc_try_instantiate P Q R0 Delta e gfs tts p sh t_root gfs0 v n N H SH GFS TY V
    | `(field_at_ ?SH ?TY ?GFS _) =>
      test_legal_nested_efield TY e gfs tts lr;
      sc_try_instantiate P Q R0 Delta e gfs tts p sh t_root gfs0 v n N H SH GFS TY
      (default_val (nested_field_type2 TY GFS))
    | _ => sc_new_instantiate P Q R Rnow' Delta e gfs tts lr p sh t_root gfs0 v n (S N) H
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
       unfold data_at;
       instantiate (2 := IDS);
       assert (IDS = skipn (length ids - length IDS) ids) as _ by reflexivity;
       simpl skipn; subst e ids tts;
       instantiate (2 := SH);
       instantiate (1 := V);
       try unfold field_at_;
       generalize V;
       intro;
       solve [ (entailer!; cancel) ]
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
       unfold data_at; (* move to somewhere later? *)
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
       solve [ (entailer!; cancel) ]
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
 eapply derives_trans;  [ | apply (H H0) ].
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
 forall {cs: compspecs} v t i, 
   isptr v -> 
   Cop2.sem_add (tptr t) tint v (Vint (Int.repr i)) = Some (add_ptr_int t v i).
Proof.
intros. destruct v; inv H; reflexivity.
Qed.
Hint Rewrite @sem_add_ptr_int using assumption : norm1.

Arguments field_type id fld / .
Arguments fieldlist.field_type2 i m / .
Arguments nested_field_type2 {cs} t gfs / .

(* old, slow version
Ltac solve_load_rule_evaluation :=
  match goal with
  | |- repinject _ (@proj_reptype ?cs ?t ?gfs ?v) = _ =>
         rewrite (repinject_JMeq _ (@proj_reptype cs t gfs v)) by reflexivity;
         let t' := eval compute in t in
         let gfs' := eval cbv delta [gfs] in gfs in
         let v' := eval cbv delta [v] in v in
         let H := fresh "H" in
         pose_proj_reptype cs t' gfs' v' H;
         exact H
  end.
*)


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

Ltac candidate A :=
 match A with context [_ _] => idtac end.

Ltac really_simplify_one_thing :=
   match goal with
   | |- @eq ?T _ _ => 
    candidate T; progress (really_simplify T)
   | A := @pair ?T _  _ _ |- _ => 
    candidate T; revert A; progress (really_simplify T); intro A
   | A := @pair _ ?T _ _ |- _ => 
    candidate T; revert A; progress (really_simplify T); intro A
   | A := _ : ?T |- _ => 
    candidate T; revert A; progress (really_simplify T); intro A
   | |- context [@pair ?T _ _ _] =>
     candidate T; progress (really_simplify T)
   | |- context [@pair _ ?T _ _] =>
   candidate T; progress (really_simplify T)
   | |- @eq _ ?GG _ => 
   match GG with
    | (_,_) =>
              eapply pair_congr
    | _ => rewrite eq_rect_r_eq
    | _ => rewrite <- eq_rect_eq
    | compact_prod_upd _ _ _ _ _ =>
       unfold compact_prod_upd at 1;
         cbv delta [list_rect]
    | context [fst (?A, ?B)] =>
              change (fst (A, B)) with A
    | context [snd (?A, ?B)] =>
              change (snd (A, B)) with B
    | context [ListTypeGen ?A ?B ?C] =>
       let s := fresh "s" in set (s := ListTypeGen A B C);
       unfold ListTypeGen in s; subst s
    | context [nested_field_type2 ?A ?B] =>
         really_simplify (nested_field_type2 A B)
    | fold_reptype _  =>
           unfold fold_reptype at 1; rewrite eq_rect_r_eq
    | replace_reptype _ _ _ _ =>
      rewrite replace_reptype_ind;
      cbv delta [singleton_hole singleton_hole_rec rev app ]
    | compact_prod_map _ _ _ =>
        unfold compact_prod_map at 1; cbv beta iota zeta delta [list_rect]
    | func_type _ _ _ _ _ _ _ _ _  => 
             rewrite func_type_ind
    | context [co_members (get_co ?i)] =>
            really_simplify (co_members (get_co i))
    | context [gfield_dec ?A ?B] =>
         really_simplify (gfield_dec A B)
    | context [member_dec ?A ?B] =>
       really_simplify (member_dec A B)
    | context [fieldlist.fieldlist.field_type ?A ?B] =>
         really_simplify (fieldlist.fieldlist.field_type A B)
    | context [field_type ?A ?B] =>
         really_simplify (field_type A B)
    | repinject _ _ =>
       cbv delta [repinject proj_reptype]
    | context [default_val ?A] =>
       really_simplify (default_val A)
    | context C [fst (unfold_reptype (?a,?b))] =>
       let A' := context C [fst (a,b)] in
        transitivity A'; 
           [repeat f_equal; 
            unfold unfold_reptype; rewrite <- eq_rect_eq;
            reflexivity
           | change (fst(a,b)) with a]
    | context C [snd (unfold_reptype (?a,?b))] =>
       let A' := context C [snd (a,b)] in
        transitivity A'; 
           [repeat f_equal; 
            unfold unfold_reptype; rewrite <- eq_rect_eq;
            reflexivity
           | change (snd(a,b)) with b]
     | singleton_subs _ _ _ _  =>
        unfold singleton_subs; simpl rgfs_dec;
        unfold eq_rec_r, eq_rec;
        rewrite <- ?eq_rect_eq, ?eq_rect_r_eq
(*    | appcontext [@zl_nth] =>
              progress (autorewrite with zl_nth_db)
*)
     | context [@proj_reptype ?a ?b ?c ?d ?e] =>
         let z := fresh "z" in set (z := @proj_reptype a b c d e);
         cbv beta iota zeta delta [
               proj_reptype proj_gfield_reptype
         ] in z; subst z
     | context [@proj_struct _ _ _ _ _] =>
         cbv beta iota delta [
             proj_struct proj_compact_prod list_rect
          ]; 
         repeat match goal with 
                 | |- context [member_dec ?A ?B] =>
                 really_simplify (member_dec A B);
                cbv beta iota zeta
         end
     | context [@aggregate_type.proj_struct _ _ _ _ _] => 
         cbv delta [
             aggregate_type.proj_struct proj_compact_prod list_rect
         ]
     | context [unfold_reptype _] =>
        unfold unfold_reptype at 1; rewrite <- eq_rect_eq
    end
    | A := ?AA |- _ => first [is_evar AA; fail 1 | subst A]
  end; 
    cbv beta iota zeta.

Ltac really_simplify_some_things := 
   repeat really_simplify_one_thing.

Lemma quick_derives_right:
  forall P Q : environ -> mpred,
   TT |-- Q -> P |-- Q.
Proof.
intros. eapply derives_trans; try eassumption; auto.
Qed.

Ltac quick_typecheck3 := 
 clear; 
 repeat match goal with
 | H := _ |- _ => clear H 
 | H : _ |- _ => clear H 
 end;
 apply quick_derives_right; clear; go_lower;
 clear; repeat apply andp_right; auto; fail.

(*
Ltac solve_load_rule_evaluation := (* fastest version *)
 clear;
 repeat match goal with
  | A : _ |- _ => clear A 
  | A := _ |- _ => clear A 
  end;
  match goal with A := ?gfs : list gfield |- repinject _ (proj_reptype _ _ ?v) = _ =>
   remember_indexes gfs;
   let h0 := fresh "h0" in
   set (h0:=v);
   lazy beta zeta iota delta - [h0 sublist.Znth];
   subst h0;
   subst; apply eq_refl
  end.
*)

Ltac solve_load_rule_evaluation' := (* old faster version *)
  clear;
  repeat match goal with
  | A : _ |- _ => clear A 
  | A := _ |- _ => clear A 
  | A := _ : list gfield |- _ => subst A
  | A := _ : type |- _ => subst A
  end;
  really_simplify_some_things;
  cbv beta iota delta [proj_gfield_reptype]; 
  really_simplify_some_things;
  cbv beta iota delta [aggregate_type.proj_struct proj_struct proj_compact_prod list_rect]; 
  really_simplify_some_things;
  repeat match goal with A := _ |- _ => subst A end;
  really_simplify_some_things;
  simpl; apply eq_refl.

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
   remember_indexes gfs;
   let h0 := fresh "h0" in let h1 := fresh "h1" in
   set (h0:=v0); set (h1:=v1);
   rewrite upd_reptype_ind;
   let j := fresh "j" in match type of h0 with ?J => set (j := J) in h0 end;
   lazy beta zeta iota delta in j; subst j;
   lazy beta zeta iota delta - [rhs h0 h1 upd_Znth_in_list];
   subst rhs h0 h1;
   subst; apply eq_refl
  end.

Ltac solve_store_rule_evaluation'' :=
  clear;
  repeat match goal with
  | A : _ |- _ => clear A 
  | A := _ |- _ => clear A 
  | A := _ : list gfield |- _ => subst A
  | A := _ : type |- _ => subst A
  end;
  apply data_equal_congr;
  match goal with |- context [valinject ?t ?v] =>
     rewrite (valinject_JMeq t v (eq_refl _))
 end;
 rewrite upd_reptype_ind;
 really_simplify_some_things;
 cbv beta iota delta [upd_reptype_rec];
 really_simplify_some_things;
 cbv beta iota delta [upd_gfield_reptype];
 really_simplify_some_things;
 reflexivity.

Ltac solve_store_rule_evaluation' :=
  repeat match goal with
  | A : _ |- _ => clear A 
  | A := _ |- _ => clear A 
  end;
  match goal with
  | |- data_equal (@upd_reptype ?cs ?t ?gfs ?v (valinject ?t0 ?v0)) _ =>
         rewrite (valinject_JMeq t0 v0 (eq_refl _));
         rewrite upd_reptype_ind;
         let t2 := fresh "t2" in set (t2 := t) in *;
         compute in t2; subst t2;
         let t' := eval compute in t in
         let gfs' := eval cbv delta [gfs] in gfs in
         let Hproj := fresh "Hproj" in
         pose_proj_reptype cs t' gfs' v Hproj;
         let Hupd := fresh "Hupd" in
         pose_upd_reptype cs t' gfs' v v0 Hupd;
         clear Hproj;
         match goal with H: data_equal _ ?A |- data_equal _ ?B =>  unify A B end (*
                 this line is to get around a bug in Coq 8.4; in Coq 8.5 maybe
                 it won't be necessary; may be related to "Anomaly: undefined evars"*);
         exact Hupd
  end.

Ltac load_tac :=   (* matches:  semax _ _ (Sset _ (Efield _ _ _)) _  *)
 ensure_normal_ret_assert;
 hoist_later_in_pre;
 match goal with   
| |- semax ?Delta (|> (PROPx ?P (LOCALx ?Q (SEPx ?R)))) (Sset _ (Ecast ?e _)) _ =>
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
    sc_new_instantiate P Q R R Delta e1 gfs tts lr p sh t_root gfs0 v n (0%nat) H;
    
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
    eapply (semax_SC_field_cast_load1 Delta sh n) with (lr0 := lr) (t_root0 := t_root) (gfs2 := gfs0) (gfs3 := gfs1);
    [reflexivity | reflexivity
      | solve [repeat econstructor]
      | unfold app at 1; reflexivity
      | solve [repeat econstructor]
    | reflexivity
    | reflexivity | exact Heq | exact HLE | exact H_Denote | exact H
    | auto (* readable share *)
    | solve_load_rule_evaluation
    | clear Heq HLE H_Denote H;
      subst e1 gfs0 gfs1 efs tts t_root v sh lr n;
      repeat match goal with H := _ |- _ => clear H end;
      try quick_typecheck3; 
      unfold tc_efield; try solve [entailer!]; try (clear Heq HLE H_Denote H (*H_LEGAL*);
      subst e1 gfs0 gfs1 efs tts t_root v sh lr n; simpl app; simpl typeof)
    | solve_legal_nested_field_in_entailment;
         try clear Heq HLE H_Denote H;
         subst e1 gfs0 gfs1 efs tts t_root v sh lr n
    ]

| |- semax ?Delta (|> (PROPx ?P (LOCALx ?Q (SEPx ?R)))) (Sset _ ?e) _ =>
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
    sc_new_instantiate P Q R R Delta e1 gfs tts lr p sh t_root gfs0 v n (0%nat) H;
    
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

    eapply (semax_SC_field_load1 Delta sh n) with (lr0 := lr) (t_root0 := t_root) (gfs2 := gfs0) (gfs3 := gfs1);
    [reflexivity | reflexivity
      | solve [repeat econstructor]
      | unfold app at 1; reflexivity
      | solve [repeat econstructor]
    | reflexivity
    | reflexivity | exact Heq | exact HLE | exact H_Denote | exact H
    | auto (* readable share *)
    | solve_load_rule_evaluation
    | clear Heq HLE H_Denote H;
      subst e1 gfs0 gfs1 efs tts t_root v sh lr n;
      repeat match goal with H := _ |- _ => clear H end;
      try quick_typecheck3; 
      unfold tc_efield; try solve [entailer!]; try (clear Heq HLE H_Denote H (*H_LEGAL*);
      subst e1 gfs0 gfs1 efs tts t_root v sh lr n; simpl app; simpl typeof)
    | solve_legal_nested_field_in_entailment; try clear Heq HLE H_Denote H (*H_LEGAL*);
      subst e1 gfs0 gfs1 efs tts t_root v sh lr n]
end.

Ltac old_load_tac :=   (* matches:  semax _ _ (Sset _ (Efield _ _ _)) _  *)
 ensure_normal_ret_assert;
 hoist_later_in_pre;
 match goal with   
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

Hint Rewrite numbd_rewrite1 : norm2.
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

(*
Ltac simpl_fold_reptype :=
 match goal with
 |- context [@fold_reptype ?cs ?t ?A] => 
    let G := fresh "G" in let Heq := fresh "Heq" in 
     remember (@fold_reptype cs t A) as G eqn:Heq;
     unfold fold_reptype, compact_prod_upd, eq_rect_r in Heq;
     rewrite <- !eq_rect_eq in Heq; simpl in Heq;
     subst G
  end.
*)

Ltac simpl_proj_reptype :=
progress
match goal with |- context [@proj_reptype ?cs ?t ?gfs ?v] =>
  let d := fresh "d" in let Hd := fresh "Hd" in
  remember (@proj_reptype cs t gfs v) as d eqn:Hd;
 unfold proj_reptype, proj_gfield_reptype, unfold_reptype,
   nested_field_type2, nested_field_rec in Hd;
 rewrite ?eq_rect_r_eq, <- ?eq_rect_eq in Hd;
 simpl aggregate_type.aggregate_type.proj_struct in Hd;
 rewrite ?eq_rect_r_eq, <- ?eq_rect_eq in Hd;
  subst d
end.

Ltac store_tac := 
ensure_open_normal_ret_assert;
hoist_later_in_pre;
match goal with
| |- semax ?Delta (|> (PROPx ?P (LOCALx ?Q (SEPx ?R)))) (Sassign ?e ?e2) _ =>
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
    sc_new_instantiate P Q R R Delta e1 gfs tts lr p sh t_root gfs0 v n (0%nat) H;

    try (unify v (default_val (nested_field_type2 t_root gfs0));
          lazy beta iota zeta delta - [list_repeat Z.to_nat] in v);

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
          eapply (semax_SC_field_store Delta sh n)
            with (lr0 := lr) (t_root0 := t_root) (gfs2 := gfs0) (gfs3 := gfs1);
            [reflexivity | reflexivity | reflexivity
            | reflexivity | exact Heq | exact HLE 
            | exact HRE | exact H_Denote | exact H | solve [auto]
            | solve_store_rule_evaluation
            | subst e1 gfs0 gfs1 efs tts t_root sh v0 lr n;
              pre_entailer;
              try quick_typecheck3; 
              clear Heq HLE HRE H_Denote H;
              unfold tc_efield; try solve[entailer!]; 
              simpl app; simpl typeof
            | subst e1 gfs0 gfs1 efs tts t_root sh v0 lr n;
              clear Heq HLE HRE H_Denote H;
              solve_legal_nested_field_in_entailment
           ]
end.

Ltac old_store_tac := 
ensure_open_normal_ret_assert;
hoist_later_in_pre;
match goal with
  | |- @semax ?cs ?Espec ?Delta (|> PROPx ?P (LOCALx ?Q (SEPx ?R))) 
                     (Sassign ?e ?e2) _ =>

 let n := fresh "n" in evar (n: nat); 
  let sh := fresh "sh" in evar (sh: share);
  assert (PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx (number_list O R))) 
     |-- (`(numbd n (mapsto_ sh (typeof e))) (eval_lvalue e)) * TT) as _;
  [ unfold number_list, n, sh; 
   repeat rewrite numbd_lift1; repeat rewrite numbd_lift2;
   unfold at_offset; solve [entailer; cancel]
  |  ];
  eapply (@semax_store_nth Espec cs n Delta P Q R e e2);
    (unfold n,sh; clear n sh);
     [reflexivity | reflexivity |solve [entailer; cancel] | solve [auto] 
     | try solve [entailer!] ]
end.

(* END new semax_load and semax_store tactics *************************)

(*
Ltac semax_logic_and_or :=
first [ eapply semax_logical_or_PQR | eapply semax_logical_and_PQR];
[ auto 50 with closed
| auto 50 with closed
| auto 50 with closed
| auto 50 with closed
| auto | auto | reflexivity
| try solve [intro rho; simpl; repeat apply andp_right; apply prop_right; auto] | ].
*)

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

Ltac forward_return :=
     repeat match goal with |- semax _ _ _ ?D => unfold D, abbreviate; clear D end;
     (eapply semax_pre; [  | apply semax_return ]; 
      entailer_for_return).

Ltac forward_ifthenelse :=
           (*semax_logic_and_or 
           ||*)  fail 2 "Use this tactic:  forward_if POST, where POST is the post condition".

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
                 (SEPx (`(Pre x)  (make_args' fsig (eval_exprlist Delta (argtypes (fst fsig)) bl)) ::
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
*)

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
  | |- @semax _ ?Espec ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) (Scall (Some ?id) (Evar ?f _) ?bl) _ =>

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
  | Sassign _ _ => store_tac
  | Sset _ (Efield ?e _ ?t)  => 
      no_loads_expr e true false;
      first [unify true (match t with Tarray _ _ _ => true | _ => false end);
               forward_setx
              |load_tac]
  | Sset _ (Ecast (Efield ?e _ ?t) _) => 
      no_loads_expr e true false;
      first [unify true (match t with Tarray _ _ _ => true | _ => false end);
               forward_setx
              |load_tac]
  | Sset _ (Ederef ?e _) => 
         no_loads_expr e true false; load_tac
  | Sset _ (Ecast (Ederef ?e _) ?t) => 
         no_loads_expr e true false; 
      first [unify true (match t with Tarray _ _ _ => true | _ => false end);
               forward_setx
              |load_tac]
  | Sset _ (Evar _ ?t)  => 
      first [unify true (match t with Tarray _ _ _ => true | _ => false end);
               forward_setx
              |load_tac]
  | Sset _ (Ecast (Evar _ _) _) => load_tac
  | Sset _ ?e => no_loads_expr e false false; (bool_compute e; forward_ptr_cmp) || forward_setx
  | Sifthenelse ?e _ _ => no_loads_expr e false false; forward_ifthenelse
  | Swhile _ _ => forward_while_complain
  | Sloop (Ssequence (Sifthenelse _ Sskip Sbreak) _) _ => forward_for_complain
(*  | Ssequence (Scall (Some ?id') (Evar _ _) ?el) (Sset _ (Etempvar ?id' _)) => 
          no_loads_exprlist el false; forward_compound_call
*)
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
               repeat simpl_proj_reptype;
(*               try simpl_fold_reptype;*)
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
(*               try simpl_fold_reptype;*)
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
(*  first
   [ simple apply extract_exists_pre;
     let v := fresh "v" in intros v;
     autorewrite with subst;
     simpl_first_temp;
     repeat extract_prop_from_LOCAL;
     revert v
   | (* try simpl_fold_reptype;*)
     simple apply revert_unit
   ];
*)
   repeat simpl_proj_reptype.

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

Ltac forward :=
  check_Delta;
 repeat simple apply seq_assoc2;
 first
 [ fwd_last
 | fwd_skip
 | fwd';
  [ .. |
   repeat (apply semax_extract_PROP; intro);
   abbreviate_semax;
   try fwd_skip]
 ].

(*
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
*)

Lemma start_function_aux1:
  forall (Espec: OracleKind) {cs: compspecs} Delta R1 P Q R c Post,
   semax Delta (PROPx P (LOCALx Q (SEPx (R1::R)))) c Post ->
   semax Delta ((PROPx P (LOCALx Q (SEPx R))) * R1) c Post.
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

Ltac unfold_Delta :=  (* obsolete? replaced by simplify_func_tycontext *)
  repeat match goal with Delta := func_tycontext ?f ?V ?G |- _ =>
     first [unfold f in Delta | unfold V in Delta | unfold G in Delta ]
  end;
 match goal with
   | Delta:=func_tycontext ?f ?V ?G:_
     |- _ =>
         change (func_tycontext f V G)
          with (@abbreviate _ (func_tycontext f V G)) in Delta;
          unfold func_tycontext, make_tycontext, make_tycontext_t,
           make_tycontext_v, make_tycontext_g, fn_temps, fn_params, fn_vars,
           fn_return in Delta;
           let s := fresh in set (s := make_tycontext_s G) in Delta;
           simpl in Delta;
           hnf in s;
           let s' := fresh  "Delta_specs" in pose (s' := @abbreviate _ s); 
           change s with s' in Delta; subst s       
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

Ltac start_function' :=
 match goal with |- semax_body _ _ _ (pair _ (mk_funspec _ _ ?Pre _)) =>
   match Pre with 
   | (fun x => match x with (a,b) => _ end) => intros Espec [a b] 
   | (fun i => _) => intros Espec i
   end;
   simpl fn_body; simpl fn_params; simpl fn_return
 end;
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

(*
Definition compspecs_program (p: program): compspecs.
  apply (mkcompspecs (prog_comp_env p)).
  eapply build_composite_env_consistent.
  apply (prog_comp_env_eq p).
Defined.
*)

Definition mk_prog_compspecs:
  forall (p: program),
  (Forall
    (fun x : ident * composite =>
      composite_legal_alignas (prog_comp_env p) (snd x) /\
      composite_legal_fieldlist (snd x))
      (PTree.elements (prog_comp_env p))) ->
  compspecs.
Proof.
intros p Ha.
apply (mkcompspecs (prog_comp_env p)).
+
eapply build_composite_env_consistent.
apply (prog_comp_env_eq p).
+ intros ? ? ?.
    apply PTree.elements_correct in H.
    revert H.
    change co with (snd (id, co)) at 2.
    forget (id, co) as ele.
    revert ele.
    apply Forall_forall. auto.
    induction (PTree.elements (prog_comp_env p)). constructor.
   inv Ha. constructor; auto.  destruct H1; auto.
+ intros ? ? ?.
    apply PTree.elements_correct in H.
    revert H.
    change co with (snd (id, co)) at 2.
    forget (id, co) as ele.
    revert ele.
    apply Forall_forall. auto.
    induction (PTree.elements (prog_comp_env p)). constructor.
   inv Ha. constructor; auto.  destruct H1; auto.
Defined.

Lemma Zge_refl: forall (n: Z), n >= n.
Proof. intros. omega. Qed.

Lemma EqLtFalse: Eq = Lt -> False.
Proof. intro. discriminate. Qed.

Ltac make_compspecs1 prog :=
let p := eval lazy beta zeta iota delta [
   prog_comp_env 
   PTree.elements PTree.xelements prog
   make_composite_env build_composite_env
  add_composite_definitions composite_of_def
  Errors.bind PTree.get PTree.empty
  ] in (prog_comp_env prog)
in let p := eval simpl in p
in 
assert (H : Forall
       (fun x : ident * composite =>
        composite_legal_alignas p (snd x) /\
        composite_legal_fieldlist (snd x))
        (PTree.elements p)) 
  by (repeat constructor; compute; apply EqLtFalse);
let b :=eval lazy beta zeta iota delta [
   H mk_prog_compspecs prog_comp_env 
   PTree.elements PTree.xelements prog
   make_composite_env build_composite_env
  add_composite_definitions composite_of_def
  Errors.bind PTree.get PTree.empty
  ] in (mk_prog_compspecs prog H)
in let b := eval simpl in b
in exact b.

Ltac make_compspecs2 CS :=
 let a := eval lazy beta delta [CS] in CS
 in exact a.

Ltac make_compspecs prog :=
assert (H : Forall
       (fun x : ident * composite =>
        composite_legal_alignas (prog_comp_env prog) (snd x) /\
        composite_legal_fieldlist (snd x))
       (PTree.elements (prog_comp_env prog)))
  by (repeat constructor; try apply Zge_refl);
let a := eval vm_compute in (mk_prog_compspecs prog H)
 in exact a.
