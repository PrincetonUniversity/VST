Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.go_lower.
Require Import VST.floyd.closed_lemmas.
Require Import VST.floyd.subsume_funspec.
Require Import VST.floyd.forward_lemmas VST.floyd.call_lemmas.
Require Import VST.floyd.extcall_lemmas.
Require Import VST.floyd.nested_field_lemmas.
Require Import VST.floyd.efield_lemmas.
Require Import VST.floyd.type_induction.
Require Import VST.floyd.mapsto_memory_block.
Require Import VST.floyd.data_at_rec_lemmas.
Require Import VST.floyd.field_at.
Require Import VST.floyd.loadstore_mapsto.
Require Import VST.floyd.loadstore_field_at.
Require Import VST.floyd.nested_loadstore.
Require Import VST.floyd.sc_set_load_store.
Require Import VST.floyd.stronger.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.local2ptree_eval.
Require Import VST.floyd.reptype_lemmas.
Require Import VST.floyd.proj_reptype_lemmas.
Require Import VST.floyd.replace_refill_reptype_lemmas.
Require Import VST.floyd.aggregate_type.
Require Import VST.floyd.entailer.
Require Import VST.floyd.globals_lemmas.
Require Import VST.floyd.semax_tactics.
Require Import VST.floyd.for_lemmas.
Require Import VST.floyd.diagnosis.
Require Import VST.floyd.simpl_reptype.
Require Import VST.floyd.nested_pred_lemmas.
Require Import VST.floyd.freezer.
(*Require Import VST.floyd.funspec_old.*)
Import Cop.
Import Cop2.
Import Clight_Cop2.
Import LiftNotation.

Global Opaque denote_tc_test_eq.

Hint Rewrite @sem_add_pi_ptr_special' using (solve [try reflexivity; auto with norm]) : norm.
Hint Rewrite @sem_add_pl_ptr_special' using (solve [try reflexivity; auto with norm]) : norm.

Lemma func_ptr'_emp phi v: func_ptr' phi v |-- emp.
Proof. apply andp_left2; trivial. Qed.

Lemma func_ptr'_mono {fs gs v}: funspec_sub fs gs ->
       func_ptr' fs v |-- func_ptr' gs v.
Proof. intros. apply andp_derives; trivial. apply func_ptr_mono; trivial. Qed.

Lemma isptr_force_sem_add_ptr_int:
  forall {cs: compspecs}  t si p i,
 complete_type cenv_cs t = true ->
 isptr p ->
 isptr (force_val (sem_add_ptr_int t si p (Vint (Int.repr i)))).
Proof.
intros. destruct p; inv H0; hnf; auto.
unfold sem_add_ptr_int.
rewrite H; simpl; auto.
Qed.

#[export] Hint Extern 2 (isptr (force_val (sem_add_ptr_int _ _ _ _))) =>
    apply isptr_force_sem_add_ptr_int; [reflexivity | auto with prove_it_now] : core.

(* Done in this tail-recursive style so that "hnf" fully reduces it *)
Fixpoint mk_varspecs' (dl: list (ident * globdef Clight.fundef type)) (el: list (ident * type)) :
     list (ident * type) :=
 match dl with
 | (i,Gvar v)::dl' => mk_varspecs' dl' ((i, gvar_info v) :: el)
 | (i, _) :: dl' => mk_varspecs' dl' el
 | nil => rev_append el nil
end.

Ltac unfold_varspecs al :=
 match al with
 | context [gvar_info ?v] =>
      let b := eval lazy beta zeta iota delta [gvar_info v] in al
      in unfold_varspecs b
 | _ => exact al
 end.

Ltac mk_varspecs prog :=
 let a := constr:(prog)
   in let a := eval unfold prog in a
   in let d :=  match a with
                    | Clightdefs.mkprogram _ ?d _ _ _ => constr:(d)
                    | {| prog_defs := ?d |} => constr:(d)
                    end
   in let e := constr:(mk_varspecs' d nil)
          in let e := eval hnf in e
          in unfold_varspecs e.

#[export] Hint Resolve field_address_isptr : norm.

Lemma field_address_eq_offset':
 forall {cs: compspecs} t path v ofs,
    field_compatible t path v ->
    ofs = nested_field_offset t path ->
    field_address t path v = offset_val ofs v.
Proof.
intros. subst. apply field_compatible_field_address; auto.
Qed.

#[export] Hint Resolve field_address_eq_offset' : prove_it_now.

Hint Rewrite <- @prop_and using solve [auto with typeclass_instances]: norm1.

Local Open Scope logic.


Lemma var_block_lvar2:
 forall {cs: compspecs} {Espec: OracleKind} id t Delta P Q R Vs c Post,
   (var_types Delta) ! id = Some t ->
   complete_legal_cosu_type t = true ->
   sizeof t < Ptrofs.modulus ->
   is_aligned cenv_cs ha_env_cs la_env_cs t 0 = true ->
  (forall v,
   semax Delta ((PROPx P (LOCALx (lvar id t v :: Q) (SEPx (data_at_ Tsh t v :: R))))
                      * fold_right sepcon emp Vs)
               c Post) ->
 semax Delta ((PROPx P (LOCALx Q (SEPx R)))
                      * fold_right sepcon emp (var_block Tsh (id,t) :: Vs))
               c Post.
Proof.
intros.
assert (Int.unsigned Int.zero + sizeof t <= Ptrofs.modulus)
 by (rewrite Int.unsigned_zero; lia).
eapply semax_pre.
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
apply exp_right with (Vptr b Ptrofs.zero).
unfold size_compatible.
rewrite prop_true_andp. rewrite TT_andp.
rewrite memory_block_data_at_.
cancel.
split3; auto. apply Coq.Init.Logic.I.
split3; auto.
apply la_env_cs_sound; auto.
apply Coq.Init.Logic.I.
split; auto.
rewrite memory_block_isptr; normalize.
rewrite memory_block_isptr; normalize.
apply extract_exists_pre.  apply H3.
Qed.

Lemma var_block_lvar0
     : forall {cs: compspecs} (id : positive) (t : type) (Delta : tycontext)  v rho,
       (var_types Delta) ! id = Some t ->
       complete_legal_cosu_type t = true ->
       sizeof t < Ptrofs.modulus ->
       is_aligned cenv_cs ha_env_cs la_env_cs t 0 = true ->
       tc_environ Delta rho ->
       locald_denote (lvar id t v) rho ->
       data_at_ Tsh t v |-- var_block Tsh (id, t) rho.
Proof.
intros.
hnf in H4.
assert (Ptrofs.unsigned Ptrofs.zero + sizeof t <= Ptrofs.modulus)
 by (rewrite Ptrofs.unsigned_zero; lia).
unfold var_block.
simpl @fst; simpl @snd.
rewrite prop_true_andp
  by (change (Ptrofs.max_unsigned) with (Ptrofs.modulus-1); lia).
unfold_lift.
rewrite (lvar_eval_lvar _ _ _ _ H4).
rewrite memory_block_data_at_; auto.
hnf in H4.
destruct ( Map.get (ve_of rho) id); try contradiction.
destruct p.
destruct H4; subst.
repeat split; auto.
apply la_env_cs_sound; eauto.
Qed.

Lemma postcondition_var_block:
  forall {cs: compspecs} {Espec: OracleKind} Delta Pre c S1 S2 i t vbs,
       (var_types  Delta) ! i = Some t ->
       complete_legal_cosu_type t = true ->
       sizeof t < Ptrofs.modulus ->
       is_aligned cenv_cs ha_env_cs la_env_cs t 0 = true ->
   semax Delta Pre c (frame_ret_assert S1
     (S2 *  (EX  v : val, local (locald_denote (lvar i t v)) && `(data_at_ Tsh t v))
      * fold_right sepcon emp vbs)) ->
  semax Delta Pre c (frame_ret_assert S1
     (S2 * fold_right sepcon emp (var_block Tsh (i,t) :: vbs))).
Proof.
intros.
destruct S1 as [?R ?R ?R ?R];
eapply semax_post; try apply H3; clear H3;
 intros; simpl_ret_assert; go_lowerx.
*
apply sepcon_derives; auto.
rewrite <- !sepcon_assoc.
apply sepcon_derives; auto.
apply sepcon_derives; auto.
apply exp_left; intro v.
normalize.
eapply var_block_lvar0; try apply H; try eassumption.
*
apply sepcon_derives; auto.
rewrite <- !sepcon_assoc.
apply sepcon_derives; auto.
apply sepcon_derives; auto.
apply exp_left; intro v.
normalize.
eapply var_block_lvar0; try apply H; try eassumption.
*
apply sepcon_derives; auto.
rewrite <- !sepcon_assoc.
apply sepcon_derives; auto.
apply sepcon_derives; auto.
apply exp_left; intro v.
normalize.
eapply var_block_lvar0; try apply H; try eassumption.
*
apply sepcon_derives; auto.
rewrite <- !sepcon_assoc.
apply sepcon_derives; auto.
apply sepcon_derives; auto.
apply exp_left; intro v.
normalize.
eapply var_block_lvar0; try apply H; try eassumption.
Qed.

Ltac process_stackframe_of :=
 lazymatch goal with |- semax _ (_ * stackframe_of ?F) _ _ =>
   let sf := fresh "sf" in set (sf:= stackframe_of F) at 1;
     unfold stackframe_of in sf; simpl map in sf; subst sf
  end;
 repeat
   lazymatch goal with |- semax _ (_ * fold_right sepcon emp (var_block _ (?i,_) :: _)) _ _ =>
     simple apply var_block_lvar2;
       [ reflexivity | reflexivity | reflexivity | reflexivity | let n := fresh "v" i in intros n ]
   end;
  repeat (simple apply postcondition_var_block;
   [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity |  ]);
 change (fold_right sepcon emp (@nil (environ->mpred))) with
   (@emp (environ->mpred) _ _);
 rewrite ?sepcon_emp, ?emp_sepcon.

Definition tc_option_val' (t: type) : option val -> Prop :=
 match t with Tvoid => fun v => True | _ => fun v => tc_val t (force_val v) end.
Lemma tc_option_val'_eq: tc_option_val = tc_option_val'.
Proof. extensionality t v.
unfold tc_option_val, tc_option_val'.
destruct t as [ | | | [ | ] |  | | | | ] eqn:?,v eqn:?; try reflexivity.
unfold tc_val. destruct (eqb_type _ _); reflexivity.
Qed.
Hint Rewrite tc_option_val'_eq : norm.

Lemma emp_make_ext_rval:
  forall ge t v, @emp (environ->mpred) _ _ (make_ext_rval ge t v) = emp.
Proof. reflexivity. Qed.
Hint Rewrite emp_make_ext_rval : norm2.

Ltac semax_func_cons_ext_tc :=
  repeat match goal with
  | |- (forall x: (?A * ?B), _) =>
      intros [? ?];  match goal with a1:_ , a2:_ |- _ => revert a1 a2 end
  | |- forall x:?T, _ => let t := fresh "t" in set (t:=T); progress simpl in t; subst t
  | |- forall x, _ => intro
  end;
  try apply prop_True_right;
  normalize; simpl tc_option_val' .

Ltac fast_Qed_reflexivity :=
hnf;
match goal with |- ?A = ?B => 
 let a := eval compute in A in let b := eval compute in B in unify a b;
  vm_cast_no_check (eq_refl b) 
end.

Ltac LookupID := 
 lazymatch goal with
 | GS : Genv.genv_symb _ = @abbreviate _ _ |- _ =>
    cbv beta delta [Genv.find_symbol]; rewrite GS
 | _ => idtac "Using alternate LookupID"
 end;
 fast_Qed_reflexivity
  || fail "Lookup for a function identifier in Genv failed".

Ltac LookupB := 
 lazymatch goal with
 | GD : Genv.genv_defs _ = @abbreviate _ _ |- _ =>
    cbv beta delta [Genv.find_funct_ptr Genv.find_def]; rewrite GD
 | _ => idtac "Using alternate LookupB"
 end;
 fast_Qed_reflexivity
 || fail "Lookup for a function pointer block in Genv failed".

Lemma semax_body_subsumption' cs cs' V V' F F' f spec
      (SF: @semax_body V F cs f spec)
      (CSUB: cspecs_sub cs cs')
      (COMPLETE : Forall (fun it : ident * type => complete_type (@cenv_cs cs) (snd it) = true) (fn_vars f))
      (TS: tycontext_sub (func_tycontext f V F nil) (func_tycontext f V' F' nil)):
  @semax_body V' F' cs' f spec.
Proof.
  intros.
  apply (@semax_body_cenv_sub _ _ CSUB); auto.
  eapply semax_body_subsumption; try eassumption.
Qed.

Lemma sub_option_get' {A: Type} (s t: PTree.t A) B (f:A -> option B):
  Forall (fun x => PTree.get (fst x) t = Some (snd x)) (PTree.elements s) ->
  forall i, sub_option (match PTree.get i s with Some x => f x | _ => None end)
                       (match PTree.get i t with Some x => f x | _ => None end).
Proof.
intros.
destruct (s ! i) eqn:?H; [ | apply I].
pose proof (PTree.elements_correct s i H0).
rewrite Forall_forall in H.
apply H in H1.
simpl in H1. rewrite H1. apply sub_option_refl.
Qed.

Lemma sub_option_get {A: Type} (s t: PTree.t A):
  Forall (fun x => PTree.get (fst x) t = Some (snd x)) (PTree.elements s) ->
  forall i, sub_option (PTree.get i s) (PTree.get i t).
Proof.
  intros; specialize (sub_option_get' s t A Some H i); intros.
  destruct (s!i); [simpl; destruct (t!i); inv H0 | ]; trivial.
Qed. 

Definition tycontext_subVG Vprog1 Gprog1 Vprog2 Gprog2 :=
 (forall id : positive,
   sub_option (make_tycontext_g Vprog1 Gprog1) ! id
    (make_tycontext_g Vprog2 Gprog2) ! id) /\
 (forall id : positive,
   subsumespec (make_tycontext_s Gprog1) ! id (make_tycontext_s Gprog2) ! id).

Lemma tycontext_sub_i99:
 forall f Vprog1 Vprog2 Gprog1 Gprog2 Annot,
 tycontext_subVG Vprog1 Gprog1 Vprog2 Gprog2 ->
  tycontext_sub (func_tycontext f Vprog1 Gprog1 Annot)
                    (func_tycontext f Vprog2 Gprog2 Annot).
Proof.
intros.
destruct H.
split3; [ | | split3; [ | | split]]; auto.
-
unfold temp_types, func_tycontext, make_tycontext.
intros. destruct ((make_tycontext_t (fn_params f) (fn_temps f)) ! id); auto.
-
intros. apply Annotation_sub_refl.
Qed.

  Lemma make_tycontext_s_app1 G1 G2 i:
    sub_option (make_tycontext_s G1) ! i (make_tycontext_s (G1++G2)) ! i.
  Proof.
    red; rewrite 2 semax_prog.find_id_maketycontext_s.
    remember (initial_world.find_id i G1) as q; destruct q; [symmetry in Heqq | trivial].
    apply initial_world.find_id_app1; trivial.
  Qed.
  Lemma make_tycontext_s_app2 G1 G2 i: list_norepet (map fst (G1++G2)) ->
    sub_option (make_tycontext_s G2) ! i (make_tycontext_s (G1++G2)) ! i.
  Proof.
    intros; red; rewrite 2 semax_prog.find_id_maketycontext_s.
    remember (initial_world.find_id i G2) as q; destruct q; [symmetry in Heqq | trivial].
    apply initial_world.find_id_app2; trivial.
  Qed.
  
  Lemma make_tycontext_g_app1 V G1 G2 (HG1: list_norepet (map fst G1))
        (HG12: list_norepet (map fst V ++ map fst (G1 ++ G2))) i:
    sub_option ((make_tycontext_g V G1) ! i) ((make_tycontext_g V (G1 ++ G2)) ! i).
  Proof.
    intros. apply semax_prog.suboption_make_tycontext_s_g; trivial.
    intros. eapply make_tycontext_s_app1. 
  Qed.
  Lemma make_tycontext_g_app2 V G1 G2 (HG1: list_norepet (map fst G2))
        (HG12: list_norepet (map fst V ++ map fst (G1 ++ G2))) i:
    sub_option ((make_tycontext_g V G2) ! i) ((make_tycontext_g V (G1 ++ G2)) ! i).
  Proof.
    intros. apply semax_prog.suboption_make_tycontext_s_g; trivial.
    apply list_norepet_append_right in HG12. 
    intros. eapply make_tycontext_s_app2; trivial. 
  Qed.
  
  Lemma subsumespec_app1 G1 G2 i:
    subsumespec ((make_tycontext_s G1) ! i) ((make_tycontext_s (G1++G2)) ! i).
  Proof.
    red. remember ((make_tycontext_s G1) ! i) as q; destruct q; [symmetry in Heqq | trivial].
    specialize (make_tycontext_s_app1 G1 G2 i). rewrite Heqq; simpl. intros X; rewrite X; clear X.
    exists f; split. trivial. apply funspec_sub_si_refl.
  Qed.
  
  Lemma subsumespec_app2 G1 G2 i: list_norepet (map fst (G1++G2)) ->
    subsumespec ((make_tycontext_s G2) ! i) ((make_tycontext_s (G1++G2)) ! i).
  Proof.
    intros; red. remember ((make_tycontext_s G2) ! i) as q; destruct q; [symmetry in Heqq | trivial].
    specialize (make_tycontext_s_app2 G1 G2 i H). rewrite Heqq; simpl. intros X; rewrite X; clear X.
    exists f; split. trivial. apply funspec_sub_si_refl.
  Qed.

  Lemma tycontext_sub_Gprog_app1 f V G1 G2 (HG1: list_norepet (map fst G1))
        (HG12: list_norepet (map fst V ++ map fst (G1 ++ G2))):
    tycontext_sub (func_tycontext f V G1 [])
                  (func_tycontext f V (G1++G2) []).
  Proof.
     apply tycontext_sub_i99. split; intros.
     + apply make_tycontext_g_app1; trivial.
     + apply subsumespec_app1.
  Qed.

  Lemma tycontext_sub_Gprog_app2 f V G1 G2 (HG1: list_norepet (map fst G2))
        (HG12: list_norepet (map fst V ++ map fst (G1 ++ G2))):
    tycontext_sub (func_tycontext f V G2 [])
                  (func_tycontext f V (G1++G2) []).
  Proof.
     apply tycontext_sub_i99. split; intros.
     + apply make_tycontext_g_app2; trivial.
     + apply list_norepet_append_right in HG12. apply subsumespec_app2; trivial.
  Qed.
  
  Lemma tycontext_sub_Gprog_nil f V G (VG:list_norepet (map fst V ++ map fst G)):
    tycontext_sub (func_tycontext f V [] [])
                  (func_tycontext f V G []).
  Proof.
    specialize (tycontext_sub_Gprog_app1 f V nil G); simpl.
    intros H; apply H; clear H; [ constructor | trivial].
  Qed.
  
Lemma subsume_spec_get:
  forall (s t: PTree.t funspec),
   Forall (fun x => subsumespec (Some (snd x)) (t ! (fst x))) (PTree.elements s) ->
   (forall i, subsumespec (s ! i) (t ! i)).
Proof.
intros.
destruct (s ! i) eqn:?H; [ | apply I].
pose proof (PTree.elements_correct s i H0).
rewrite Forall_forall in H.
apply H in H1.
auto.
Qed.

Ltac apply_semax_body L := 
eapply (@semax_body_subsumption' _ _ _ _ _ _ _ _ L);
  [ first [ apply cspecs_sub_refl
          | split3; red; apply @sub_option_get; 
            repeat (apply Forall_cons; [reflexivity | ]);  apply Forall_nil ]
 | repeat (apply Forall_cons; [ reflexivity | ]); apply Forall_nil
 | simple apply tycontext_sub_refl ||
          (apply tycontext_sub_i99; assumption)].

Ltac try_prove_tycontext_subVG L :=
  match goal with |- semax_func ?V2 ?G2 _ _ _ =>
    try match type of L with
    | semax_body ?V1 ?G1 _ _ =>
     lazymatch goal with
     | H: tycontext_subVG V1 G1 V2 G2 |- _ => idtac
     | _ => 
      let H := fresh in
      assert (H: tycontext_subVG V1 G1 V2 G2);
      [split;
        [apply sub_option_get;
          let A1 := fresh "A1" in let A2 := fresh "A2" in
          set (A1 := make_tycontext_g V1 G1);
          set (A2 := make_tycontext_g V2 G2);
          compute in A1; compute in A2; subst A1 A2;
          repeat (apply Forall_cons; [reflexivity | ]);  apply Forall_nil
         | apply subsume_spec_get;
          let A1 := fresh "A1" in let A2 := fresh "A2" in
          set (A1 := make_tycontext_s G1);
          set (A2 := make_tycontext_s G2);
          let a := make_ground_PTree A1 in change A1 with a; clear A1;
          let a := make_ground_PTree A2 in change A2 with a; clear A2;
          repeat (apply Forall_cons; [apply subsumespec_refl | ]); 
          apply Forall_nil
         ] | ]
     end end end.

Ltac semax_func_cons L := 
 repeat (eapply semax_func_cons_ext_vacuous; [reflexivity | reflexivity | LookupID | LookupB |]);
 try_prove_tycontext_subVG L;
 first [eapply semax_func_cons;
           [ reflexivity
           | repeat apply Forall_cons; try apply Forall_nil; try computable; reflexivity
           | unfold var_sizes_ok; repeat constructor; try (simpl; rep_lia)
           | reflexivity | LookupID | LookupB
           | try solve [apply L]; apply_semax_body L
           | ]
        | eapply semax_func_cons_ext;
             [reflexivity | reflexivity | reflexivity
             | left; reflexivity
             | semax_func_cons_ext_tc | LookupID | LookupB | apply L |
             ]
        ];
 repeat (eapply semax_func_cons_ext_vacuous; [reflexivity | reflexivity | LookupID | LookupB |]);
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
  forall (f: val -> Prop)  t (v: val) (gx: genviron) (ret: option val) P R,
 f v -> 
 (PROPx P
 (LOCALx (temp ret_temp v::nil)
 (SEPx R))) (make_ext_rval gx t ret) |-- !! f (force_val ret).
Proof.
intros.
 rewrite <- insert_local.
 rewrite lower_andp.
 apply derives_extract_prop; intro.
 hnf in H0. unfold_lift in H0.
 destruct H0.
apply prop_right.
unfold make_ext_rval in H0.
destruct (rettype_eq t AST.Tvoid).
subst t.
unfold eval_id in H0; simpl in H0. contradiction.
destruct t; try contradiction;
destruct ret; try (change (v = v0) in H0; subst v0; auto);
change (v = Vundef) in H0; contradiction.
Qed.

Ltac semax_func_cons_ext :=
 repeat (eapply semax_func_cons_ext_vacuous; [reflexivity | reflexivity | LookupID | LookupB | ]);
  eapply semax_func_cons_ext;
    [ reflexivity | reflexivity |  reflexivity 
    | left; reflexivity
    | semax_func_cons_ext_tc;
      try solve [apply typecheck_return_value; auto]
    | LookupID | LookupB
    | solve[ first [eapply semax_ext;
          [ (*repeat first [reflexivity | left; reflexivity | right]*) apply from_elements_In; reflexivity
          | apply compute_funspecs_norepeat_e; reflexivity
          | reflexivity ]]]
      || fail "Try 'eapply semax_func_cons_ext.'"
              "To solve [semax_external] judgments, do 'eapply semax_ext.'"
              "Make sure that the Espec declared using 'Existing Instance'
               is defined as 'add_funspecs NullExtension.Espec Gprog.'"
    |
    ].

Tactic Notation "forward_seq" :=
  first [eapply semax_seq'; [  | abbreviate_semax ]
         | eapply semax_post_flipped' ].

Tactic Notation "forward_seq" constr(R) :=
match goal with P := @abbreviate ret_assert _ |- semax _ _ _ ?P' =>
  constr_eq P P'; unfold abbreviate in P; subst P;
  first [apply semax_seq with R; abbreviate_semax
          | apply (semax_post_flipped' R); [abbreviate_semax | ]]
end.

(* end of "stuff to move elsewhere" *)

Lemma local_True_right:
 forall (P: environ -> mpred),
   P |-- local (`True).
Proof. intros. intro rho; apply TT_right.
Qed.

Lemma force_val_sem_cast_neutral_isptr:
  forall v,
  isptr v ->
  Some (force_val (sem_cast_pointer v)) = Some v.
Proof.
intros.
 destruct v; try contradiction; reflexivity.
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

Ltac check_vl_eq_args:=
first [ 
   cbv beta; go_lower;
   repeat (( simple apply derives_extract_prop
                || simple apply derives_extract_prop');
                fancy_intros true);
   gather_prop;
   repeat (( simple apply derives_extract_prop
                || simple apply derives_extract_prop');
                fancy_intros true);
 repeat erewrite unfold_reptype_elim in * by reflexivity;
   try autorewrite with entailer_rewrite in *;
   simpl; auto;
 apply prop_right;
 match goal with
 | |- ?A = ?B =>
    unify (Datatypes.length A) (Datatypes.length B)
 | |- @eq (list val) _ _ =>
    fail 100 "Length of PARAMS list is not equal to the number of formal parameters of the funsig"
 | |- _ => fail 100 "Mysterious error in check_vl_eq_args"
 end;    
 repeat match goal with |- _ :: _ = _ :: _ => f_equal end;
 normalize;
 unfold field_address, field_address0;
 rewrite if_true; auto;
 auto with field_compatible;
 match goal with |- ?G => 
  match G with
  | field_compatible0 _ _ _ => idtac
  | field_compatible _ _ _ => idtac
  end;
  fail 100 "Before forward_call, assert and prove" G
 end
  | idtac (*alternative: fail 99 "Fail in tactic check_vl_eq_args"*)] .

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
     apply exp_congr; intros [? ?]; reflexivity
  | rewrite exp_uncurry2;
     apply exp_congr; intros [[? ?] ?]; reflexivity
  | rewrite exp_uncurry3;
     apply exp_congr; intros [[[? ?] ?] ?]; reflexivity
  ].

Ltac change_compspecs' cs cs' :=
  match goal with
  | |- context [@data_at cs' ?sh ?t ?v1] => erewrite (@data_at_change_composite cs' cs _ sh t); [| apply JMeq_refl | reflexivity]
  | |- context [@field_at cs' ?sh ?t ?gfs ?v1] => erewrite (@field_at_change_composite cs' cs _ sh t gfs); [| apply JMeq_refl | reflexivity]
  | |- context [@data_at_ cs' ?sh ?t] => erewrite (@data_at__change_composite cs' cs _ sh t); [| reflexivity]
  | |- context [@field_at_ cs' ?sh ?t ?gfs] => erewrite (@field_at__change_composite cs' cs _ sh t gfs); [| reflexivity]
  | |- context [?A cs'] => change (A cs') with (A cs)
  | |- context [?A cs' ?B] => change (A cs' B) with (A cs B)
  | |- context [?A cs' ?B ?C] => change (A cs' B C) with (A cs B C)
  | |- context [?A cs' ?B ?C ?D] => change (A cs' B C D) with (A cs B C D)
  | |- context [?A cs' ?B ?C ?D ?E] => change (A cs' B C D E) with (A cs B C D E)
  | |- context [?A cs' ?B ?C ?D ?E ?F] => change (A cs' B C D E F) with (A cs B C D E F)
 end.

(* TODO: use CCE as arguments to gain CS' *)
Ltac change_compspecs cs :=
 match goal with |- context [?cs'] =>
   match type of cs' with compspecs =>
     try (constr_eq cs cs'; fail 1);
     change_compspecs' cs cs';
     repeat change_compspecs' cs cs'
   end
end.


Ltac check_struct_params al :=
 lazymatch al with
 | nil => idtac
 | Tstruct _ _ :: _ => fail "struct parameters are not supported in VST"
 | Tunion _ _ :: _ => fail "union parameters are not supported in VST"
 | _ :: ?al' => check_struct_params al'
 end.

Ltac check_callconv cc := 
 (tryif unify (cc_structret cc) false then idtac else fail "struct-returning functions are not supported in VST");
 (tryif unify (cc_unproto cc) false then idtac else fail "no-prototype functions are not supported in VST");
 (tryif unify (cc_vararg cc) false then idtac else fail "vararg function definitions are not supported in VST; there is some limited support for calling (but not defining) printf and fprintf").

Ltac function_body_unsupported_features spec :=
 check_callconv (fn_callconv spec);
 let al := constr:(map snd  (fn_params spec)) in let al := eval compute in al in 
 check_struct_params al.

Definition Warning_perhaps_funspec_postcondition_needs_EX_outside_PROP_LOCAL_SEP (p: Prop) := p.
Ltac give_EX_warning :=
     match goal with |- ?A => change
                 (Warning_perhaps_funspec_postcondition_needs_EX_outside_PROP_LOCAL_SEP A)
             end.

Ltac check_parameter_types :=
   match goal with |- _ = fun_case_f (typelist_of_type_list ?argsig) ?retty ?cc =>
     check_callconv cc; 
     let al := eval compute in argsig in 
    check_struct_params al
  end;
  first [reflexivity | elimtype  Parameter_types_in_funspec_different_from_call_statement].

Ltac check_result_type :=
   first [reflexivity | elimtype  Result_type_in_funspec_different_from_call_statement].

Inductive Cannot_find_function_spec_in_Delta (id: ident) := .
Inductive Global_function_name_shadowed_by_local_variable := .

Ltac check_function_name :=
   first [reflexivity | elimtype Global_function_name_shadowed_by_local_variable].

Inductive Actual_parameters_cannot_be_coerced_to_formal_parameter_types := .

Ltac check_cast_params :=
reflexivity + 
(simpl explicit_cast_exprlist;
lazymatch goal with |- force_list (map ?F ?A) = _ =>
  let el := constr:(A) in 
  let bl := constr:(map F A) in
  let cl := eval simpl in bl in 
  fail 100 "Some of the argument expressions in your function call do not evaluate (sometimes this is caused by missing LOCALs in your precondition).  Your argument expressions are:"
         el "They evaluate (or fail) as follows:" cl
end).

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

Ltac lookup_spec id :=
 tryif apply f_equal_Some
 then
   match goal with
   | |- vacuous_funspec _ = _ => fail 100 "Your Gprog contains no funspec with the name" id
   | |- ?fs = _ => check_canonical_funspec (id,fs);
      first [reflexivity |
      match goal with
       | |- mk_funspec _ _ ?t1 _ _ = mk_funspec _ _ ?t2 _ _ =>
         first [unify t1 t2
           | elimtype False; elimtype (Witness_type_of_forward_call_does_not_match_witness_type_of_funspec
      t2 t1)]
      end]
   end
 else fail 100 "Your Gprog contains no funspec with the name" id.

Inductive Function_arguments_include_a_memory_load_of_type (t:type) := .

Ltac goal_has_evars :=
 match goal with |- ?A => has_evar A end.

Lemma drop_SEP_tc:
 forall Delta P Q R' RF R S,
   (forall rho, predicates_hered.boxy predicates_sl.extendM (S rho)) ->
   fold_right_sepcon R = sepcon (fold_right_sepcon R') (fold_right_sepcon RF) ->
   ENTAIL Delta, PROPx P (LOCALx Q (SEPx R')) |-- S ->
   ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- S.
Proof.
  intros.
  unfold PROPx, LOCALx, SEPx in H1 |- *.
  intro rho; specialize (H1 rho).
  simpl in H1 |- *.
  unfold local, lift1; simpl.
  rewrite H0.
  rewrite <- !sepcon_andp_prop'.
  specialize (H rho).
  eapply derives_trans; [apply sepcon_derives; [exact H1 | apply derives_refl] |].
  apply (@predicates_sl.extend_sepcon _ _ _ _ compcert_rmaps.R.Age_rmap); auto.
Qed.

Ltac delete_FRZR_from_SEP :=
match goal with
| |- ENTAIL _, PROPx _ (LOCALx _ (SEPx ?R)) |-- _ =>
  match R with context [FRZR] =>
  eapply drop_SEP_tc;
    [ first [apply extend_tc.extend_tc_expr
             | apply extend_tc.extend_tc_exprlist
             | apply extend_tc.extend_tc_lvalue]
   | apply split_FRZ_in_SEP_spec; prove_split_FRZ_in_SEP
   | ]
end end.

Ltac check_typecheck :=
 try delete_FRZR_from_SEP;
 first [goal_has_evars; idtac |
 try apply local_True_right;
 entailer!;
 match goal with
 | |- typecheck_error (deref_byvalue ?T) =>
       elimtype (Function_arguments_include_a_memory_load_of_type T)
 | |- _ => idtac
 end].

Ltac prove_delete_temp := match goal with |- ?A = _ =>
  (* This leads to exponential Qed blow up: let Q := fresh "Q" in set (Q:=A); hnf in Q; subst Q; reflexivity *)
  reflexivity
end.

Ltac cancel_for_forward_call := cancel_for_evar_frame.
Ltac default_cancel_for_forward_call := cancel_for_evar_frame.

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

Ltac fix_up_simplified_postcondition_warning :=
  idtac "Warning: Fixed up a postcondition that was damaged; typically this has happened because you did 'simpl in *' that messed up Delta_specs.  Avoid 'simpl in *'.".

Ltac fix_up_simplified_postcondition_failure :=
  idtac "Error: Unable to repair a postcondition that was damaged; typically this has happened because you did 'simpl in *' that messed up Delta_specs.  Avoid 'simpl in *'.".


Ltac fix_up_simplified_postcondition := 
  (* If the user's postcondition (e.g., fetched from Delta_specs) has been
    messed up by 'simpl in *', try to patch it. *)
  lazymatch goal with
  | |- (fun a => exp (fun x:?T => ?P a)) = ?Q => 
            (change (exp (fun x:T => P) = Q) || fix_up_simplified_postcondition_warning)
            || fix_up_simplified_postcondition_failure
  | |- (fun a => ?P a) = ?Q => 
           (change (P=Q); fix_up_simplified_postcondition_warning)
          || fix_up_simplified_postcondition_failure
  | |- _ => idtac
 end.

Ltac match_postcondition := 
fix_up_simplified_postcondition;
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

Ltac prove_PROP_preconditions :=
  unfold fold_right_and; repeat rewrite and_True; my_auto.

Ltac  forward_call_id1_wow_nil := 
let H := fresh in intro H;
eapply (semax_call_id1_wow_nil H); 
 clear H; 
 lazymatch goal with Frame := _ : list mpred |- _ => try clear Frame end;
 [check_result_type
 |apply Logic.I
 | match_postcondition
 | prove_delete_temp
 | unify_postcondition_exps
 | prove_PROP_preconditions
 ].

Ltac  forward_call_id1_wow := 
let H := fresh in intro H;
eapply (semax_call_id1_wow H);
 clear H;
 lazymatch goal with Frame := _ : list mpred |- _ => try clear Frame end;
 [check_result_type
 |apply Logic.I
 | match_postcondition
 | prove_delete_temp
 | unify_postcondition_exps
 | prove_PROP_preconditions
 ].

Ltac forward_call_id1_x_wow_nil :=
let H := fresh in intro H;
eapply (semax_call_id1_x_wow_nil H); 
 clear H;
 lazymatch goal with Frame := _ : list mpred |- _ => try clear Frame end;
 [ check_result_type | check_result_type
 | apply Coq.Init.Logic.I | apply Coq.Init.Logic.I | reflexivity
 | (clear; let H := fresh in intro H; inversion H)
 | match_postcondition
 | prove_delete_temp
 | prove_delete_temp
 | unify_postcondition_exps
 | prove_PROP_preconditions
 ].

Ltac forward_call_id1_x_wow :=
let H := fresh in intro H;
eapply (semax_call_id1_x_wow H); 
 clear H;
 lazymatch goal with Frame := _ : list mpred |- _ => try clear Frame end;
 [ check_result_type | check_result_type
 | apply Coq.Init.Logic.I | apply Coq.Init.Logic.I | reflexivity
 | (clear; let H := fresh in intro H; inversion H)
 | match_postcondition
 | prove_delete_temp
 | prove_delete_temp
 | unify_postcondition_exps
 | prove_PROP_preconditions
 ].

Ltac forward_call_id1_y_wow_nil :=
let H := fresh in intro H;
eapply (semax_call_id1_y_wow_nil H); 
 clear H;
 lazymatch goal with Frame := _ : list mpred |- _ => try clear Frame end;
 [ check_result_type | check_result_type
 | apply Coq.Init.Logic.I | apply Coq.Init.Logic.I | reflexivity
 | (clear; let H := fresh in intro H; inversion H)
 | match_postcondition
 | prove_delete_temp
 | prove_delete_temp
 | unify_postcondition_exps
 | prove_PROP_preconditions
 ].

Ltac forward_call_id1_y_wow :=
let H := fresh in intro H;
eapply (semax_call_id1_y_wow H); 
 clear H;
 lazymatch goal with Frame := _ : list mpred |- _ => try clear Frame end;
 [ check_result_type | check_result_type
 | apply Coq.Init.Logic.I | apply Coq.Init.Logic.I | reflexivity
 | (clear; let H := fresh in intro H; inversion H)
 | match_postcondition
 | prove_delete_temp
 | prove_delete_temp
 | unify_postcondition_exps
 | prove_PROP_preconditions
 ].

Ltac forward_call_id01_wow_nil :=
let H := fresh in intro H;
eapply (semax_call_id01_wow_nil H); 
 clear H;
 lazymatch goal with Frame := _ : list mpred |- _ => try clear Frame end;
 [ apply Coq.Init.Logic.I 
 | match_postcondition
 | unify_postcondition_exps
 | prove_PROP_preconditions
 ].

Ltac forward_call_id01_wow :=
let H := fresh in intro H;
eapply (semax_call_id01_wow H); 
 clear H;
 lazymatch goal with Frame := _ : list mpred |- _ => try clear Frame end;
 [ apply Coq.Init.Logic.I 
 | match_postcondition
 | unify_postcondition_exps
 | prove_PROP_preconditions
 ].

Ltac forward_call_id00_wow_nil  :=
let H := fresh in intro H;
eapply (semax_call_id00_wow_nil H); 
 clear H;
 lazymatch goal with Frame := _ : list mpred |- _ => try clear Frame end;
 [ check_result_type 
 | fix_up_simplified_postcondition;
    cbv beta iota zeta; unfold_post; (* extensionality rho; *)
    repeat rewrite exp_uncurry;

    (*Replaced to resolve GIT issue 385: 
      try rewrite no_post_exists0;
      (* apply equal_f; *)
      apply exp_congr*)
    first [ apply exp_congr | try rewrite no_post_exists0; apply exp_congr];

    intros ?vret;
    apply PROP_LOCAL_SEP_ext; [reflexivity | | reflexivity];
    (reflexivity || fail "The funspec of the function has a POSTcondition
that is ill-formed.  The LOCALS part of the postcondition
should be empty, but it is not")
 | unify_postcondition_exps
 | prove_PROP_preconditions
 ].

Ltac forward_call_id00_wow  :=
let H := fresh in intro H;
eapply (semax_call_id00_wow H); 
 clear H;
 lazymatch goal with Frame := _ : list mpred |- _ => try clear Frame end;
 [ check_result_type 
 | (*match_postcondition*)
    fix_up_simplified_postcondition;
    cbv beta iota zeta; unfold_post; (* extensionality rho; *)
    repeat rewrite exp_uncurry;

    (*Replaced to resolve GIT issue 385: 
      try rewrite no_post_exists0;
      (* apply equal_f; *)
      apply exp_congr*)
    first [ apply exp_congr | try rewrite no_post_exists0; apply exp_congr];

    intros ?vret;
    apply PROP_LOCAL_SEP_ext; [reflexivity | | reflexivity];
    (reflexivity || fail "The funspec of the function has a POSTcondition
that is ill-formed.  The LOCALS part of the postcondition
should be empty, but it is not")
 | unify_postcondition_exps
 | prove_PROP_preconditions
 ].

Ltac simpl_strong_cast :=
try match goal with |- context [strong_cast ?t1 ?t2 ?v] =>
  first [change (strong_cast t1 t2 v) with v
         | change (strong_cast t1 t2 v) with
                (force_val (sem_cast t1 t2 v))
          ]
end.

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

Local Definition dummy := I.

Ltac simplify_remove_localdef_temp :=
  match goal with |- context [remove_localdef_temp ?i ?L]  =>
    let u := constr:(remove_localdef_temp i L) in
    (* unfold remove_localdef_temp and do function and if/match conversion, 
      but do not expand the let in remove_localdef_temp, which would lead to exponential blow up *)
    let u' := eval lazy delta [remove_localdef_temp] beta iota in u in
    (* now fully simplify all terms with rlt_ident_eq as head symbol *)
    let u' := eval simpl rlt_ident_eq in u' in
    (* do another beta iota conversion to collapse all ifs *)
    let u' := eval lazy beta iota in u' in
    (* now all the correct branches have been selected and we can safely expand the lets *)
    let u' := eval lazy zeta in u' in
    (* Note: an explicit cast with "cbv delta [dummy]" does not improve performance *)
    change u with u'
  end.

Ltac after_forward_call :=
    check_POSTCONDITION; 
    try match goal with |- context [remove_localdef_temp] =>
              simplify_remove_localdef_temp
     end;
    unfold_app; 
    try (apply extract_exists_pre; intros _); 
    match goal with
        | |- semax _ _ _ _ => idtac
        | |- unit -> semax _ _ _ _ => intros _
    end;
    match goal with
        | |- @semax ?CS _ _ _ _ _ => try change_compspecs CS
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

Ltac check_witness_type ts A witness :=
  (unify A (rmaps.ConstType Ridiculous); (* because [is_evar A] doesn't seem to work *)
             elimtype False)
 ||
 let TA := constr:(functors.MixVariantFunctor._functor
     (rmaps.dependent_type_functor_rec ts A) mpred) in
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

Lemma trivial_Forall_inclusion:
 forall {A} (G: list A), Forall (fun x => In x G) G.
Proof.
intros.
apply Forall_forall; intros; auto.
Qed.

Lemma trivial_Forall_inclusion0:
 forall {A} (G: list A), Forall (fun x => In x G) nil.
Proof.
intros. constructor.
Qed.

Lemma classify_fun_ty_hack:
 (* This is needed for the varargs (printf) hack *)
  forall fs fs',
  funspec_sub fs fs' ->
  forall ty (*argsig*)typs retty cc,
  ty = type_of_funspec fs ->
  type_of_funspec fs' = Tfunction typs retty cc -> 
  classify_fun ty = fun_case_f typs retty cc.
Proof.
intros.
subst.
destruct fs, fs'. 
destruct H as [[? ?] _].
subst.
simpl in H1.
inv H1.
auto.
Qed.

Ltac check_type_of_funspec id :=
 reflexivity || 
 lazymatch goal with |- ?ty = ?tyfun =>
  let t' := eval simpl in tyfun in
    fail 100 "The type of identifier" id "in the program is" ty "which does not match the type of the funspec which is " t'
  end.

Ltac check_subsumes subsumes :=
 apply subsumes ||
 lazymatch goal with |- ?g =>
 lazymatch type of subsumes with ?t =>
  fail 100 "Function-call subsumption fails.  The term" subsumes "of type" t
     "does not prove the funspec_sub," g
 end end.

(*This has two cases; it priorizitizes func_ptr lookup over Delta-lookup*)
Ltac prove_call_setup1 subsumes :=
  match goal with
  | |- @semax _ _ _ (@exp _ _ _ _) _ _ =>
    fail 1 "forward_call fails because your precondition starts with EX.
Use Intros  to move          the existentially bound variables above the line"
  | |- @semax ?CS _ ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R'))) ?c _ =>
    let cR := (fun R =>
    match c with
    | context [Scall _ ?a ?bl] =>
      exploit (call_setup1_i CS Delta P Q (*R*) R' a bl);
      [check_prove_local2ptree
      |reflexivity
      |prove_func_ptr
      |check_subsumes subsumes
      |check_parameter_types
      |check_typecheck
      |check_typecheck
      |check_cast_params
      | ]
    | context [Scall _ (Evar ?id ?ty) ?bl] =>
      exploit (call_setup1_i2 CS Delta P Q R' id ty bl) ;
      [check_prove_local2ptree
      | apply can_assume_funcptr2;
        [ check_function_name
        | lookup_spec id
        | find_spec_in_globals'
        | check_type_of_funspec id
        ]
      |check_subsumes subsumes
      | try reflexivity; ((*idtac "found one"; *) eapply classify_fun_ty_hack; [apply subsumes| reflexivity ..])  (* function-id type in AST matches type in funspec *)
      |check_typecheck
      |check_typecheck
      |check_cast_params
      | ..
      ]
    end)
    in strip1_later R' cR
  end.

Ltac check_gvars :=
  first [exact Logic.I
         | reflexivity
         | match goal with |- check_gvars_spec None (Some ?gv) =>
              fail 100 "The function precondition requires (gvars" gv ")" "which is not present in your current assertion's LOCAL clause"
           end
         ].

Ltac try_convertPreElim := reflexivity.

Ltac prove_call_setup_aux  ts witness :=
 let H := fresh "SetupOne" in
 intro H;
 match goal with | |- @semax ?CS _ _ (PROPx ?P (LOCALx ?L (SEPx ?R'))) _ _ =>
 let Frame := fresh "Frame" in evar (Frame: list mpred); 
 let cR := (fun R =>
 exploit (call_setup2_i _ _ _ _ _ _ _ _ R R' _ _ _ _ ts _ _ _ _ _ _ _ H witness Frame); clear H;
 simpl functors.MixVariantFunctor._functor;
 [ try_convertPreElim
 | check_prove_local2ptree
 | check_vl_eq_args (*WAS: Forall_pTree_from_elements*)
 | auto 50 with derives
 | unfold check_gvars_spec; solve [exact I | reflexivity]
 | try change_compspecs CS; cancel_for_forward_call
 |
 ])
  in strip1_later R' cR
 end.

Ltac prove_call_setup ts subsumes witness :=
 prove_call_setup1 subsumes;
 [ .. | 
 match goal with |- call_setup1  _ _ _ _ _ _ _ _ _ _ _ _ _ ?A _ _ _ _ _ _  -> _ =>
      check_witness_type ts A witness
 end;
 prove_call_setup_aux ts witness].

Ltac fwd_call' ts subsumes witness :=
check_POSTCONDITION;
lazymatch goal with
| |- semax _ _ (Ssequence (Scall ?ret _ _) _) _ =>
  eapply semax_seq';
    [prove_call_setup ts subsumes witness;
     clear_Delta_specs; clear_MORE_POST;
     [ .. |
      lazymatch goal with
      | |- _ -> semax _ _ (Scall (Some _) _ _) _ =>
         forward_call_id1_wow
      | |- call_setup2 _ _ _ _ _ _ _ _ _ _ _ _ ?retty _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> 
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
         [prove_call_setup ts subsumes witness;
          clear_Delta_specs; clear_MORE_POST;
             [ .. | forward_call_id1_x_wow ]
         |  after_forward_call ]
| |- semax _ _ (Ssequence (Ssequence (Scall (Some ?ret') _ _)
                                       (Sset _ (Etempvar ?ret'2 _))) _) _ =>
       unify ret' ret'2;
       eapply semax_seq';
         [prove_call_setup ts subsumes witness;
          clear_Delta_specs; clear_MORE_POST;
             [ .. | forward_call_id1_y_wow ]
         |  after_forward_call ]
| |- _ => rewrite <- seq_assoc; fwd_call' ts subsumes witness
end.

Ltac fwd_call_dep ts subsumes witness :=
 try lazymatch goal with
      | |- semax _ _ (Scall _ _ _) _ => rewrite -> semax_seq_skip
      end;
 repeat lazymatch goal with
  | |- semax _ _ (Ssequence (Ssequence (Ssequence _ _) _) _) _ =>
      rewrite <- seq_assoc
 end;
lazymatch goal with |- @semax ?CS _ ?Delta _ (Ssequence ?C _) _ =>
  lazymatch C with context [Scall _ _ _] =>
         fwd_call' ts subsumes witness
    end
end.

Tactic Notation "forward_call" constr(ts) constr(subsumes) constr(witness) :=
    fwd_call_dep ts subsumes witness.

Tactic Notation "forward_call" constr(witness) :=
    fwd_call_dep (@nil Type) funspec_sub_refl witness.

Tactic Notation "forward_call" constr(subsumes) constr(witness) := 
  fwd_call_dep (@nil Type) subsumes witness.

Ltac tuple_evar2 name T cb evar_tac :=
  lazymatch T with
  | prod ?A ?B => tuple_evar2 name A
    ltac: (fun xA =>
      tuple_evar2 name B ltac: (fun xB =>
        cb (xA, xB)) evar_tac) evar_tac
  | _ => my_unshelve_evar name T cb evar_tac
  end; idtac.

Ltac get_function_witness_type func :=
 let TA := constr:(functors.MixVariantFunctor._functor
     (rmaps.dependent_type_functor_rec nil func) mpred) in
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
 in TA''.

Ltac new_prove_call_setup :=
 prove_call_setup1 funspec_sub_refl;
 [ .. | 
 match goal with |- call_setup1 _ _ _ _ _ _ _ _ _ (*_*) _ _ _ _ ?A _ _ _ _ _ _ (*OMITTED _*) -> _ =>
      let x := fresh "x" in tuple_evar2 x ltac:(get_function_witness_type A)
      ltac:(prove_call_setup_aux (@nil Type))
      ltac:(fun _ => try refine tt; fail "Failed to infer some parts of witness")
 end].

Ltac new_fwd_call' :=
lazymatch goal with
| |- semax _ _ (Ssequence (Scall _ _ _) _) _ =>
  eapply semax_seq';
    [new_prove_call_setup;
     clear_Delta_specs; clear_MORE_POST;
     [ .. |
      lazymatch goal with
      | |- _ -> semax _ _ (Scall (Some _) _ _) _ =>
         forward_call_id1_wow
      | |- call_setup2 _ _ _ _ _ _ _ _ _ _ _ _ ?retty _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (*_*) ->
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
         [new_prove_call_setup;
          clear_Delta_specs; clear_MORE_POST;
             [ .. | forward_call_id1_x_wow ]
         |  after_forward_call ]
| |- semax _ _ (Ssequence (Ssequence (Scall (Some ?ret') _ _)
                                       (Sset _ (Etempvar ?ret'2 _))) _) _ =>
       unify ret' ret'2;
       eapply semax_seq';
         [new_prove_call_setup;
          clear_Delta_specs; clear_MORE_POST;
             [ .. | forward_call_id1_y_wow ]
         |  after_forward_call ]
| |- _ => rewrite <- seq_assoc; new_fwd_call'
end.


Ltac new_fwd_call:=
 try lazymatch goal with
      | |- semax _ _ (Scall _ _ _) _ => rewrite -> semax_seq_skip
      end;
 repeat lazymatch goal with
  | |- semax _ _ (Ssequence (Ssequence (Ssequence _ _) _) _) _ =>
      rewrite <- seq_assoc
 end;
lazymatch goal with |- @semax ?CS _ ?Delta _ (Ssequence ?C _) _ =>
  lazymatch C with context [Scall _ _ _] =>
         new_fwd_call'
    end
end.

Tactic Notation "forward_call"  := new_fwd_call.

Lemma seq_assoc2:
  forall (Espec: OracleKind) {cs: compspecs}  Delta P c1 c2 c3 c4 Q,
  semax Delta P (Ssequence (Ssequence c1 c2) (Ssequence c3 c4)) Q ->
  semax Delta P (Ssequence (Ssequence (Ssequence c1 c2) c3) c4) Q.
Proof.
intros.
 rewrite <- seq_assoc. auto.
Qed.

(* solve msubst_eval_expr, msubst_eval_lvalue, msubst_eval_LR *)
Ltac solve_msubst_eval :=
    let e := match goal with
       | |- msubst_eval_expr _ _ _ _ ?a = _ => a
       | |- msubst_eval_lvalue _ _ _ _ ?a = _ => a
    end in
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
         | Vptr _ _ => Vptr _ (Ptrofs.add _ (Ptrofs.repr ?ofs))
         end)
         => change E with (offset_val ofs E'')
       | _ => change E with E'
       end
     | |- ?NotSome = Some _ => 
             fail 1000 "The C-language expression " e
                 " does not necessarily evaluate, perhaps because some variable is missing from your LOCAL clause"

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

Lemma do_compute_expr_helper_lemma:
 forall {cs: compspecs} Delta P Q R v e T1 T2 GV,
 local2ptree Q = (T1,T2,nil,GV) ->
 msubst_eval_expr Delta T1 T2 GV e = Some v ->
 ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- 
   local (liftx (eq v) (eval_expr e)).
Proof.
intros.
eapply derives_trans;
 [ |  apply (go_lower_localdef_canon_eval_expr
 _ P Q R _ _ _ _ v v H H0)].
apply andp_right; auto.
intro.
apply prop_right; auto.
Qed.

Ltac do_compute_expr_helper_old Delta Q v e :=
   try assumption;
   eapply derives_trans; [| apply msubst_eval_expr_eq];
    [apply andp_derives; [apply derives_refl | apply derives_refl']; apply local2ptree_soundness; try assumption;
     let HH := fresh "H" in
     construct_local2ptree Q HH;
     exact HH |
     unfold v;
     cbv [msubst_eval_expr msubst_eval_lvalue]; 
     repeat match goal with |- context [PTree.get ?a ?b] => 
             let u := constr:(PTree.get a b) in
             let u' := eval hnf in u in
             match u' with Some ?v' => let v := fresh "v" in pose (v:=v');
                         change u with (Some v)
            end
      end;
(* match goal with |- ?a => idtac "ONE:" a end; *)
     simpl;  (* This 'simpl' should be safe because user's terms have been removed *)
(* match goal with |- ?a => idtac "TWO:" a end; *)
     unfold force_val2, force_val1;
      (apply (f_equal Some) || fail 100 "Cannot evaluate expression " e "Possibly there are missing local declarations.");
     simpl;
    repeat match goal with v:=_ |- _ => subst v end;
(*     match goal with |- ?a => idtac "THREE:" a end; *)
     reflexivity].

Ltac do_compute_expr_helper Delta Q v e :=
 try assumption;
 eapply do_compute_expr_helper_lemma;
 [   prove_local2ptree
 | unfold v;
   cbv [msubst_eval_expr msubst_eval_lvalue];
     repeat match goal with |- context [PTree.get ?a ?b] => 
             let u := constr:(PTree.get a b) in
             let u' := eval hnf in u in
             match u' with Some ?v' => let v := fresh "v" in pose (v:=v');
                         change u with (Some v)
            end
      end;
(* match goal with |- ?a => idtac "ONE:" a end; *)
     simpl;  (* This 'simpl' should be safe because user's terms have been removed *)
(* match goal with |- ?a => idtac "TWO:" a end; *)
     unfold force_val2, force_val1;
     (apply (f_equal Some) || fail 100 "Cannot evaluate expression " e "Possibly there are missing local declarations.");
     simpl;
    repeat match goal with v:=_ |- _ => subst v end;
(*      [ match goal with |- ?A => fail "here" A end ]; *)
     reflexivity
 ].

Ltac do_compute_expr1 Delta Pre e :=
 lazymatch Pre with
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
     by (let a := fresh "a" in intro a; do_compute_expr_helper Delta (Q a) v e)
 | PROPx ?P (LOCALx ?Q (SEPx ?R)) =>
  let H9 := fresh "H" in
  let v := fresh "v" in evar (v: val);
  assert (H9:  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R))|--
                     local (`(eq v) (eval_expr e)))
   by (do_compute_expr_helper Delta Q v e)
 end.

Lemma int64_eq_e: forall i, Int64.eq i Int64.zero = true -> i=Int64.zero.
Proof.
intros.
pose proof (Int64.eq_spec i Int64.zero). rewrite H in H0; auto.
Qed.

Lemma ptrofs_eq_e: forall i, Ptrofs.eq i Ptrofs.zero = true -> i=Ptrofs.zero.
Proof.
intros.
pose proof (Ptrofs.eq_spec i Ptrofs.zero). rewrite H in H0; auto.
Qed.

Lemma typed_true_Cne_neq: 
  forall x y, 
    typed_true tint (force_val (sem_cmp_pp Cne x y)) -> x <> y.
Proof.
  intros. hnf in H. destruct x, y; try inversion H.
  - unfold sem_cmp_pp, strict_bool_val, Val.cmplu_bool, Val.cmpu_bool in H.
    destruct Archi.ptr64 eqn:Hp; simpl in H; 
    try destruct (Int64.eq i i0) eqn:?;
    try destruct (Int.eq i i0) eqn:?;
    simpl in H; try inversion H.
    intro. 
    inversion H0. subst i. 
    try pose proof (Int64.eq_spec i0 i0). 
    try pose proof (Int.eq_spec i0 i0). 
    rewrite Heqb in *.
    contradiction. 
  - intro. inversion H0.
  - intro. inversion H0.
  - unfold sem_cmp_pp in H. simpl in H.
    destruct (eq_block b b0).
    + destruct (Ptrofs.eq i i0) eqn:? .
      * simpl in H. pose proof (Ptrofs.eq_spec i i0). rewrite Heqb1 in H0.
        subst b i. inversion H.  
      * intro. inversion H0.
        subst i.
        pose proof (Ptrofs.eq_spec i0 i0). rewrite Heqb1 in H2.
        contradiction.  
    + intro. inversion H0. subst b. contradiction.
Qed.

Lemma typed_true_Ceq_eq: 
  forall x y, 
    typed_true tint (force_val (sem_cmp_pp Ceq x y)) -> x = y.
Proof.
  intros. hnf in H. destruct x, y; try inversion H.
  - unfold sem_cmp_pp, strict_bool_val, Val.cmplu_bool, Val.cmpu_bool in H;
    destruct Archi.ptr64 eqn:Hp; simpl in H; 
    try destruct (Int64.eq i i0) eqn:?; 
    try destruct (Int.eq i i0) eqn:?; 
    simpl in H; try inversion H.
    f_equal.
    try pose proof (Int64.eq_spec i i0).
    try pose proof (Int.eq_spec i i0).
    rewrite Heqb in *. auto.
  - unfold sem_cmp_pp, strict_bool_val, Val.cmplu_bool, Val.cmpu_bool in H;
    destruct Archi.ptr64 eqn:Hp; simpl in H;
    try destruct (Int64.eq i Int64.zero) eqn:?; 
    try destruct (Int.eq i Int.zero) eqn:?; 
    simpl in H; try inversion H.
  - unfold sem_cmp_pp, strict_bool_val, Val.cmplu_bool, Val.cmpu_bool in H;
    destruct Archi.ptr64 eqn:Hp; simpl in H;
    try destruct (Int64.eq i0 Int64.zero) eqn:?; 
    try destruct (Int.eq i0 Int.zero) eqn:?; 
    simpl in H; try inversion H.
  - unfold sem_cmp_pp in H. simpl in H.
    destruct (eq_block b b0) eqn:E.
    + subst b. 
      destruct (Ptrofs.eq i i0) eqn:E'.
      * pose proof (Ptrofs.eq_spec i i0). rewrite E' in H0. subst i.
        reflexivity.
      * simpl in H. inversion H.
    + simpl in H. inversion H.
Qed.

Lemma typed_false_Cne_eq: 
  forall x y, 
    typed_false tint (force_val (sem_cmp_pp Cne x y)) -> x = y.
Proof.
  intros. hnf in H. destruct x, y; try inversion H.
  - unfold sem_cmp_pp, strict_bool_val, Val.cmplu_bool, Val.cmpu_bool in H;
    destruct Archi.ptr64 eqn:Hp; simpl in H; 
    try destruct (Int64.eq i i0) eqn:?; 
    try destruct (Int.eq i i0) eqn:?; 
    simpl in H; try inversion H.
    f_equal.
    try pose proof (Int64.eq_spec i i0).
    try pose proof (Int.eq_spec i i0).
    rewrite Heqb in *. auto.
  - unfold sem_cmp_pp, strict_bool_val, Val.cmplu_bool, Val.cmpu_bool in H;
    destruct Archi.ptr64 eqn:Hp; simpl in H;
    try destruct (Int64.eq i Int64.zero) eqn:?; 
    try destruct (Int.eq i Int.zero) eqn:?; 
    simpl in H; try inversion H.
  - unfold sem_cmp_pp, strict_bool_val, Val.cmplu_bool, Val.cmpu_bool in H;
    destruct Archi.ptr64 eqn:Hp; simpl in H;
    try destruct (Int64.eq i0 Int64.zero) eqn:?; 
    try destruct (Int.eq i0 Int.zero) eqn:?; 
    simpl in H; try inversion H.
  - unfold sem_cmp_pp in H. simpl in H.
    destruct (eq_block b b0).
    + destruct (Ptrofs.eq i i0) eqn:? .
      * simpl in H. pose proof (Ptrofs.eq_spec i i0). rewrite Heqb1 in H0.
        subst b i. reflexivity.  
      * simpl in H. inversion H.
    + simpl in H. inversion H.
Qed.

Lemma typed_false_Ceq_neq: 
  forall x y, 
    typed_false tint (force_val (sem_cmp_pp Ceq x y)) -> x <> y.
Proof.
  intros. hnf in H. destruct x, y; try inversion H. 
  - unfold sem_cmp_pp, strict_bool_val, Val.cmplu_bool, Val.cmpu_bool in H.
    destruct Archi.ptr64 eqn:Hp; simpl in H; 
    try destruct (Int64.eq i i0) eqn:?;
    try destruct (Int.eq i i0) eqn:?;
    simpl in H; try inversion H.
    intro. 
    inversion H0. subst i. 
    try pose proof (Int64.eq_spec i0 i0). 
    try pose proof (Int.eq_spec i0 i0). 
    rewrite Heqb in *.
    contradiction. 
  - intro. inversion H0.
  - intro. inversion H0.
  - unfold sem_cmp_pp in H. simpl in H.
    destruct (eq_block b b0).
    + destruct (Ptrofs.eq i i0) eqn:? .
      * simpl in H. pose proof (Ptrofs.eq_spec i i0). rewrite Heqb1 in H0.
        subst b i. inversion H.
      * intro. inversion H0. subst b i. pose proof (Ptrofs.eq_spec i0 i0). 
        rewrite Heqb1 in H2. contradiction.
    + intro. inversion H0. contradiction. 
Qed.

Corollary typed_true_nullptr3:
  forall p,
  typed_true tint (force_val (sem_cmp_pp Ceq p nullval)) ->
  p=nullval.
Proof.
  intros p.
  apply (typed_true_Ceq_eq p nullval).
Qed.

Corollary typed_false_nullptr3:
  forall p,
  typed_false tint (force_val (sem_cmp_pp Ceq p nullval)) ->
  p<>nullval.
Proof.
  intros p.
  apply (typed_false_Ceq_neq p nullval).
Qed.

Corollary typed_true_nullptr4:
  forall p,
  typed_true tint (force_val (sem_cmp_pp Cne p nullval)) ->
  p <> nullval.
Proof.
  intros p.
  apply (typed_true_Cne_neq p nullval).
Qed.

Corollary typed_false_nullptr4:
  forall p,
  typed_false tint (force_val (sem_cmp_pp Cne p nullval)) ->
  p=nullval.
Proof.
  intros p.
  apply (typed_false_Cne_eq p nullval).
Qed.

Ltac cleanup_repr H :=
rewrite ?mul_repr, ?add_repr, ?sub_repr in H;
match type of H with
 | _ (Int.signed (Int.repr ?A)) (Int.signed (Int.repr ?B)) =>
    try (rewrite (Int.signed_repr A) in H by rep_lia);
    try (rewrite (Int.signed_repr B) in H by rep_lia)
 | _ (Int.unsigned (Int.repr ?A)) (Int.unsigned (Int.repr ?B)) =>
    try (rewrite (Int.unsigned_repr A) in H by rep_lia);
    try (rewrite (Int.unsigned_repr B) in H by rep_lia)
 | context [Int.signed (Int.repr ?A) ] =>
    try (rewrite (Int.signed_repr A) in H by rep_lia)
 | context [Int.unsigned (Int.repr ?A) ] =>
    try (rewrite (Int.unsigned_repr A) in H by rep_lia)
end.

Lemma typed_true_ptr_e:
 forall t v, typed_true (tptr t) v -> isptr v.
Proof.
  intros.
  unfold typed_true, strict_bool_val, tptr in H.
  destruct v; match type of H with | None = Some true => inv H | _ => idtac end.
  + destruct Archi.ptr64 eqn:Hp; destruct (Int.eq i Int.zero); inv H.
  + destruct Archi.ptr64 eqn:Hp; destruct (Int64.eq i Int64.zero); inv H.
  + apply Coq.Init.Logic.I.
Qed.

Lemma typed_false_ptr_e:
 forall t v, typed_false (tptr t) v -> v=nullval.
Proof.
 intros. destruct v; inv H; try apply Coq.Init.Logic.I.
unfold nullval.
(*destruct Archi.ptr64; try discriminate.*)
f_equal.
try (pose proof (Int64.eq_spec i Int64.zero);
      destruct (Int64.eq i Int64.zero); inv H1; auto);
try (pose proof (Int.eq_spec i Int.zero);
      destruct (Int.eq i Int.zero); inv H1; auto).
Qed.

Lemma repr_neq_e:
 forall i j, Int.repr i <> Int.repr j -> i <> j.
Proof. intros. contradict H. subst. auto. Qed.

Lemma repr64_neq_e:
 forall i j, Int64.repr i <> Int64.repr j -> i <> j.
Proof. intros. contradict H. subst. auto. Qed.

Lemma Byte_signed_lem: 
 forall b,
  (Byte.signed b = 0) = (b = Byte.zero).
Proof.
intros.
apply prop_ext; split; intro.
rewrite <- (Byte.repr_signed b). rewrite H; reflexivity.
rewrite <- Byte.signed_repr by rep_lia.
f_equal; auto.
Qed.
Hint Rewrite Byte_signed_lem: norm entailer_rewrite.

Lemma Byte_signed_lem': 
 forall b c,
  (Byte.signed b = Byte.signed c) = (b = c).
Proof.
intros.
apply prop_ext; split; intro.
rewrite <- (Byte.repr_signed b).
rewrite <- (Byte.repr_signed c).
 rewrite H; reflexivity.
congruence.
Qed.
Hint Rewrite Byte_signed_lem': norm entailer_rewrite.

Lemma int_repr_byte_signed_eq0:
  forall c, (Int.repr (Byte.signed c) = Int.zero) = (c = Byte.zero).
Proof.
intros.
apply prop_ext; split; intro.
apply repr_inj_signed in H; try rep_lia.
rewrite <- (Byte.repr_signed c). rewrite H. reflexivity.
subst; reflexivity.
Qed.
Hint Rewrite int_repr_byte_signed_eq0: norm entailer_rewrite.

Lemma int_repr_byte_signed_eq:
  forall c d, (Int.repr (Byte.signed c) = Int.repr (Byte.signed d)) = (c = d).
Proof.
intros.
apply prop_ext; split; intro.
apply repr_inj_signed in H; try rep_lia.
rewrite <- (Byte.repr_signed c). 
rewrite <- (Byte.repr_signed d). rewrite H. reflexivity.
subst; reflexivity.
Qed.
Hint Rewrite int_repr_byte_signed_eq: norm entailer_rewrite.

Lemma typed_true_negb_bool_val_p:
  forall p, 
   typed_true tint
      (force_val
         (option_map (fun b : bool => Val.of_bool (negb b))
            (bool_val_p p))) ->
     p = nullval.
Proof.
intros. destruct p; inv H.
destruct Archi.ptr64 eqn:Hp;
(simpl in H1;
try (pose proof (Int64.eq_spec i Int64.zero);
      destruct (Int64.eq i Int64.zero); inv H1; auto);
try (pose proof (Int.eq_spec i Int.zero);
      destruct (Int.eq i Int.zero); inv H1; auto)).
Qed.

Lemma typed_false_negb_bool_val_p:
  forall p, 
   is_pointer_or_null p ->
   typed_false tint
      (force_val
         (option_map (fun b : bool => Val.of_bool (negb b))
            (bool_val_p p))) ->
     isptr p.
Proof.
intros. destruct p; try solve [inv H0]; auto; rename H0 into H1.
simpl in H.
simpl.
destruct Archi.ptr64 eqn:Hp;
(simpl in H1;
try (pose proof (Int64.eq_spec i Int64.zero);
      destruct (Int64.eq i Int64.zero); inv H1; auto);
try (pose proof (Int.eq_spec i Int.zero);
      destruct (Int.eq i Int.zero); inv H1; auto)).
Qed.

Lemma typed_false_negb_bool_val_p':
  forall p : val,
  typed_false tint
    (force_val (option_map (fun b : bool => Val.of_bool (negb b)) (bool_val_p p))) ->
   p <> nullval.
Proof.
 intros. intro; subst. discriminate.
Qed.

Ltac do_repr_inj H :=
   simpl typeof in H;  (* this 'simpl' should be fine, since its argument is just clightgen-produced ASTs *)
  try first [apply typed_true_of_bool in H
               |apply typed_false_of_bool in H
               | apply typed_true_ptr in H
               | apply typed_false_ptr_e in H
               | apply typed_true_negb_bool_val_p in H
               | apply typed_false_negb_bool_val_p in H; [| solve [auto]]
               | apply typed_false_negb_bool_val_p' in H
               | unfold nullval in H; (*simple*) apply typed_true_tint_Vint in H
               | unfold nullval in H; (*simple*) apply typed_false_tint_Vint in H
               ];
   rewrite ?ptrofs_to_int_repr in H;
   rewrite ?ptrofs_to_int64_repr in H by reflexivity;
   repeat (rewrite -> negb_true_iff in H || rewrite -> negb_false_iff in H);
   try apply int_eq_e in H;
   try apply int64_eq_e in H;
   try apply ptrofs_eq_e in H;
   match type of H with
(*  don't do these, because they weaken the statement, unfortunately.
          | _ <> _ => apply repr_neq_e (*int_eq_false_e*) in H
          | _ <> _ => apply repr64_neq_e in H
*)
          | _ <> _ => let H' := fresh H "'" in assert (H' := repr_neq_e _ _ H)
          | _ <> _ => let H' := fresh H "'" in assert (H' := repr64_neq_e _ _ H)
          | Int.eq _ _ = false => apply int_eq_false_e in H
          | Int64.eq _ _ = false => apply int64_eq_false_e in H
          | Ptrofs.eq _ _ = false => apply ptrofs_eq_false_e in H
          | _ => idtac
  end;
  first [ simple apply repr_inj_signed in H; [ | rep_lia | rep_lia ]
         | simple apply repr_inj_unsigned in H; [ | rep_lia | rep_lia ]
         | simple apply repr_inj_signed' in H; [ | rep_lia | rep_lia ]
         | simple apply repr_inj_unsigned' in H; [ | rep_lia | rep_lia ]
         | match type of H with
            | typed_true _  (force_val (sem_cmp_pp Ceq _ _)) =>
                                    try apply typed_true_nullptr3 in H;
                                    try apply typed_true_Ceq_eq in H
            | typed_true _  (force_val (sem_cmp_pp Cne _ _)) =>
                                    try apply typed_true_nullptr4 in H;
                                    try apply typed_true_Cne_neq in H
            | typed_false _  (force_val (sem_cmp_pp Ceq _ _)) =>
                                    try apply typed_false_nullptr3 in H;
                                    try apply typed_false_Ceq_neq in H
            | typed_false _  (force_val (sem_cmp_pp Cne _ _)) =>
                                    try apply typed_false_nullptr4 in H;
                                    try apply typed_false_Cne_eq in H
          end
         | apply typed_false_nullptr4 in H
         | simple apply ltu_repr in H; [ | rep_lia | rep_lia]
         | simple apply ltu_repr64 in H; [ | rep_lia | rep_lia]
         | simple apply ltu_repr_false in H; [ | rep_lia | rep_lia]
         | simple apply ltu_repr_false64 in H; [ | rep_lia | rep_lia]
         | simple apply ltu_inv in H; cleanup_repr H
         | simple apply ltu_inv64 in H; cleanup_repr H
         | simple apply ltu_false_inv in H; cleanup_repr H
         | simple apply ltu_false_inv64 in H; cleanup_repr H
         | simple apply lt_repr in H; [ | rep_lia | rep_lia]
         | simple apply lt_repr64 in H; [ | rep_lia | rep_lia]
         | simple apply lt_repr_false in H; [ | rep_lia | rep_lia]
         | simple apply lt_repr_false64 in H; [ | rep_lia | rep_lia]
         | simple apply lt_inv in H; cleanup_repr H
         | simple apply lt_inv64 in H; cleanup_repr H
         | simple apply lt_false_inv in H; cleanup_repr H
         | simple apply lt_false_inv64 in H; cleanup_repr H
         | idtac
         ];
    rewrite ?Byte_signed_lem, ?Byte_signed_lem',
                 ?int_repr_byte_signed_eq0, ?int_repr_byte_signed_eq0
      in H.

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

Fixpoint nobreaksx (s: statement) : bool :=
match s with
| Sbreak => false
| Scontinue => false
| Ssequence c1 c2 => nobreaksx c1 && nobreaksx c2
| Sifthenelse _ c1 c2 => nobreaksx c1 && nobreaksx c2
| _ => true  (* including Sloop case! *)
end.

Ltac forward_while_advise_loop :=
      idtac "Suggestion: Because your while-loop is followed by a known postcondition, you may wish to prove it with forward_loop instead of forward_while, because then your postcondition might be weaker (easier to prove) than the standard while-loop postcondition (Invariant & ~test)".

Tactic Notation "forward_while" constr(Inv) :=
  repeat (apply -> seq_assoc; abbreviate_semax);
  match goal with
  | |- semax _ _ (Ssequence _ _) _ => idtac 
  | Post := @abbreviate ret_assert ?P' |- semax _ _ (Swhile _ _) ?P =>
       constr_eq P Post;
       tryif (no_evars P') then forward_while_advise_loop else idtac;
      apply <- semax_seq_skip
  | |- semax _ _ (Swhile _ _) ?P => 
       tryif (no_evars P) then forward_while_advise_loop else idtac;
      apply <- semax_seq_skip
  | _ => apply <- semax_seq_skip 
  end;
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
      [match goal with |- semax ?Delta ?Pre (Swhile ?e ?s) _ =>
        tryif (unify (nobreaksx s) true) then idtac 
        else fail "Your while-loop has a break command in the body.  Therefore, you should use forward_loop to prove it, since the standard while-loop postcondition (Invariant & ~test) may not hold at the break statement";
        (* the following line was before: eapply semax_while_3g1; *)
        match goal with [ |- semax _ (@exp _ _ ?A _) _ _ ] => eapply (@semax_while_3g1 _ _ A) end;
        (* check if we can revert back to the previous version with coq 8.5.
           (as of December 2015 with compcert 2.6 the above fix is still necessary)
           The bug happens when we destruct the existential variable of the loop invariant:

             (* example.c program: *)
             int main(){int i=0; while(i);}

             (* verif_example.v file (+you have to Require Import the example.v file produced by clightgen) *)
             Require Import VST.floyd.proofauto.
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
        simpl typeof;  (* this 'simpl' should be fine, since its argument is just clightgen-produced ASTs *)
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
       | apply extract_exists_pre; special_intros_EX;
         let HRE := fresh "HRE" in apply semax_extract_PROP; intro HRE;
         do_repr_inj HRE;
         repeat (apply semax_extract_PROP; intro);
         normalize in HRE
       ]
    ]; abbreviate_semax; 
    simpl_ret_assert (*autorewrite with ret_assert*).

Inductive Type_of_invariant_in_forward_for_should_be_environ_arrow_mpred_but_is : Type -> Prop := .
Inductive Type_of_bound_in_forward_for_should_be_Z_but_is : Type -> Prop := .

Ltac check_type_forward_for_simple_bound :=
   match goal with |- semax _ _ ?c _ => 
         let x := constr:(match c with (Ssequence _ (Sloop _ (Sset _ e))) => Some (typeof e) | _ => None end) in
         let x := eval hnf in x in
         let x := eval simpl in x in   (* this 'simpl' should be safe enough  *)
         match x with
         | None => idtac
         | Some ?t => 
             unify (is_int32_type t) true
             + fail 100 "At present, forward_for_simple_bound works only on iteration variables that are (signed or unsigned) int, but your iteration variable has type" t
         end
     end.

Ltac forward_for_simple_bound n Pre :=
  check_Delta; check_POSTCONDITION;
 repeat match goal with |-
      semax _ _ (Ssequence (Ssequence (Ssequence _ _) _) _) _ =>
      apply -> seq_assoc; abbreviate_semax
 end;
 match goal with |-
      semax _ _ (Ssequence (Ssequence (Sfor _ _ _ _) _) _) _ =>
      apply -> seq_assoc; abbreviate_semax
 | _ => idtac
 end;
 match type of n with
      ?t => tryif (unify t Z) then idtac 
               else fail "Type of bound" n "should be Z but is" t
 end;
 match type of Pre with
 | ?t => tryif (unify t (environ->mpred)) then idtac 
               else fail "Type of precondition" Pre "should be environ->mpred but is" t
  end;
 match goal with
    | |- semax _ _ (Sfor _ _ _ _) _ =>
           rewrite semax_seq_skip
    | |- semax _ _ (Ssequence _ (Sloop _ _)) _ =>
           rewrite semax_seq_skip
    | |- semax _ _ (Ssequence _ ?MORE_COMMANDS) _ =>
        revert MORE_COMMANDS;
        match goal with
        | |- let MORE_COMMANDS := @abbreviate _ (Sloop _ _) in _ =>
            intros MORE_COMMANDS;
            rewrite semax_seq_skip
        end
    | _ => idtac
    end;
    forward_for_simple_bound'' n Pre; [.. | abbreviate_semax; cbv beta; try fwd_skip].

Ltac forward_for3 Inv PreInc Postcond :=
   apply semax_seq with Postcond;
       [ eapply semax_for_3g1 with (PQR:=PreInc);
        [ reflexivity
        |intro  
        | intro ;
          match goal with |- ENTAIL ?Delta, ?Pre |-- local (liftx (eq _) (eval_expr ?e)) =>
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
            match goal with
            | |- context [RA_normal (overridePost ?P ?Post)] => change (RA_normal (overridePost ?P ?Post)) with P
            end ]
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
          match goal with |- ENTAIL ?Delta, ?Pre |-- local (liftx (eq _) (eval_expr ?e)) =>
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

Lemma semax_loop_noincr :
  forall {Espec: OracleKind}{CS: compspecs} ,
forall Delta Q body R,
     @semax CS Espec Delta  Q body (loop1_ret_assert Q R) ->
     @semax CS Espec Delta Q (Sloop body Sskip) R.
Proof.
intros.
apply semax_loop with Q; auto.
eapply semax_post_flipped.
apply semax_skip.
all: try (simpl; intros; apply andp_left2; destruct R; try apply derives_refl; apply FF_left).
Qed.

Lemma semax_post1: forall R' Espec {cs: compspecs} Delta R P c,
           ENTAIL Delta, R' |-- RA_normal R ->
      @semax cs Espec Delta P c (overridePost R' R) ->
      @semax cs Espec Delta P c R.
Proof. intros. eapply semax_post; try apply H0.
 destruct R; apply H.
 all: intros; destruct R; apply andp_left2; apply derives_refl.
Qed.

Lemma semax_post1_flipped: forall R' Espec {cs: compspecs} Delta R P c,
      @semax cs Espec Delta P c (overridePost R' R) ->
         ENTAIL Delta, R' |-- RA_normal R ->
      @semax cs Espec Delta P c R.
Proof. intros. apply semax_post1 with R'; auto. Qed.

Lemma semax_skip_seq1:
  forall {Espec: OracleKind} {CS: compspecs} Delta P s1 s2 Q,
   semax Delta P (Ssequence s1 s2) Q ->
   semax Delta P (Ssequence (Ssequence Sskip s1) s2) Q.
Proof.
intros. apply seq_assoc1. apply -> semax_skip_seq. auto.
Qed.

Ltac delete_skip :=
 repeat apply -> semax_skip_seq;
 try apply semax_skip_seq1.

Ltac forward_loop_aux2 Inv PreInc :=
 lazymatch goal with
  | |- semax _ _ (Sloop _ Sskip) _ => 
         tryif (constr_eq Inv PreInc) then (apply (semax_loop_noincr _ Inv); abbreviate_semax)
         else (apply (semax_loop _ Inv PreInc); [delete_skip | ]; abbreviate_semax)
  | |- semax _ _ (Sloop _ _) _ =>apply (semax_loop _ Inv PreInc); [delete_skip | ]; abbreviate_semax
 end.

Ltac forward_loop_aux1 Inv PreInc:=
  lazymatch goal with
  | |- semax _ _ (Sfor _ _ _ _) _ => apply semax_seq' with Inv; [abbreviate_semax | forward_loop_aux2 Inv PreInc]
  | |- semax _ _ (Sloop _ _) _ => apply semax_pre with Inv; [ | forward_loop_aux2 Inv PreInc]
  | |- semax _ _ (Swhile ?E ?B) _ => 
          let x := fresh "x" in set (x := Swhile E B); hnf in x; subst x;
          apply semax_pre with Inv; [ | forward_loop_aux2 Inv PreInc]
 end.
 
Tactic Notation "forward_loop" constr(Inv) "continue:" constr(PreInc) "break:" constr(Post) :=
check_POSTCONDITION;
  repeat simple apply seq_assoc1;
 repeat apply -> semax_seq_skip;
  match goal with
  | |- semax _ _ (Ssequence (Sloop _ _) _) _ => 
          apply semax_seq with Post; [forward_loop_aux1 Inv PreInc | abbreviate_semax ]
  | |- semax _ _ (Ssequence (Sfor _ _ _ _) _) _ => 
          apply semax_seq with Post; [forward_loop_aux1 Inv PreInc | abbreviate_semax ]
  | |- semax _ _ (Ssequence (Swhile _ _) _) _ => 
          apply semax_seq with Post; [forward_loop_aux1 Inv PreInc | abbreviate_semax ]
  | |- semax _ _ _ ?Post' => 
            tryif (unify Post Post') then forward_loop_aux1 Inv PreInc 
           else (apply (semax_post1_flipped Post); [ forward_loop_aux1 Inv PreInc | ])
  end.

Ltac check_no_incr S :=
 let s' := eval hnf in S in 
 match s' with
 | Ssequence ?x _ => check_no_incr x
 | Sloop _ ?inc => let i' := eval hnf in inc in match i' with Sskip => idtac end
 | Sloop _ _ => fail 100 "Your loop has an increment statement, so your forward_loop must have a continue: invariant"
 | Sfor _ _ ?inc _ => let i' := eval hnf in inc in match i' with Sskip => idtac end
 | Sfor _ _ _ _ => fail 100 "Your loop has an increment statement, so your forward_loop must have a continue: invariant"
 | _ => fail 100 "applied forward_loop to something that is not a loop"
end.

Tactic Notation "forward_loop" constr(Inv) "continue:" constr(PreInc) :=
check_POSTCONDITION;
 repeat apply -> semax_seq_skip;
lazymatch goal with
  | |- semax _ _ (Ssequence (Sloop _ _) _) _ =>
         fail 100 "Your loop is followed by more statements, so you must use the form of forward_loop with the break: keyword to supply an explicit postcondition for the loop."
  | |- semax _ _ (Ssequence (Sfor _ _ _ _) _) _ =>
         fail 100 "Your loop is followed by more statements, so you must use the form of forward_loop with the break: keyword to supply an explicit postcondition for the loop."
  | P := @abbreviate ret_assert ?Post' |- semax _ _ _ ?Post => 
      first [constr_eq P Post | fail 100 "forward_loop failed; try doing abbreviate_semax first"];
      try (has_evar Post'; fail 100 "Error: your postcondition " P " has unification variables (evars), so you must use the form of forward_loop with the break: keyword to supply an explicit postcondition for the loop.");
     forward_loop Inv continue: PreInc break: Post
  | |- semax _ _ _ _ => fail 100 "forward_loop failed; try doing abbreviate_semax first"
  | |- _ => fail 100 "forward_loop applicable only to a semax goal"
end.

Tactic Notation "forward_loop" constr(Inv) "break:" constr(Post) "continue:" constr(PreInc) :=
    forward_loop Inv continue: PreInc break: Post.

Tactic Notation "forward_loop" :=
    fail "Usage:   forward_loop Inv,     where Inv is your loop invariant".

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
     andb (quickflow body (fun ek => match ek with
                              | EK_normal => true
                              | EK_break => ok EK_normal
                              | EK_continue => true
                              | EK_return => ok EK_return
                              end))
          (quickflow incr (fun ek => match ek with
                              | EK_normal => true
                              | EK_break => ok EK_normal
                              | EK_continue => false
                              | EK_return => ok EK_return
                              end))
 | Sbreak => ok EK_break
 | Scontinue => ok EK_continue
 | Sswitch _ _ => false   (* this could be made more generous *)
 | Slabel _ c => quickflow c ok
 | Sgoto _ => false
 | _ => ok EK_normal
 end.

Ltac check_nocontinue s :=
 let s' := eval hnf in s in
  lazymatch s' with 
 | Ssequence ?x _ => check_nocontinue x
 | Sloop ?body _ => unify (nocontinue body) true
 | _ => fail 100 "applied forward_loop to something that is not a loop"
end.

Ltac forward_loop_nocontinue2 Inv :=
  apply semax_loop_nocontinue; delete_skip; abbreviate_semax.

Ltac forward_loop_nocontinue1 Inv :=
  lazymatch goal with
  | |- semax _ _ (Sfor _ _ _ _) _ => apply semax_seq' with Inv; [abbreviate_semax | forward_loop_nocontinue2 Inv]
  | |- semax _ _ (Sloop _ _) _ => apply semax_pre with Inv; [ | forward_loop_nocontinue2 Inv]
  | |- semax _ _ (Swhile ?E ?B) _ => 
          let x := fresh "x" in set (x := Swhile E B); hnf in x; subst x;
          apply semax_pre with Inv; [ | forward_loop_nocontinue2 Inv]
 end.

Ltac forward_loop_nocontinue Inv Post :=
  repeat simple apply seq_assoc1;
  repeat apply -> semax_seq_skip;
  match goal with
  | |- semax _ _ (Ssequence _ _) _ => 
          apply semax_seq with Post; [forward_loop_nocontinue1 Inv  | abbreviate_semax ]
  | |- semax _ _ _ ?Post' => 
            tryif (unify Post Post') then forward_loop_nocontinue1 Inv
           else (apply (semax_post1_flipped Post); [ forward_loop_nocontinue1 Inv  
                           | abbreviate_semax; simpl_ret_assert; auto ])
  end.

Ltac forward_loop_nocontinue_nobreak Inv :=
 repeat apply -> semax_seq_skip;
  lazymatch goal with
  | |- semax _ _ (Ssequence (Swhile _ ?S) _) _ =>
          tryif (unify (nocontinue S) true; unify (nobreaksx S) true) then forward_while Inv 
          else fail 100 "Use forward_while, or (unfold Swhile at 1) and then use forward_loop"
  | |- semax _ _ (Ssequence (Sloop _ _) _) _ =>
         fail 100 "Your loop is followed by more statements, so you must use the form of forward_loop with the break: keyword to supply an explicit postcondition for the loop."
  | |- semax _ _ (Ssequence (Sfor _ _ _ _) _) _ =>
         fail 100 "Your loop is followed by more statements, so you must use the form of forward_loop with the break: keyword to supply an explicit postcondition for the loop."
  | P := @abbreviate ret_assert ?Post' |- semax _ _ _ ?Post => 
      first [constr_eq P Post | fail 100 "forward_loop failed; try doing abbreviate_semax first"];
      try (has_evar Post'; fail 100 "Error: your postcondition " P " has unification variables (evars), so you must use the form of forward_loop with the break: keyword to supply an explicit postcondition for the loop.");
     forward_loop_nocontinue Inv Post
  | |- semax _ _ _ _ => fail 100 "forward_loop failed; try doing abbreviate_semax first"
  | |- _ => fail 100 "forward_loop applicable only to a semax goal"
end.

Tactic Notation "forward_loop" constr(Inv)  := 
 repeat simple apply seq_assoc1;
 repeat apply -> semax_seq_skip;
  lazymatch goal with
  | |- semax _ _ (Ssequence (Sfor _ ?e2 ?s3 ?s4) _) _ =>
     let c := constr:(Sloop (Ssequence (Sifthenelse e2 Sskip Sbreak) s3) s4) in
    tryif (check_nocontinue c)
     then forward_loop_nocontinue_nobreak Inv
     else (check_no_incr c; forward_loop Inv continue: Inv)
  | |- semax _ _ ?c _ =>
  tryif (check_nocontinue c)
   then forward_loop_nocontinue_nobreak Inv
  else (check_no_incr c; forward_loop Inv continue: Inv)
 end.

Tactic Notation "forward_loop" constr(Inv) "break:" constr(Post) :=
 repeat simple apply seq_assoc1;
 repeat apply -> semax_seq_skip;
  lazymatch goal with
  | |- semax _ _ (Ssequence (Sfor _ ?e2 ?s3 ?s4) _) _ =>
     let c := constr:(Sloop (Ssequence (Sifthenelse e2 Sskip Sbreak) s3) s4) in
      tryif (check_nocontinue c)
       then forward_loop_nocontinue Inv Post
       else (check_no_incr c; forward_loop Inv continue: Inv break: Post)
  | |- semax _ _ (Sfor _ ?e2 ?s3 ?s4) _ =>
     let c := constr:(Sloop (Ssequence (Sifthenelse e2 Sskip Sbreak) s3) s4) in
      tryif (check_nocontinue c)
       then forward_loop_nocontinue Inv Post
       else (check_no_incr c; forward_loop Inv continue: Inv break: Post)
  | |- semax _ _ ?c _ =>
  tryif (check_nocontinue c)
   then forward_loop_nocontinue Inv Post
  else (check_no_incr c; forward_loop Inv continue: Inv break: Post)
 end.

Tactic Notation "forward_for" constr(Inv) "continue:" constr(PreInc) :=
  check_Delta; check_POSTCONDITION;
  repeat simple apply seq_assoc1;
  lazymatch type of Inv with
  | _ -> environ -> mpred => idtac
  | _ => fail "Invariant (first argument to forward_for) must have type (_ -> environ -> mpred)"
  end;
  lazymatch type of PreInc with
  | _ -> environ -> mpred => idtac
  | _ => fail "PreInc (continue: argument to forward_for) must have type (_ -> environ -> mpred)"
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

Tactic Notation "forward_for" constr(Inv) "continue:" constr(PreInc) "break:" constr(Postcond) :=
  check_Delta; check_POSTCONDITION;
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

Tactic Notation "forward_for" constr(Inv) "break:" constr(Postcond) "continue:" constr(PreInc) :=
   forward_for Inv continue: PreInc break: Postcond.

Tactic Notation "forward_for" constr(Inv) constr(PreInc) :=
  fail "Usage of the forward_for tactic:
forward_for  Inv   (* where Inv: A->environ->mpred is a predicate on index values of type A *)
forward_for Inv continue: PreInc (* where Inv,PreInc are predicates on index values of type A *)
forward_for Inv continue: PreInc break:Post (* where Post: environ->mpred is an assertion *)".

Lemma semax_convert_for_while:
 forall CS Espec Delta Pre s1 e2 s3 s4 Post,
  nocontinue s4 = true ->
  nocontinue s3 = true ->
  @semax CS Espec Delta Pre (Ssequence s1 (Swhile e2 (Ssequence s4 s3))) Post ->
  @semax CS Espec Delta Pre (Sfor s1 e2 s4 s3) Post.
Proof.
intros.
pose proof (semax_convert_for_while' CS Espec Delta Pre s1 e2 s3 s4 Sskip Post H).
spec H2; auto.
apply -> semax_seq_skip in H1; auto.
apply seq_assoc in H1; auto.
apply <- semax_seq_skip.
apply H2; auto.
Qed.

Tactic Notation "forward_for" constr(Inv) :=
  check_Delta; check_POSTCONDITION;
  repeat simple apply seq_assoc1;
  lazymatch type of Inv with
  | _ -> environ -> mpred => idtac
  | _ => fail "Invariant (first argument to forward_for) must have type (_ -> environ -> mpred)"
  end;
  lazymatch goal with
  | |- semax _ _ (Ssequence (Sfor _ _ _ _) _) _ =>
        apply semax_convert_for_while';
             [(reflexivity ||
                 fail "Your for-loop has a continue statement, so your forward_for needs a continue: clause")
               | (reflexivity || fail "Unexpected continue statement in for-loop increment")
               | apply semax_seq' with (exp Inv);
                   [  |  forward_while (EX x:_, Inv x); [ apply ENTAIL_refl | | |  ]  ] ]
  | |- semax _ _ (Sfor _ _ _ _) _ =>
        apply semax_convert_for_while;
             [(reflexivity ||
                 fail "Your for-loop has a continue statement, so your forward_for needs a continue: clause")
               | (reflexivity || fail "Unexpected continue statement in for-loop increment")
               | apply semax_seq' with (exp Inv);
                   [  |  forward_while (EX x:_, Inv x);
                             [ apply ENTAIL_refl | | | eapply semax_post_flipped'; [apply semax_skip | ] ]  ] ]
        
  end.

Ltac process_cases sign := 
match goal with
| |- semax _ _ (seq_of_labeled_statement 
     match select_switch_case ?N (LScons (Some ?X) ?C ?SL)
      with Some _ => _ | None => _ end) _ =>
       let y := constr:(adjust_for_sign sign X) in let y := eval compute in y in 
      rewrite (select_switch_case_signed y); 
           [ | reflexivity | clear; compute; split; congruence];
     let E := fresh "E" in let NE := fresh "NE" in 
     destruct (zeq N (Int.unsigned (Int.repr y))) as [E|NE];
      [ try ( rewrite if_true; [  | symmetry; apply E]);
        unfold seq_of_labeled_statement at 1;
        apply unsigned_eq_eq in E;
        match sign with
        | Signed => apply repr_inj_signed in E; [ | rep_lia | rep_lia]
        | Unsigned => apply repr_inj_unsigned in E; [ | rep_lia | rep_lia]
        end;
        try match type of E with ?a = _ => is_var a; subst a end;
        repeat apply -> semax_skip_seq
     | try (rewrite if_false by (contradict NE; symmetry; apply NE));
        process_cases sign
    ]
| |- semax _ _ (seq_of_labeled_statement 
     match select_switch_case ?N (LScons None ?C ?SL)
      with Some _ => _ | None => _ end) _ =>
      change (select_switch_case N (LScons None C SL))
       with (select_switch_case N SL);
        process_cases sign
| |- semax _ _ (seq_of_labeled_statement 
     match select_switch_case ?N LSnil
      with Some _ => _ | None => _ end) _ =>
      change (select_switch_case N LSnil)
           with (@None labeled_statements);
      cbv iota;
      unfold seq_of_labeled_statement at 1;
      repeat apply -> semax_skip_seq
end.

Ltac forward_switch' := 
match goal with
| |- semax ?Delta ?Pre (Sswitch ?e _) _ =>
   let sign := constr:(signof e) in let sign := eval hnf in sign in
    let HRE := fresh "H" in let v := fresh "v" in 
    do_compute_expr1 Delta Pre e;
    match goal with v' := _, H:_ |- _ => rename H into HRE; rename v' into v end;
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
           | clear HRE; unfold select_switch at 1; unfold select_switch_default at 1;
             try match goal with H := @abbreviate statement _ |- _ => clear H end;
             process_cases sign ]
]
end.

Definition nofallthrough ek :=
 match ek with
 | EK_normal => false
 | _ => true
 end.

Ltac forward_if'_new :=
  check_Delta; check_POSTCONDITION;
 repeat apply -> semax_seq_skip;
 repeat (apply seq_assoc1; try apply -> semax_seq_skip);
match goal with
| |- semax ?Delta ?Pre (Sifthenelse ?e ?c1 ?c2) _ =>
   let HRE := fresh "H" in let v := fresh "v" in
    do_compute_expr1 Delta Pre e;
    match goal with v' := _, H:_ |- _ => rename H into HRE; rename v' into v end;
    apply (semax_ifthenelse_PQR' _ v);
     [ reflexivity | entailer | assumption
     | simpl in v; clear HRE; subst v; apply semax_extract_PROP; intro HRE;
       do_repr_inj HRE;
       repeat (apply semax_extract_PROP; intro);
       try rewrite Int.signed_repr in HRE by rep_lia;
       repeat apply -> semax_skip_seq;
       abbreviate_semax
     |  simpl in v; clear HRE; subst v; apply semax_extract_PROP; intro HRE;
       do_repr_inj HRE;
       repeat (apply semax_extract_PROP; intro);
       try rewrite Int.signed_repr in HRE by rep_lia;
       repeat apply -> semax_skip_seq;
       abbreviate_semax
     ]
| |- semax ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) (Ssequence (Sifthenelse ?e ?c1 ?c2) _) _ =>
    tryif (unify (orb (quickflow c1 nofallthrough) (quickflow c2 nofallthrough)) true)
    then (apply semax_if_seq; forward_if'_new)
    else fail "Because your if-statement is followed by another statement, you need to do 'forward_if Post', where Post is a postcondition of type (environ->mpred) or of type Prop"
| |- semax _ (@exp _ _ _ _) _ _ =>
      fail "First use Intros ... to take care of the EXistentially quantified variables in the precondition"
| |- semax _ _ (Sswitch _ _) _ =>
  forward_switch'
| |- semax _ _ (Ssequence (Sifthenelse _ _ _) _) _ => 
     fail "forward_if failed for some unknown reason, perhaps your precondition is not in canonical form"
| |- semax _ _ (Ssequence (Sswitch _ _) _) _ => 
     fail "Because your switch statement is followed by another statement, you need to do 'forward_if Post', where Post is a postcondition of type (environ->mpred) or of type Prop"
end.

Lemma ENTAIL_break_normal:
 forall Delta R S, ENTAIL Delta, RA_break (normal_ret_assert R) |-- S.
Proof.
intros. simpl_ret_assert. apply andp_left2; apply FF_left.
Qed.

Lemma ENTAIL_continue_normal:
 forall Delta R S, ENTAIL Delta, RA_continue (normal_ret_assert R) |-- S.
Proof.
intros. simpl_ret_assert. apply andp_left2; apply FF_left.
Qed.

Lemma ENTAIL_return_normal:
 forall Delta R v S, ENTAIL Delta, RA_return (normal_ret_assert R) v |-- S.
Proof.
intros. simpl_ret_assert. apply andp_left2; apply FF_left.
Qed.

#[export] Hint Resolve ENTAIL_break_normal ENTAIL_continue_normal ENTAIL_return_normal : core.

#[export] Hint Extern 0 (ENTAIL _, _ |-- _) =>
 match goal with |- ENTAIL _, ?A |-- ?B => constr_eq A B; simple apply ENTAIL_refl end : core.

Ltac forward_if_tac post :=
  check_Delta; check_POSTCONDITION;
  repeat (apply -> seq_assoc; abbreviate_semax);
  repeat apply -> semax_seq_skip;
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
      | try subst P; unfold abbreviate;
        simpl_ret_assert;
        try (match goal with |- ?A => no_evars A end;
             try apply ENTAIL_refl;
             try solve [normalize])
      | intros; try subst P; unfold abbreviate;
        simpl_ret_assert;
        try (match goal with |- ?A => no_evars A end;
             try apply ENTAIL_refl; 
             try solve [normalize])
        .. 
      ]
   | |- semax _ _ (Ssequence (Sifthenelse _ _ _) _) _ =>
     apply semax_seq with post;
      [forward_if'_new 
      | abbreviate_semax; 
        simpl_ret_assert (*autorewrite with ret_assert*)]
   | |- semax _ _ (Ssequence (Sswitch _ _) _) _ =>
     apply semax_seq with post;
      [forward_switch' 
      | abbreviate_semax; 
        simpl_ret_assert (*autorewrite with ret_assert*)]
end.

Ltac remove_LOCAL name Q :=
  let i := eval hnf in (find_LOCAL_index name O Q) in
    match i with
    | Some ?i' =>
        let r := eval cbv iota zeta beta delta [delete_nth] in (delete_nth i' Q) in
        constr:(r)
    | None =>
        constr:(Q)
    end.

Ltac remove_LOCAL2 Qr Q :=
  match Qr with
  | nil => constr:(Q)
  | cons ?Qr_head ?Qr_tail =>
      match Qr_head with
      | temp ?name _ =>
          let Q' := remove_LOCAL name Q in remove_LOCAL2 Qr_tail Q'
      | _ =>
          remove_LOCAL2 Qr_tail Q
      end
  end.

Tactic Notation "forward_if" constr(post) :=
  lazymatch type of post with
  | Prop =>
      match goal with
      | |- semax _ (PROPx (?P) ?Q) _ _ =>
          forward_if_tac (PROPx (post :: P) Q)
      end
  | list Prop =>
      match goal with
      | |- semax _ (PROPx (?P) ?Q) _ _ =>
          let P' := eval cbv iota zeta beta delta [app] in (post ++ P) in
          forward_if_tac (PROPx P' Q)
      end
  | localdef =>
      match goal with
      | |- semax _ (PROPx (?P) (LOCALx ?Q ?R)) _ _ =>
          let Q' := remove_LOCAL2 constr:(cons post nil) Q in
          forward_if_tac (PROPx (P) (LOCALx (post :: Q') R))
      end
  | list localdef =>
      match goal with
      | |- semax _ (PROPx (?P) (LOCALx ?Q ?R)) _ _ =>
          let Q' := remove_LOCAL2 post Q in
          let Q'' := eval cbv iota zeta beta delta [app] in (post ++ Q') in
          forward_if_tac (PROPx (P) (LOCALx Q'' R))
      end
  | _ => forward_if_tac post
  end.

Tactic Notation "forward_if" :=
  forward_if'_new.

Ltac normalize :=
 floyd.seplog_tactics.normalize.

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

Lemma eqb_su_refl s: eqb_su s s = true. Proof. unfold eqb_su. destruct s; trivial. Qed.
Lemma Neqb_option_refl n: @eqb_option N N.eqb n n = true. Proof. destruct n; simpl; trivial. apply N.eqb_refl. Qed.
Lemma eqb_attr_refl a: eqb_attr a a = true.
Proof. unfold eqb_attr. destruct a. rewrite eqb_reflx, Neqb_option_refl; trivial. Qed.
Lemma eqb_member_refl m: eqb_member m m = true.
Proof. unfold eqb_member. rewrite eqb_ident_true, eqb_type_refl; trivial. Qed.

Lemma eqb_list_sym {A} f: forall l1 l2, @eqb_list A f l1 l2 = @eqb_list A (fun x y => f y x) l2 l1.
Proof. induction l1; simpl; intros; destruct l2; simpl; trivial. f_equal; auto. Qed.

Lemma eqb_ident_sym i j: eqb_ident i j = eqb_ident j i.
Proof. apply Pos.eqb_sym. Qed.
Lemma eqb_member_sym: (fun x y : ident * type => eqb_member y x) = eqb_member.
Proof.
  extensionality x. extensionality y. unfold eqb_member.
  rewrite eqb_ident_sym, expr_lemmas4.eqb_type_sym; trivial.
Qed.

Lemma eqb_su_sym a b: eqb_su a b = eqb_su b a.
Proof. destruct a; destruct b; trivial. Qed. 
Lemma eqb_attr_sym a b: eqb_attr a b = eqb_attr b a.
Proof. destruct a; destruct b; simpl; f_equal.
  apply Raux.eqb_sym. unfold eqb_option.
  destruct attr_alignas; destruct attr_alignas0; trivial. apply N.eqb_sym.
Qed.

Lemma test_aux_sym cs1 cs2 b i: test_aux cs1 cs2 b i = test_aux cs2 cs1 b i. 
Proof. unfold test_aux. f_equal.
  destruct ((@cenv_cs cs1) ! i); destruct ((@cenv_cs cs2) ! i); trivial.
  rewrite eqb_list_sym, eqb_su_sym, eqb_member_sym, eqb_attr_sym; trivial.
Qed.

Lemma cs_preserve_type_sym cs1 cs2: forall t CCE, cs_preserve_type cs1 cs2 CCE t = cs_preserve_type cs2 cs1 CCE t. 
Proof. induction t; simpl; trivial; intros; destruct (CCE ! i); trivial; apply test_aux_sym. Qed.


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

Ltac ensure_open_normal_ret_assert :=
 try simple apply sequential';
 match goal with
 | |- semax _ _ _ (normal_ret_assert ?X) => is_evar X
 end.

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
    local (tc_environ Delta) && R' |-- R ->
    @semax cs Espec Delta P c (normal_ret_assert R') ->
    @semax cs Espec Delta P c (normal_ret_assert R) .
Proof.
 intros. eapply semax_post'; [ | apply H0]. auto.
Qed.

Lemma semax_post_flipped3:
  forall R' Espec {cs: compspecs} Delta P c R,
    @semax cs Espec Delta P c (normal_ret_assert R') ->
    local (tc_environ Delta) && R' |-- R ->
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
#[export] Hint Extern 1 (@sizeof _ ?A > 0) =>
   (let a := fresh in set (a:= sizeof A); hnf in a; subst a; computable)
  : valid_pointer.
#[export] Hint Resolve denote_tc_test_eq_split : valid_pointer.

Ltac pre_entailer :=
  try match goal with
  | H := @abbreviate statement _ |- _ => clear H
  end;
  try match goal with
  | H := @abbreviate ret_assert _ |- _ => clear H
  end.

Inductive Type_of_right_hand_side_does_not_match_type_of_assigned_variable := .

Ltac check_cast_assignment :=
   first [reflexivity | elimtype Type_of_right_hand_side_does_not_match_type_of_assigned_variable].

Ltac forward_setx :=
  ensure_normal_ret_assert;
  hoist_later_in_pre;
 match goal with
 | |- semax ?Delta (|> (PROPx ?P (LOCALx ?Q (SEPx ?R)))) (Sset _ ?e) _ =>
        eapply semax_PTree_set;
        [ prove_local2ptree
        | reflexivity
        | check_cast_assignment
        | solve_msubst_eval; simplify_casts; reflexivity
        | first [ quick_typecheck3
                | pre_entailer; try solve [entailer!]]
        ]
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
  P |-- local (`(eq (Vint i)) (eval_expr ei)) ->
  is_int_type (typeof ei) = true ->
  P |-- local (efield_denote (eArraySubsc ei :: efs) 
          (ArraySubsc (int_signed_or_unsigned (typeof ei) i) :: gfs)).
Proof.
  intros.
  rewrite (add_andp _ _ H), (add_andp _ _ H0), andp_assoc.
  apply andp_left2.
  intros rho; simpl; unfold local, lift1; unfold_lift; floyd.seplog_tactics.normalize.
  constructor; auto.
  2:   constructor; auto.
  clear - H1. destruct (typeof ei); inv H1.
  unfold int_signed_or_unsigned. destruct i0,s; simpl; rep_lia. 
  rewrite <- H2.
  destruct (typeof ei); inv H1.
  unfold int_signed_or_unsigned. destruct i0,s; simpl;
  rewrite ?Int.repr_signed, ?Int.repr_unsigned; auto. 
Qed.

Lemma efield_denote_cons_struct: forall {cs: compspecs} P efs gfs i,
  P |-- local (efield_denote efs gfs) ->
  P |-- local (efield_denote (eStructField i :: efs) (StructField i :: gfs)).
Proof.
  intros.
  eapply derives_trans; [exact H |].
  intros rho; simpl; unfold local, lift1; unfold_lift; floyd.seplog_tactics.normalize.
  constructor; auto.
Qed.

Lemma efield_denote_cons_union: forall {cs: compspecs} P efs gfs i,
  P |-- local (efield_denote efs gfs) ->
  P |-- local (efield_denote (eUnionField i :: efs) (UnionField i :: gfs)).
Proof.
  intros.
  eapply derives_trans; [exact H |].
  intros rho; simpl; unfold local, lift1; unfold_lift; floyd.seplog_tactics.normalize.
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
          let vi := fresh "vi" in
          do_compute_expr1 Delta constr:(PROPx P (LOCALx Q (SEPx R))) ei;
          match goal with v' := _, H:_ |- _ => rename H into HA; rename v' into vi end;
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

Lemma sem_add_ptr_int_lem:
 forall {cs: compspecs} v t i,
   complete_type cenv_cs t = true ->
   isptr v ->
   Clight_Cop2.sem_add (tptr t) tint v (Vint (Int.repr i)) = Some (add_ptr_int t v i).
Proof.
intros. destruct v; inv H0; simpl.
unfold add_ptr_int; simpl; unfold sem_add_ptr_int.
rewrite H. reflexivity.
Qed.
Hint Rewrite @sem_add_ptr_int_lem using (try reflexivity; assumption) : norm1.

Lemma sem_add_pi': forall {CS: compspecs} t0 si v i,
   complete_type cenv_cs t0 = true ->
  isptr v ->
  match si with
  | Signed => Int.min_signed <= i <= Int.max_signed
  | Unsigned => 0 <= i <= Int.max_unsigned
  end ->
   force_val (sem_add_ptr_int t0 si v (Vint (Int.repr i))) =
   offset_val (sizeof t0 * i) v.
Proof.
  intros.
  unfold sem_add_ptr_int.
  rewrite H.
  rewrite sem_add_pi_ptr; auto.
Qed.
Hint Rewrite @sem_add_pi' using (solve [try reflexivity; auto with norm ; rep_lia]) : norm.

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
 | repeat ?v' (Z.to_nat _) => simple_value v'
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


Ltac store_tac :=
ensure_open_normal_ret_assert;
hoist_later_in_pre;
sc_set_load_store.store_tac.

(* END new semax_load and semax_store tactics *************************)

Ltac forward0 :=  (* USE FOR DEBUGGING *)
  match goal with
  | |- @semax _ _ _ ?PQR (Ssequence ?c1 ?c2) ?PQR' =>
           let Post := fresh "Post" in
              evar (Post : environ->mpred);
              apply semax_seq' with Post;
               [
               | unfold Post; clear Post ]
  end.

(*
Lemma normal_ret_assert_derives'':
  forall P Q R, P |-- R ->  normal_ret_assert (local Q && P) |-- normal_ret_assert R.
Proof.
  intros. intros ek vl rho. apply normal_ret_assert_derives.
 simpl. apply andp_left2. apply H.
Qed.
*)

(*
Lemma frame_ret_assert_derives P Q: P |-- Q -> frame_ret_assert P |-- frame_ret_assert Q.
Proof. intros.
 unfold frame_ret_assert. intros ? ? ?. apply sepcon_derives; trivial. apply H. Qed.
*)

Lemma bind_ret_derives t P Q v: P|-- Q -> bind_ret v t P |-- bind_ret v t Q.
Proof. intros. destruct v. simpl; intros. entailer!. apply H.
  destruct t; try apply derives_refl. simpl; intros. apply H. 
Qed.

(*
Lemma function_body_ret_assert_derives t P Q: P |-- Q ->
      function_body_ret_assert t P |-- function_body_ret_assert t Q.
Proof. intros. intros ek v.
  destruct ek; simpl; trivial.
  intros. apply bind_ret_derives; trivial.
Qed.
*)

Ltac entailer_for_return := entailer.

Ltac solve_return_outer_gen := solve [repeat constructor].

Ltac solve_return_inner_gen :=
  match goal with
  | |- return_inner_gen _ ?v ?P _ =>
    match P with
    | exp _ =>
      simple apply return_inner_gen_EX;
      let a := fresh "a" in
      intro a;
      eexists;
      split;
      [ solve_return_inner_gen
      | build_func_abs_right
      ]
    | PROPx _ (LOCALx _ (SEPx _)) =>
      match v with
      | Some _ => first [ simple apply return_inner_gen_canon_Some;
                          unfold VST_floyd_app; reflexivity
                        | simple apply return_inner_gen_canon_nil;
                          unfold VST_floyd_app; reflexivity
                        | fail 1000 "the LOCAL clauses of this POSTCONDITION should only contain ret_temp. Other variables appears there now."]
      | None   => first [ simple apply return_inner_gen_canon_nil;
                          unfold VST_floyd_app; reflexivity
                        | fail 1000 "the LOCAL clauses of this POSTCONDITION should not contain any variable."]
      end
    | _ => first [ simple apply return_inner_gen_main
                 | fail 1000 "the POSTCONDITION should be in an existential canonical form."
                             "One possible cause of this is some 'simpl in *' command which destroys the existential form in POSTCONDITION."]
    end
 end.

Inductive fn_data_at {cs: compspecs} (Delta: tycontext) (T2: PTree.t (type * val)): ident * type -> mpred -> Prop :=
| fn_data_at_intro: forall i t p,
    (complete_legal_cosu_type t && (sizeof t <? Ptrofs.modulus) && is_aligned cenv_cs ha_env_cs la_env_cs t 0 = true)%bool ->
    msubst_eval_lvar Delta T2 i t = Some p ->
    fn_data_at Delta T2 (i, t) (data_at_ Tsh t p).

Lemma canonicalize_stackframe: forall {cs: compspecs} Delta P Q R T1 T2 GV fn,
  local2ptree Q = (T1, T2, nil, GV) ->
  Forall2 (fn_data_at Delta T2) fn R ->
  local (tc_environ Delta) && PROPx P (LOCALx Q (SEPx R)) |-- fold_right sepcon emp (map (var_block Tsh) fn).
Proof.
  intros.
  induction H0.
  + go_lowerx.
  + change (ENTAIL Delta, PROPx P (LOCALx Q (SEPx (y :: l'))) |-- var_block Tsh x * fold_right sepcon emp (map (var_block Tsh) l)).
    eapply derives_trans; [| apply sepcon_derives; [apply derives_refl | exact IHForall2]]; clear IHForall2.
    apply (local2ptree_soundness P Q (y :: l')) in H; simpl app in H.
    inv H0.
    rewrite !andb_true_iff in H2; destruct H2 as [[? ?] ?].
    apply (msubst_eval_lvar_eq Delta P T1 T2 GV (data_at_ Tsh t p :: l')) in H3.
    rewrite <- H in H3; clear H.
    rewrite (add_andp _ _ H3); clear H3.
    go_lowerx.
    apply sepcon_derives; auto.
    subst.
    rewrite var_block_data_at_ by auto. apply derives_refl.
Qed.

Lemma canonicalize_stackframe_emp: forall {cs: compspecs} Delta P Q,
  local (tc_environ Delta) && PROPx P (LOCALx Q (SEPx nil)) |-- emp.
Proof.
  intros.
  go_lowerx.
Qed.

Ltac solve_Forall2_fn_data_at :=
  solve
    [ apply Forall2_nil
    | apply Forall2_cons; [ apply fn_data_at_intro; [reflexivity | solve_msubst_eval_lvar] | solve_Forall2_fn_data_at]].

Ltac solve_canon_derives_stackframe :=
  solve
    [ simple apply canonicalize_stackframe_emp
    | try unfold stackframe_of;
      simple eapply canonicalize_stackframe;
      [ prove_local2ptree
      | solve_Forall2_fn_data_at
      ]
    ].

Ltac fold_frame_function_body :=
match goal with P := @abbreviate ret_assert _ |- _ => unfold abbreviate in P; subst P end;
match goal with |- semax _ _ _ ?R =>
 match R with {| RA_return := (fun vl rho => bind_ret _ ?t ?P _ * stackframe_of ?f _) |} =>
  apply semax_post with (frame_ret_assert (function_body_ret_assert t P) (stackframe_of f));
   [ simpl_ret_assert; rewrite FF_sepcon; apply andp_left2; apply FF_left
   | simpl_ret_assert; rewrite FF_sepcon; apply andp_left2; apply FF_left
   | simpl_ret_assert; rewrite FF_sepcon; apply andp_left2; apply FF_left
   | simpl_ret_assert; solve [auto]
   |]
 end
end.

Lemma fold_another_var_block:
  forall {cs: compspecs} Delta P Q R P' Q' R' i (t: type) vbs T1 T2 GV p,
  local2ptree Q = (T1,T2,[],GV) ->
  complete_legal_cosu_type t = true ->
  sizeof t <? Ptrofs.modulus = true ->
  is_aligned cenv_cs ha_env_cs la_env_cs t 0 = true ->
  (var_types Delta) ! i = Some t ->
  T2 ! i = Some (t,p) ->
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) 
      |-- PROPx P' (LOCALx Q' (SEPx (data_at_ Tsh t p :: R')))
             * fold_right sepcon emp (map (var_block Tsh) vbs) ->
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) 
    |-- PROPx P' (LOCALx Q' (SEPx R')) 
           * fold_right sepcon emp (map (var_block Tsh) ((i,t)::vbs)).
Proof.
intros until 1.
intros H1 H2 H3 H4 H5 H0.
set (r1 := data_at_ Tsh t p) in *.
change (ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- 
    PROPx P' (LOCALx Q' (SEPx R')) * (var_block Tsh (i,t) * fold_right sepcon emp (map (var_block Tsh) vbs))).
forget  (fold_right sepcon emp (map (var_block Tsh) vbs)) as VBS.
replace (PROPx P' (LOCALx Q' (SEPx (r1 :: R'))) * VBS)
   with (PROPx P' (LOCALx Q' (SEPx R')) * (liftx r1 * VBS)) in H0.
2:{
  extensionality rho;
 unfold PROPx, LOCALx, SEPx; unfold_lift; simpl.
 unfold local, lift1.
 floyd.seplog_tactics.normalize. f_equal. rewrite <- sepcon_assoc.
 pull_left r1. auto.
}
apply derives_trans with
((local (tc_environ Delta) &&  PROPx P (LOCALx Q (SEPx R))) 
   && (local (tc_environ Delta) &&  PROPx nil (LOCALx Q (SEPx(TT::nil))))).
go_lowerx.
repeat apply andp_right; auto; try apply prop_right; auto.
rewrite sepcon_emp. apply TT_right.
erewrite (local2ptree_soundness nil Q) by eassumption.
eapply derives_trans.
apply andp_derives.
apply H0. apply derives_refl.
forget (PROPx P' (LOCALx Q' (SEPx R'))) as PQR'.
clear H0.
simpl app.
inv H1.
assert (  msubst_extract_local Delta T1 T2 GV (lvar i t p)).
hnf.
rewrite H5. rewrite eqb_type_refl. auto.
apply localdef_local_facts_inv with (P:=nil)(R := [TT]) in H0.
forget (LocalD T1 T2 GV) as L.
eapply derives_trans with
(PQR' * (liftx r1 * VBS) && 
(local (tc_environ Delta) && local (locald_denote (lvar i t p)))).
apply andp_derives; auto.
apply andp_right.
apply andp_left1; auto.
auto.
go_lowerx.
normalize.
apply sepcon_derives; auto.
apply sepcon_derives; auto.
eapply var_block_lvar0; try eassumption.
apply Z.ltb_lt; auto.
Qed.

Lemma no_more_var_blocks:
 forall {cs: compspecs} Delta PQR PQR',
  ENTAIL Delta, PQR |-- PQR' ->
  ENTAIL Delta, PQR |-- PQR' * fold_right sepcon emp (map (var_block Tsh) []).
Proof.
intros.
unfold map.
unfold fold_right.
rewrite sepcon_emp.
auto.
Qed.

Ltac try_clean_up_stackframe :=
  lazymatch goal with |-
     ENTAIL _, PROPx _ (LOCALx _ (SEPx _)) |--
        PROPx _ (LOCALx _ (SEPx _)) * stackframe_of _ =>
     unfold stackframe_of;
     simpl fn_vars;
     repeat (
     simple eapply fold_another_var_block;
       [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity 
         | reflexivity | ]);
     try simple apply no_more_var_blocks
  | |- _ => idtac
 end.

Ltac clean_up_stackframe ::=
  lazymatch goal with |-
     ENTAIL _, PROPx _ (LOCALx _ (SEPx _)) |--
        PROPx _ (LOCALx _ (SEPx _)) * stackframe_of _ =>
     unfold stackframe_of;
     simpl fn_vars;
     repeat (
     simple eapply fold_another_var_block;
       [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity 
         | reflexivity | ]);
     try simple apply no_more_var_blocks
  | |- ENTAIL _ , _ |-- exp _ * stackframe_of _ =>
      fail 2 "In this case, because stackframe_of is present, use Exists to instantiate the existential before calling entailer!"
  | |- ENTAIL _ , _ |-- exp ?P =>
        lazymatch P with context [@stackframe_of] => 
         fail 2 "In this case, because stackframe_of is present, use Exists to instantiate the existential before calling entailer!"
       | _ => idtac
       end
  | |- _ => idtac
 end.

Ltac forward_return :=
  try fold_frame_function_body;
  match goal with
  | |- @semax ?CS _ ?Delta ?Pre (Sreturn ?oe) _ =>
    match oe with
    | None =>
        eapply semax_return_None;
        [ (reflexivity || fail 1000 "Error: return type is not Tvoid")
        | (solve_return_outer_gen || fail 1000 "unexpected failure in forward_return. Do not remove the stackframe")
        | (solve_canon_derives_stackframe || fail 1000 "stackframe is unfolded or modified.")
        | try match goal with Post := _ : ret_assert |- _ => subst Post; unfold abbreviate end;
          try change_compspecs CS;
          solve_return_inner_gen
        | entailer_for_return]
    | Some ?ret =>
        let v := fresh "v" in
        let H := fresh "HRE" in
        do_compute_expr1 Delta Pre constr:(Ecast ret (ret_type Delta));
        match goal with v' := _, H':_ |- _ => rename H' into H; rename v' into v end;
        subst v;
        eapply semax_return_Some;
        [ exact H
        | entailer_for_return
        | (solve_return_outer_gen || fail 1000 "unexpected failure in forward_return. Do not remove the stackframe")
        | (solve_canon_derives_stackframe || fail 1000 "stackframe is unfolded or modified.")
        | try match goal with Post := _ : ret_assert |- _ => subst Post; unfold abbreviate end;
          try change_compspecs CS;
          solve_return_inner_gen
        | entailer_for_return];
        clear H
    end
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
 | Evar _ ?t => lazymatch as_lvalue with true => idtac | false => is_array_type t end
 | Etempvar _ _ => idtac
 | Ederef ?e1 ?t => lazymatch as_lvalue with true => idtac | false => is_array_type t end;
                               no_loads_expr e1 true
 | Eaddrof ?e1 _ => no_loads_expr e1 true
 | Eunop _ ?e1 _ => no_loads_expr e1 as_lvalue
 | Ebinop _ ?e1 ?e2 _ => no_loads_expr e1 as_lvalue ; no_loads_expr e2 as_lvalue
 | Ecast ?e1 _ => no_loads_expr e1 as_lvalue
 | Efield ?e1 _ ?t => lazymatch as_lvalue with true => idtac | false => is_array_type t end;
                               no_loads_expr e1 true 
 | Esizeof _ _ => idtac
 | Ealignof _ _ => idtac
end.

Definition Undo__Then_do__forward_call_W__where_W_is_a_witness_whose_type_is_given_above_the_line_now := False.

Ltac advise_forward_call :=
 prove_call_setup1 funspec_sub_refl;
 [ .. | 
 match goal with |- call_setup1 _ _ _ _ _ _ _ _ (*_*) _ _ _ _ _ ?A _ _ _ _ _ _ _ -> _ =>
  lazymatch A with
  | rmaps.ConstType ?T => 
             fail "To prove this function call, use forward_call(W), where
W:"T"
is a WITH-clause witness"
  | _ => fail "This function has a complex calling convention not recognized by forward_call"
 end 
end].

Ltac advise_prepare_postcondition := 
 match goal with
 | Post' := _ : ret_assert |- semax _ _ _ ?Post =>
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


Ltac forward_advise_loop c :=
 try lazymatch c with
 | Sfor _ _ Sskip ?body =>
        unify (nobreaksx body) true;
        fail "Use [forward; forward_while Inv] to prove this loop, where Inv is a loop invariant of type (environ->mpred)"
 | Swhile _ ?body =>
        unify (nobreaksx body) true;
        fail "Use [forward_while Inv] to prove this loop, where Inv is a loop invariant of type (environ->mpred)"
 | Sloop (Ssequence (Sifthenelse _ Sbreak Sskip) ?body) Sskip =>
        unify (nobreaksx body) true;
        fail "Use [forward_while Inv] to prove this loop, where Inv is a loop invariant of type (environ->mpred)"
 end;
 lazymatch c with
  | Sfor _ ?test ?body ?incr  =>
       tryif (unify (nobreaksx body) true; test_simple_bound test incr)
       then fail "You can probably use [forward_for_simple_bound n Inv], provided that the upper bound of your loop can be expressed as a constant value (n:Z), and the loop invariant Inv can be expressed as (EX i:Z, ...).  Note that the Inv should not mention the LOCAL binding of the loop-count variable to the value i, and need not assert the PROP that i<=n; these will be inserted automatically.
Otherwise, you can use the general case: Use [forward_loop Inv] to prove this loop, where Inv is a loop invariant of type (environ -> mpred).  The [forward_loop] tactic will advise you if you need continue: or break: assertions in addition"
       else fail "Use [forward_loop Inv] to prove this loop, where Inv is a loop invariant of type (environ -> mpred).  The [forward_loop] tactic will advise you if you need continue: or break: assertions in addition"
  | Sloop _ _ =>
     fail "Use [forward_loop Inv] to prove this loop, where Inv is a loop invariant of type (environ -> mpred).  The [forward_loop] tactic will advise you if you need continue: or break: assertions in addition"
 end.

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
       then fail "Use [forward_if Post] to prove this if-statement, where Post is the postcondition of both branches, or try simply 'forward_if' without a postcondition to see if that is permitted in this case"
       else fail "Use [forward_if] to prove this if-statement; you don't need to supply a postcondition"
   | |- semax _ _ (Sswitch _ _) ?R =>
       tryif has_evar R
       then fail "Use [forward_if Post] to prove this switch-statement, where Post is the postcondition of all branches, or try simply 'forward_if' without a postcondition to see if that is permitted in this case"
       else fail "Use [forward_if] to prove this switch-statement; you don't need to supply a postcondition"
  end.

Ltac forward_advise_while := 
  advise_prepare_postcondition;
 lazymatch goal with
   | |- semax _ _ (Swhile _ _) _ =>
       fail "Use [forward_while Inv] to prove this loop, where Inv is the loop invariant"
  end.

Ltac forward1 s :=  (* Note: this should match only those commands that
                                     can take a normal_ret_assert *)
    lazymatch s with
  | Sassign _ _ => clear_Delta_specs; store_tac
  | Sset _ ?e => clear_Delta_specs;
    first [no_loads_expr e false; forward_setx | load_tac]
  | Sifthenelse _ _ _ => forward_advise_if
  | Sswitch _ _ => forward_advise_if
  | Swhile _ _ => forward_advise_while
  | Sfor _ _ _ _ => forward_advise_loop s
  | Sloop _ _ => forward_advise_loop s
  | Scall _ (Evar _ _) _ =>  advise_forward_call
  | Sskip => forward_skip
  end.

Ltac derives_after_forward :=
             first [ simple apply derives_refl
                     | simple apply ENTAIL_refl
(*                     | simple apply normal_ret_assert_derives'' 
                     | simple apply normal_ret_assert_derives' *)
                     | idtac].

Ltac forward_break :=
eapply semax_pre; [ | apply semax_break ];
  unfold_abbrev_ret;
  simpl_ret_assert (*autorewrite with ret_assert*).

Ltac forward_continue :=
eapply semax_pre; [ | apply semax_continue ];
  unfold_abbrev_ret;
  simpl_ret_assert (*autorewrite with ret_assert*).

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
    lazymatch R with context [sepcon _ _ :: _] =>
        fail "The SEP clause of the precondition contains * (separating conjunction).
You must flatten the SEP clause, e.g. by doing [Intros],
or else hide the * by making a Definition or using a freezer"
       | _ => idtac
    end
  | |- semax _ (exp _) _ _ => 
             fail 3 "Before going 'forward', you need to move the existentially quantified variable at the head of your precondition 'above the line'.  Do this by the tactic 'Intros x', where 'x' is the name you want to give to this Coq variable"
  | |- _ => fail "Your precondition is not in canonical form (PROP (..) LOCAL (..) SEP (..))"
 end.

Ltac union_hack_message id1 id2 :=
 idtac "Converting numeric representations by the hack of storing to union-field" id1
"then loading from union-field" id2 ". See 'Union casting' in VC.pdf reference manual".

Ltac numeric_forward_store_union_hack id1 id2 :=
     eapply semax_seq';
     [ ensure_open_normal_ret_assert;
       hoist_later_in_pre;
       union_hack_message id1 id2;
       forward_store_union_hack id2
     | unfold replace_nth; abbreviate_semax].

Ltac union_message := 
 idtac "Suggestion: you are storing to one field of a union, then loading from another.  This is not always illegal.  See chapter 'Union casting' in the VC.pdf reference manual".

Ltac simple_forward_store_union_hack id2 :=
     eapply semax_seq';
     [ ensure_open_normal_ret_assert;
       hoist_later_in_pre;
       clear_Delta_specs; 
       sc_set_load_store.store_tac
     | union_message; unfold replace_nth; abbreviate_semax].

Ltac  try_forward_store_union_hack e1 s2 id1 t1 :=
 let s2' := eval hnf in s2 in
 lazymatch s2' with
 | Ssequence ?s3 _ => try_forward_store_union_hack e1 s3 id1 t1
 | Sset _ (Efield ?e2 ?id2 ?t2) =>
   tryif unify id1 id2 then fail else idtac;
   unify e1 e2;
   let t := constr:(typeof e1) in let t := eval hnf in t in
   match t with (Tunion _ _) =>
   tryif unify t1 t2 
   then simple_forward_store_union_hack id2
   else tryif unify (andb (is_numeric_type t1) (is_numeric_type t2)) true
      then numeric_forward_store_union_hack id1 id2
   else fail
  end
end.

Ltac forward :=
 lazymatch goal with
 | |- ENTAIL _, _ |-- _ * stackframe_of _ =>
     (* backward-compatibility hack *)
      clean_up_stackframe; entailer_for_return
 | |- _ =>
  try apply semax_ff;
  check_Delta; check_POSTCONDITION;
  repeat rewrite <- seq_assoc;
  lazymatch goal with 
  | |- semax _ _ (Ssequence (Sreturn _) _) _ =>
    apply semax_seq with FF; [ | apply semax_ff];
    clear_Delta_specs; forward_return
  | |- semax _ _ (Sreturn _) _ =>  clear_Delta_specs; forward_return
  | |- semax _ _ (Ssequence Sbreak _) _ =>
    apply semax_seq with FF; [ | apply semax_ff];  forward_break
  | |- semax _ _ (Ssequence Scontinue _) _ =>
    apply semax_seq with FF; [ | apply semax_ff];  forward_continue
  | |- semax _ _ Sbreak _ => forward_break
  | |- semax _ _ Scontinue _ => forward_continue
  | |- semax _ _ Sskip _ => fwd_skip
  | |- semax _ _ ?c0 _ =>
    match c0 with
    | Ssequence _ _ => idtac
    | _ => rewrite -> semax_seq_skip
    end;
    match goal with
    | |- semax _ _ (Ssequence (Sassign (Efield ?e1 ?id1 ?t1) _) ?s2) _ =>
           try_forward_store_union_hack e1 s2 id1 t1
    | |- semax _ _ (Ssequence ?c _) _ =>
      check_precondition;
      eapply semax_seq';
      [ forward1 c
      | fwd_result;
        Intros;
        abbreviate_semax;
        try (fwd_skip; try_clean_up_stackframe) ]
    end
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

Definition must_return (ek: exitkind) : bool :=
  match ek with EK_return => true | _ => false end.

Ltac make_func_ptr id :=
  eapply (make_func_ptr id);
  [ (reflexivity || fail 99  "Local variable " id " is shadowing the global variable" id)
  | (reflexivity || fail 99 "No specification of function " id " in Delta.  If the current function is a leaf function, you may need to invoke the [function_pointers] tactic before [start_function].  If that doesn't work, make sure you have not done clear_Delta_specs or [clearbody Delta_specs].")
  | (reflexivity || fail 99 "No global variable " id " in Delta, i.e., in your extern declarations")
  | split; reflexivity | ].

Lemma gvars_denote_HP':
 forall Delta P Q R gv i, 
  In (gvars gv) Q ->
  isSome ((glob_types Delta) ! i) ->
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- !! headptr (gv i).
Proof.
intros.
intro rho.
unfold local, lift1.
simpl.
normalize.
destruct ((glob_types Delta) ! i) eqn:?H; try contradiction.
eapply derives_trans.
apply in_local'; eassumption.
unfold local, lift1.
simpl.
apply prop_derives; intro.
eapply gvars_denote_HP; eauto.
Qed.

Ltac prove_headptr_gv :=
 first [simple apply gvars_denote_HP'; 
         [solve [repeat (try (left; reflexivity) || right)] | apply I ]
        | solve [entailer!]
       ].

Ltac change_mapsto_gvar_to_data_at' gv S :=
  match S with
  | context [mapsto ?sh ?t (offset_val 0 (gv ?i)) ?v] =>
      let H := fresh "H" in 
      assert_PROP (headptr (gv i)) as H;
          [prove_headptr_gv |];
      apply <- headptr_offset_zero in H;
      erewrite (mapsto_data_at'' _ _ _ _ (offset_val _ (gv i)));
          [| reflexivity | assumption | apply JMeq_refl ];
      clear H;
      rewrite <- ? data_at_offset_zero
  | context [mapsto ?sh ?t (gv ?i) ?v] =>
      let H := fresh "H" in 
      assert_PROP (headptr (gv i)) as H;
          [prove_headptr_gv |];
      erewrite (mapsto_data_at'' _ _ _ _ (gv i));
           [| reflexivity | assumption | apply JMeq_refl ];
      clear H
   end.

Ltac change_mapsto_gvar_to_data_at := 
match goal with
| gv: globals |- semax _ (PROPx _ (LOCALx ?L (SEPx ?S))) _ _ =>
                                           change_mapsto_gvar_to_data_at' gv S
| gv: globals |- ?S |-- _ => change_mapsto_gvar_to_data_at' gv S
end.

Ltac type_lists_compatible al bl :=
 match al with
 | Ctypes.Tcons ?a ?al' => match bl with Ctypes.Tcons ?b ?bl' => 
                 first [unify a b | unify (classify_cast a b) cast_case_pointer];
                 type_lists_compatible al' bl'
                end
 | Ctypes.Tnil => match bl with Ctypes.Tnil => idtac end
 end.

Ltac function_types_compatible t1 t2 :=
 match t1 with
 | Tfunction ?al1 ?r1 _ =>
  match t2 with Tfunction ?al2 ?r2 _ =>
     type_lists_compatible al1 al2;
     first [unify r1 r2 | unify (classify_cast r1 r2) cast_case_pointer]
 end end.

Ltac check_parameter_vals Delta al :=
 (* Work very carefully here to avoid simplifying or computing v,
    in case v contains something that will blow up *)
 match al with
 | temp ?i ?v :: ?al' =>
    let ti := constr:(PTree.get i (temp_types Delta)) in
    let ti := eval compute in ti in 
    match ti with
    | Some ?t =>
        let w := constr:(tc_val_dec t v) in
        let y := eval cbv beta iota delta [is_int_dec is_long_dec 
                         is_float_dec is_single_dec is_pointer_or_integer_dec
                         is_pointer_or_null_dec isptr_dec tc_val_dec] in w in
        match y with
          | right _ => fail 4 "Local variable" i "cannot hold the value" v "(wrong type)"
          | left _ => idtac
(*  optionally, give warning
          | _ => let W := fresh "Warning_could_not_prove_this_if_its_false_then_the_caller_wont_be_able_satisfy_the_function_precondition" in 
                       pose (W := tc_val t v)
*)
          | _ => idtac (* no optional warning *)
        end
    | None => fail 3 "Identifer" i "is not a local variable of this function"
    end;
    check_parameter_vals Delta al'
 | _ :: ?al' => check_parameter_vals Delta al'
 | nil => idtac
 end.

Fixpoint find_lvars (locals: list localdef)  (m: PTree.t unit) : PTree.t unit :=
 match locals with
 | lvar i _ _ :: locals'=> find_lvars locals' (PTree.set i tt m)
 | _ :: locals' => find_lvars locals' m
 | nil => m
 end.

Definition another_gvar (i: ident) (ml: PTree.t unit * list ident) : (PTree.t unit * list ident) :=
 match ml with (t,il) =>
  match PTree.get i t with Some _ => ml | None =>  (PTree.set i tt t, i :: il) end
 end.
Arguments another_gvar i !ml .

Ltac start_function_hint := idtac. (* "Hint: at any time, try the 'hint' tactic.  To disable this message, 'Ltac start_function_hint ::= idtac.' ". *)


Definition firstopt {A} (e1 e2: option A) := 
match e1 with None => e2 | Some x => Some x end.

Inductive diagnose_expr :=
|  DE_OK : diagnose_expr
|  DE_value: expr -> diagnose_expr
|  DE_copy: expr -> diagnose_expr
|  DE_nothing: expr -> diagnose_expr.

Definition DE_compose (e1 e2: diagnose_expr) := 
match e1 with DE_OK => e2 | _ => e1 end.

Definition diagnose_this_expr (m: mode) (e: expr) : diagnose_expr :=
 match m with
 | By_reference => DE_OK
 | By_copy => DE_copy e
 | By_value _ => DE_value e
 | By_nothing => DE_nothing e
 end.


Fixpoint check_norm_expr (e: expr) : diagnose_expr :=
match e with
 | Evar _ ty => diagnose_this_expr (access_mode ty) e
 | Ederef a ty => match access_mode ty with
                  | By_reference => if is_pointer_type (typeof a) 
                                               then check_norm_expr a
                                               else DE_value e
                  | m => diagnose_this_expr m e
                  end
| Eunop _ e _ => check_norm_expr e
| Ebinop _ e1 e2 _ => DE_compose (check_norm_expr e1) (check_norm_expr e2)
| Ecast e _ => check_norm_expr e
| Efield a _ ty => match access_mode ty with
                            | By_reference => check_norm_lvalue a
                            | m => diagnose_this_expr m e
                           end
| Eaddrof e _ => check_norm_lvalue e
| _ => DE_OK
end
with check_norm_lvalue (e: expr) : diagnose_expr :=
match e with
| Ederef a _ => if is_pointer_type (typeof a) 
                              then check_norm_expr a
                              else DE_value e
| Ecast e _ => check_norm_lvalue e
| Efield e _ _ => check_norm_lvalue e
| Eunop _ e _ => check_norm_expr e
| Ebinop _ e1 e2 _ => DE_compose (check_norm_expr e1) (check_norm_expr e2)
| _ => DE_OK
end.

Fixpoint check_norm_stmt (s: statement) : diagnose_expr :=
match s with
| Sassign e1 e2 => DE_compose (check_norm_lvalue e1) (check_norm_expr e2)
| Sset _ e1 => check_norm_lvalue e1
| Scall _ (Evar _ _) el => fold_right DE_compose DE_OK (map check_norm_expr el)
| Scall _ e el => fold_right DE_compose DE_OK (map check_norm_expr (e::el))
| Sbuiltin _ _ _ el => fold_right DE_compose DE_OK (map check_norm_expr el)
| Ssequence s1 s2 => DE_compose (check_norm_stmt s1) (check_norm_stmt s2)
| Sifthenelse e s1 s2 => DE_compose (check_norm_expr e) (DE_compose (check_norm_stmt s1) (check_norm_stmt s2))
| Sloop s1 s2 => DE_compose (check_norm_stmt s1) (check_norm_stmt s2)
| Sreturn (Some e) => check_norm_expr e
| Sswitch e ls => DE_compose (check_norm_expr e)
                              (check_norm_ls ls)
| _ => DE_OK
end
with
check_norm_ls (ls: labeled_statements) : diagnose_expr :=
match ls with 
| LSnil => DE_OK 
| LScons _ s1 sr => DE_compose (check_norm_stmt s1) (check_norm_ls sr)
end.

Ltac check_normalized f := 
let x := constr:(check_norm_stmt (fn_body f)) in
let x := eval hnf in x in
match x with 
| DE_OK => idtac
| DE_value ?e => fail 99 "The expression " e " contains internal memory dereferences, which suggests that you ran clightgen without the -normalize flag.  Print Info.normalized and make sure it has the value 'true'"
| DE_copy ?e => fail 99 "The expression " e " contains internal structure-copying, a feature of C not currently supported in Verifiable C"
| DE_nothing ?e => fail 99 "The expression " e " contains a dereference of an expression with a 'By_nothing' access mode, which is quite unexpected"
end.

(*DEAD?
Lemma elim_close_precondition:
  forall {CS: compspecs} {Espec: OracleKind} al Delta P F c Q,
   closed_wrt_vars (fun i => ~ In i al) P  ->
   closed_wrt_lvars (fun _ => True) P ->    
   semax Delta (P * F) c Q ->
   semax Delta (close_precondition al al P * F) c Q.
Proof.
intros.
 apply semax_pre with (P*F); auto.
 apply andp_left2.
 apply sepcon_derives; [ | apply derives_refl].
 intro rho.
 apply Clight_seplog.close_precondition_e'; auto.
Qed.*)

Lemma elim_close_precondition:
  forall {CS: compspecs} {Espec: OracleKind} al Delta P F c Q,
   semax Delta ((argsassert2assert al P) * F) c Q ->
   semax Delta (close_precondition al P * F) c Q.
Proof.
intros.
 apply semax_pre with ((argsassert2assert al P)*F); auto.
 apply andp_left2.
 apply sepcon_derives; [ clear H | apply derives_refl].
 intro rho. unfold close_precondition, argsassert2assert.
 normalize. apply derives_refl'. f_equal. f_equal.
  unfold eval_id. simpl. clear - H. generalize dependent vals.
 induction al; simpl; intros; destruct vals; trivial; inv H.
 rewrite (IHal _ H2), H1; trivial.
Qed.

Ltac check_parameter_types' :=
 try reflexivity;
 simpl;
 match goal with |- ?A = ?B =>
   fail "Parameter types of funspec don't match types of fundef.
funspec:" A "
fundef:" B
  end.

Ltac check_return_type :=
 try reflexivity;
 simpl;
 match goal with |- ?A = ?B =>
   fail "Return type of funspec doesn't match return type of fundef.
funspec:" A "
fundef:" B
  end.

Fixpoint rename_ident (olds news: list ident) i :=
 match olds, news with
 | a::al, b::bl => if ident_eq i a then Some b else rename_ident al bl i
 | _,_ => None
 end.

Fixpoint rename_localdefs (olds news: list ident) (ds: list localdef) : option (list localdef) :=
 match ds with
 | temp i v :: ds' => match rename_ident olds news i, rename_localdefs olds news ds' with
                              | Some j, Some r => Some (temp j v::r)
                              | _, _ => None
                              end
 | lvar _ _ _ :: _ => None
 | gvars gv ::ds' => match rename_localdefs olds news ds' with
                  | Some r => Some (gvars gv :: r)
                  | None => None
                  end
 | nil => Some nil
 end.

(*DEAD?
Lemma compute_close_precondition: 
  forall olds news P Q Q' R,
  compute_list_norepet olds = true ->
  rename_localdefs olds news Q = Some Q' ->
  Clight_seplog.close_precondition olds news (PROPx P (LOCALx Q (SEPx R))) =
    (PROPx P (LOCALx Q' (SEPx R))).
Proof.
intros *. intros Hno. intros.
apply compute_list_norepet_e in Hno.
extensionality rho.
apply predicates_hered.pred_ext.
-
 intros ? [ve' [te' [? ?]]].
 destruct H1; split; auto. clear H1.
 destruct H2; split; auto. clear H2.
 revert Q' H H1; induction Q; intros; destruct Q'.
 inv H.
 apply H1.
 inv H.
 elimtype False; clear - H. destruct a0; simpl in H.
 destruct (rename_ident olds news i); try discriminate.
 destruct (rename_localdefs olds news Q); try discriminate.
 destruct (rename_localdefs olds news Q); try discriminate.
 destruct (rename_localdefs olds news Q); try discriminate.
 simpl in H.
 destruct (rename_localdefs olds news Q) eqn:H3.
2:{ destruct a0; try discriminate. destruct (rename_ident olds news i); discriminate. }
 destruct H1.
 split.
2:{ apply IHQ; auto. clear - H. destruct a0; try solve [inv H; auto].
     destruct (rename_ident olds news i); inv H; auto.
  }
 clear dependent Q.
 destruct a0.
 2,3: inv H; apply H1.
 destruct (rename_ident olds news i) eqn:?H; try discriminate.
 inv H.
 clear - H2 H1 H0.
 hnf in H1|-*. unfold_lift in *. destruct H1; subst v.
 split; auto.
 clear H1.
 unfold eval_id in *; simpl in *.
 f_equal.
 revert news H2 H0; induction olds; destruct news; simpl; intros; inv H2.
 if_tac in H1. inv H1.
 rewrite (H0 O a i0); auto.
 apply (IHolds news); auto.
 intros. apply (H0 (S n)); auto.
-
intros ? ?.
exists (ve_of rho).
destruct rho as [ge ve te].
simpl te_of.
pose (f (i: ident) := 
      match rename_ident olds news i with
      | Some j => Map.get te j
      | None => None
      end).
exists f.
split; simpl.
 *
 clear - Hno.
 unfold Map.get in *.
 subst f.
 intros.
 simpl.
 revert olds news i j H H0 Hno; induction n; destruct olds, news; simpl; intros; try discriminate.
 inv H0. inv H. rewrite if_true by auto. auto.
 inv Hno.
 if_tac.
 subst.
 apply nth_error_in in H. contradiction.
 apply (IHn _ _ _ _ H H0 H4).
 *
  destruct H0 as [? [? ?]]; split3; auto.
 clear - Hno H H1.
 revert Q' H H1; induction Q; destruct Q'; simpl; intros; auto.
 inv H.
 elimtype False; clear - H.
 destruct a0; try discriminate;
 try destruct (rename_ident olds news i); try discriminate;
 destruct (rename_localdefs olds news Q); discriminate.
 destruct H1.
 destruct (rename_localdefs olds news Q) eqn:?H.
2:{ destruct a0; try discriminate; destruct (rename_ident olds news i); try discriminate. }
  assert (l0 = Q'). { destruct a0; inv H; auto. 
      destruct (rename_ident olds news i); inv H4; auto.
  }
 subst l0. 
 split; [ | apply (IHQ Q'); auto].
 destruct a0; try solve [inv H; auto].
 destruct (rename_ident olds news i) eqn:?H; inv H.
 hnf in H0|-*. unfold_lift in *.
 destruct H0; subst. split; auto.
 unfold eval_id; simpl. f_equal.
 unfold Map.get; subst f.
 simpl. rewrite H3. reflexivity.
Qed.
*)

Fixpoint computeQ (ids:list ident) (vals:list val) : option (list localdef) :=
  match ids, vals with
    nil, nil => Some nil
  | (i::ids'), (v::vals') => match computeQ ids' vals' with
                              None => None
                            | Some defs => Some (temp i v :: defs)
                            end
  | _, _ => None
  end.

Lemma compute_close_precondition_entails1: 
  forall ids P gv vals Q R,
  compute_list_norepet ids = true ->
  computeQ ids vals = Some Q ->
  PROPx P (LOCALx ((map gvars gv)++Q) (SEPx R))
  |-- close_precondition ids (PROPx P (LAMBDAx gv vals (SEPx R))).
Proof.
intros. rewrite <- insert_locals. intros rho. unfold close_precondition; normalize. 
Exists vals. unfold GLOBALSx, PARAMSx. simpl.
  unfold argsassert2assert.
  unfold PROPx, LOCALx, SEPx. simpl. normalize.  
  apply andp_right.
  { apply andp_left2. apply andp_left1. unfold local, liftx, lift1, lift; simpl.
    apply prop_derives; intros.
    assert (AUX: map (Map.get (te_of rho)) ids = map Some vals /\
            Forall (fun v : val => v <> Vundef) vals).
    { generalize dependent Q. generalize dependent vals.
      induction ids; simpl; intros.
      - destruct vals; inv H0. simpl; split; trivial.
      - destruct vals; inv H0. remember (computeQ ids vals) as t; destruct t; try discriminate. inv H4.
        symmetry in Heqt. inv H.
        remember (id_in_list a ids) as b; symmetry in Heqb; destruct b. discriminate. destruct H2.
        destruct (IHids H3 _ _ Heqt) as [X1 X2]; simpl; trivial.
        red in H. unfold eval_id, liftx, lift in H. simpl in H. destruct H.
        unfold force_val in H. destruct (Map.get (te_of rho) a); [subst | congruence].
        rewrite X1. split; auto. }
     clear - H1 AUX; intuition. }
  apply andp_right.
  { apply andp_left1. clear. unfold local, liftx, lift1, lift; simpl. apply prop_derives; intros.
    unfold Clight_seplog.mkEnv; simpl. unfold seplog.globals_only; simpl.
    induction gv; simpl in *. trivial. destruct H.
    split; auto. }
  do 2 apply andp_left2; trivial.
Qed.

Lemma compute_close_precondition_entails2: 
  forall ids P gv vals Q R,
  compute_list_norepet ids = true ->
  computeQ ids vals = Some Q ->
  close_precondition ids (PROPx P (LAMBDAx gv vals (SEPx R)))
  |--  (PROPx P (LOCALx ((map gvars gv)++Q) (SEPx R))).
Proof.
intros. rewrite <- insert_locals. intros rho. unfold close_precondition; normalize.
unfold GLOBALSx, PARAMSx, argsassert2assert, PROPx, LOCALx, SEPx. simpl. normalize. 
  apply andp_right.
  { apply andp_left1. unfold Clight_seplog.mkEnv. simpl.
    unfold seplog.globals_only; simpl. unfold local, liftx, lift1, lift; simpl. clear.
    apply prop_derives; intros.
    induction gv; simpl in *; trivial.
    unfold gvars_denote in *; simpl in *; destruct H. split; auto. } 
  apply andp_derives; trivial.
  unfold local, liftx ,lift1, lift; simpl. apply prop_right. clear - H H0 H1 H2.
  generalize dependent Q. generalize dependent vals.
  induction ids; simpl; intros.
  - destruct vals; inv H0. simpl; trivial.
  - destruct vals; inv H0. remember (computeQ ids vals) as t; destruct t; try discriminate. inv H4.
    symmetry in Heqt. inv H; inv H1; inv H2.
    remember (id_in_list a ids) as b; symmetry in Heqb; destruct b. discriminate.
    split; [ red | eauto].
    unfold liftx, lift; simpl. unfold eval_id. rewrite H0. split; trivial.
Qed.

Lemma compute_close_precondition_eq:
  forall ids P gv vals Q R,
  compute_list_norepet ids = true ->
  computeQ ids vals = Some Q ->
  close_precondition ids (PROPx P (LAMBDAx gv vals (SEPx R)))
  = (PROPx P (LOCALx ((map gvars gv)++Q) (SEPx R))).
Proof. intros.
  apply pred_ext. eapply compute_close_precondition_entails2; trivial.
  eapply compute_close_precondition_entails1; trivial.
Qed.

Lemma semax_elim_close_precondition:
  forall {CS: compspecs} {Espec: OracleKind} ids Delta P gv vals R F c Q T,
  compute_list_norepet ids = true ->
  computeQ ids vals = Some Q ->
   semax Delta (PROPx P (LOCALx ((map gvars gv)++Q) (SEPx R)) * F) c T ->
   semax Delta (close_precondition ids ((PROPx P (LAMBDAx gv vals (SEPx R)))) * F) c T.
Proof.
intros. erewrite compute_close_precondition_eq; [ | eassumption | eassumption ]; trivial.
Qed.

Ltac start_func_convert_precondition := idtac.
Ltac rewrite_old_main_pre := idtac.

Ltac start_function1 :=
 leaf_function;
 lazymatch goal with |- semax_body ?V ?G ?F ?spec =>
    check_normalized F;
    function_body_unsupported_features F;
    let s := fresh "spec" in
    pose (s:=spec); hnf in s; cbn zeta in s; (* dependent specs defined with Program Definition often have extra lets *)
   repeat lazymatch goal with
    | s := (_, NDmk_funspec _ _ _ _ _) |- _ => fail
    | s := (_, mk_funspec _ _ _ _ _ _ _) |- _ => fail
    | s := (_, ?a _ _ _ _) |- _ => unfold a in s
    | s := (_, ?a _ _ _) |- _ => unfold a in s
    | s := (_, ?a _ _) |- _ => unfold a in s
    | s := (_, ?a _) |- _ => unfold a in s
    | s := (_, ?a) |- _ => unfold a in s
    end;
    lazymatch goal with
    | s :=  (_,  WITH _: globals
               PRE  [] main_pre _ _ _
               POST [ tint ] _) |- _ => idtac
    | s := ?spec' |- _ => check_canonical_funspec spec'
   end;
   change (semax_body V G F s); subst s;
   unfold NDmk_funspec'
 end;
 let DependedTypeList := fresh "DependedTypeList" in
 unfold NDmk_funspec; 
 match goal with |- semax_body _ _ _ (pair _ (mk_funspec _ _ _ ?Pre _ _ _)) =>

   split3; [check_parameter_types' | check_return_type | ];
    match Pre with
   | (fun _ => convertPre _ _ (fun i => _)) =>  intros Espec DependedTypeList i
   | (fun _ x => match _ with (a,b) => _ end) => intros Espec DependedTypeList [a b]
   | (fun _ i => _) => intros Espec DependedTypeList i
   end;
   simpl fn_body; simpl fn_params; simpl fn_return
 end;
 try match goal with |- semax _ (fun rho => ?A rho * ?B rho) _ _ =>
     change (fun rho => ?A rho * ?B rho) with (A * B)
  end;
 simpl functors.MixVariantFunctor._functor in *;
 simpl rmaps.dependent_type_functor_rec;
 clear DependedTypeList;
 rewrite_old_main_pre;
 repeat match goal with
 | |- @semax _ _ _ (match ?p with (a,b) => _ end * _) _ _ =>
             destruct p as [a b]
 | |- @semax _ _ _ (close_precondition _ match ?p with (a,b) => _ end * _) _ _ =>
             destruct p as [a b]
 | |- @semax _ _ _ ((match ?p with (a,b) => _ end) eq_refl * _) _ _ =>
             destruct p as [a b]
 | |- @semax _ _ _ (close_precondition _ ((match ?p with (a,b) => _ end) eq_refl) * _) _ _ =>
             destruct p as [a b]
 | |- semax _ (close_precondition _
                                                (fun ae => !! (Datatypes.length (snd ae) = ?A) && ?B
                                                      (make_args ?C (snd ae) (mkEnviron (fst ae) _ _))) * _) _ _ =>
          match B with match ?p with (a,b) => _ end => destruct p as [a b] end
       end;
(* this speeds things up, but only in the very rare case where it applies,
   so maybe not worth it ...
  repeat match goal with H: reptype _ |- _ => progress hnf in H; simpl in H; idtac "reduced a reptype" end;
*)
 try start_func_convert_precondition.

(* first [apply elim_close_precondition; [solve [auto 50 with closed] | solve [auto 50 with closed] | ]
        | erewrite compute_close_precondition by reflexivity];*)

Ltac expand_main_pre := expand_main_pre_old.

Ltac start_function2 :=
  first [ erewrite compute_close_precondition_eq; [ | reflexivity | reflexivity]
        | rewrite close_precondition_main ].

Ltac start_function3 :=
 simpl app;
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
 try simple apply start_function_aux1;
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
 abbreviate_semax;
 lazymatch goal with 
 | |- semax ?Delta (PROPx _ (LOCALx ?L _)) _ _ => check_parameter_vals Delta L
 | _ => idtac
 end;
 try match goal with DS := @abbreviate (PTree.t funspec) ?DS1 |- _ =>
     unify DS1 (PTree.empty funspec); clearbody DS
 end;
 start_function_hint.

Ltac start_function :=
  start_function1;
  start_function2; 
  start_function3.

Opaque sepcon.
Opaque emp.
Opaque andp.

Arguments overridePost Q R / .
Arguments eq_dec A EqDec / a a' .
Arguments EqDec_exitkind !a !a'.

(**** make_compspecs ****)

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

Lemma legal_alignas_env_consistency': forall (cenv : composite_env) (ha_env : PTree.t Z) (la_env: PTree.t legal_alignas_obs),
  composite_env_consistent cenv ->
  la_env = legal_alignas_env cenv ha_env ->  
  legal_alignas_env_consistent cenv ha_env la_env.
Proof.
  intros.
  subst.
  apply legal_alignas_env_consistency; auto.
Qed.

Lemma legal_alignas_env_completeness': forall (cenv : composite_env) (ha_env : PTree.t Z) (la_env: PTree.t legal_alignas_obs),
  la_env = legal_alignas_env cenv ha_env ->  
  legal_alignas_env_complete cenv la_env.
Proof.
  intros.
  subst.
  apply legal_alignas_env_completeness; auto.
Qed.

Lemma Zgeb0_ge0: forall n, Z.geb n 0 = true -> n >= 0.
Proof.
intros.
apply Z.geb_le in H. lia.
Qed.

Lemma prove_alignof_two_p (i: Z) : 
    i = two_power_nat (Nat.log2_up (Z.to_nat i)) ->
exists n: nat, i = two_power_nat n.
Proof.
intros. eexists; eassumption.
Qed.

Lemma prove_Zdivide (a b: Z): b = Z.mul (Z.div b a) a -> Z.divide a b.
Proof.
intros. eexists. eassumption.
Qed.

Ltac simplify_composite_of_def d :=
   let d := eval hnf in d in
  match d with
 Errors.OK 
   {|  co_su := ?su;
       co_members := ?m;
       co_attr := ?a;
       co_sizeof := ?sz;
       co_alignof := ?al;
       co_rank := ?rank;
       co_sizeof_pos := _;
       co_alignof_two_p := _;
       co_sizeof_alignof := _ |}  =>
  let sz := eval compute in sz in 
  let al := eval compute in al in 
  let rank := eval compute in rank in 
  let sp := constr:(Zgeb0_ge0 sz (eq_refl _)) in 
  let altwo := constr:(prove_alignof_two_p al (eq_refl _)) in
  let sa := constr:(prove_Zdivide al sz (eq_refl _)) in
   let d := constr:({|  co_su := su;
       co_members := m;
       co_attr := a;
       co_sizeof := sz;
       co_alignof := al;
       co_rank := rank;
       co_sizeof_pos := sp;
       co_alignof_two_p := altwo;
       co_sizeof_alignof := sa |})
  in
 d
end.

Ltac simplify_add_composite_definitions env cl :=  
 match cl with
 | Composite ?id ?su ?m ?a :: ?cl' =>
    let d := constr:(composite_of_def env id su m a)
    in let d' := simplify_composite_of_def d
       in let env' :=  constr:(PTree.set id d' env)
        in let env' := eval simpl in env' in 
       simplify_add_composite_definitions env' cl'
 | nil => constr:(Errors.OK env)
end.

Ltac make_composite_env composites :=
let j := constr:(build_composite_env' composites I)
in let j := eval cbv beta iota zeta delta [
       build_composite_env' build_composite_env
       PTree.empty
      ] in j
 in  match j with context C [add_composite_definitions ?empty ?c] =>
             let cd := simplify_add_composite_definitions empty c in 
             cd
     end.

Ltac make_composite_env0 prog :=
let c := constr:(prog_types prog) in
let c := eval unfold prog, prog_types, Clightdefs.mkprogram in c in 
let comp := match c with
                  | context [build_composite_env' ?comp I] => 
                     let j := eval unfold comp in comp in constr:(j)
                  | _ :: _ => constr:(c)
                  | nil => constr:(c)
                  end in 
let comp' := make_composite_env comp
   in match comp' with Errors.OK ?ce =>
            ce
       end.

Ltac make_compspecs_cenv cenv :=
  let cenv := eval hnf in cenv in
  let cenv := eval simpl in cenv in 
  let cenv_consistent_ := constr:((composite_env_consistent_i composite_consistent cenv ltac:(repeat constructor)): composite_env_consistent cenv) in
  let cenv_legal_fieldlist_ := constr:((composite_env_consistent_i' composite_legal_fieldlist cenv ltac:(repeat constructor)): composite_env_legal_fieldlist cenv) in
  let cenv_legal_su_ := constr:((composite_env_consistent_i (fun c co => composite_complete_legal_cosu_type c (co_members co) = true) cenv ltac:(repeat constructor)): composite_env_complete_legal_cosu_type cenv) in
  let ha_env := eval cbv in (hardware_alignof_env cenv) in
  let Hha_env := constr: (eq_refl: ha_env = hardware_alignof_env cenv) in
  let ha_env_consistent := constr: (hardware_alignof_consistency cenv ha_env cenv_consistent_ Hha_env) in
  let ha_env_complete := constr: (hardware_alignof_completeness cenv ha_env Hha_env) in
  let la_env := eval cbv in (legal_alignas_env cenv ha_env) in
  let Hla_env := constr: (eq_refl: la_env = legal_alignas_env cenv ha_env) in
  let la_env_consistent := constr: (legal_alignas_env_consistency' cenv ha_env la_env cenv_consistent_ Hla_env) in
  let la_env_complete := constr: (legal_alignas_env_completeness' cenv ha_env la_env Hla_env) in
  let la_env_sound := constr: (legal_alignas_soundness cenv ha_env la_env cenv_consistent_ cenv_legal_su_ ha_env_consistent ha_env_complete la_env_consistent la_env_complete) in
  exact (  {| cenv_cs := cenv ;
    cenv_consistent := cenv_consistent_;
    cenv_legal_fieldlist := cenv_legal_fieldlist_;
    cenv_legal_su := cenv_legal_su_;
    ha_env_cs := ha_env;
    ha_env_cs_consistent := ha_env_consistent;
    ha_env_cs_complete := ha_env_complete;
    la_env_cs := la_env;
    la_env_cs_consistent := la_env_consistent;
    la_env_cs_complete := la_env_complete;
    la_env_cs_sound := la_env_sound
   |}).

Ltac make_compspecs prog :=
  let cenv := make_composite_env0 prog in
  make_compspecs_cenv cenv.

Fixpoint missing_ids {A} (t: PTree.tree A) (al: list ident) :=
  match al with
  | a::al' => match PTree.get a t with None => a::nil | _ => nil end ++
                 missing_ids t al'
  | nil => nil
 end.

Ltac simpl_prog_defs p := 
 match p with
 | context C [prog_defs (Clightdefs.mkprogram _ ?d _ _ _)] =>
       let q := context C [d] in q
 | context C [prog_defs ({| prog_defs := ?d |})] =>
       let q := context C [d] in q
  end.

Definition duplicate_ids (il: list ident) : list ident :=
 let ptree_incr := fun t id => 
        match PTree.get id t with
        | Some _ => PTree.set id (true,id) t
        | None => PTree.set id (false,id) t
        end
  in let t := List.fold_left ptree_incr il (PTree.empty (bool*ident))
  in let dl := PTree.fold (fun (dl: list ident) (id: ident) (b: bool*ident) => 
                      if fst b then (snd b)::dl else dl) t nil
  in dl.

Ltac old_with_library' p G :=
  let g := eval hnf in G in
  let x := constr:(augment_funspecs' (prog_funct p) g) in
  let x := eval cbv beta iota zeta delta [prog_funct] in x in 
  let x := simpl_prog_defs x in 
  let x := eval hnf in x in
  match x with
  | Some ?l => constr:(l)
  | None => 
   let t := constr:(List.fold_right (fun i t => PTree.set i tt t) (PTree.empty _)
                           (map fst (prog_funct p))) in
   let t := eval compute in t in
   let missing := constr:(missing_ids t (map fst G)) in
   let missing := eval simpl in missing in
   let dups := constr:(duplicate_ids (map fst G))
   in let dups := eval hnf in dups in 
   let dups := eval simpl in dups in
   lazymatch dups with
   | nil => idtac
   | _::_ => fail "Duplicate funspecs:" dups
   end;
   lazymatch missing with
   | nil => fail "Superfluous funspecs?"
   | _ => fail  "The following names have funspecs but no function definitions: " missing
  end
 end.

Ltac old_with_library prog G :=
  let pr := eval unfold prog in prog in
  let x := old_with_library' pr G in exact x.

Definition ptree_incr (s:PTree.t(bool*ident)) (id:ident) := 
        match PTree.get id s with
        | Some _ => PTree.set id (true,id) s
        | None => PTree.set id (false,id) s
        end.

Ltac with_library' p G :=
   let t := constr:(List.fold_right (fun i t => PTree.set i tt t) (PTree.empty _)
                           (map fst (prog_funct p))) in
   let t := eval compute in t in
   let missing := constr:(missing_ids t (map fst G)) in
   let missing := eval simpl in missing in
   let t := constr:(List.fold_left ptree_incr (map fst G) (PTree.empty (bool*ident))) in
   let t := eval compute in t in 
   let dups := constr:(PTree.fold (fun (dl: list ident) (id: ident) (b: bool*ident) => 
                      if fst b then (snd b)::dl else dl) t nil) in
   let dups := eval simpl in dups in 
   lazymatch dups with
   | nil => idtac
   | _::_ => fail "Duplicate funspecs:" dups
   end;
   lazymatch missing with
   | nil => idtac
   | _ => idtac  "Warning: The following names have funspecs but no function definitions: " missing
  end;
  let x := eval hnf in G in
  exact x.

Ltac with_library prog G :=
  let pr := eval unfold prog in prog in  with_library' pr G.

Definition semax_prog {Espec} {CS} prog z V G :=
 @SeparationLogicAsLogicSoundness.MainTheorem.CSHL_MinimumLogic.CSHL_Defs.semax_prog
  Espec CS prog z V (augment_funspecs prog G).

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

Ltac prove_semax_prog_old :=
 split3; [ | | split3; [ | | split]];
 [ reflexivity || fail "duplicate identifier in prog_defs"
 | reflexivity || fail "unaligned initializer"
 | solve [compute; repeat f_equal; apply proof_irr] || fail "comp_specs not equal"
 |
 | reflexivity || fail "match_globvars failed"
 | match goal with |- match ?A with _ => _ end =>
      let fs := fresh "fs" in set (fs := A); hnf in fs; subst fs; cbv iota beta;
      lazymatch goal with
      | |- False => fail "Can't find _main in Gprog" 
      | |- _ =>  idtac 
      end;
      (eexists; reflexivity) || 
        fail "Funspec of _main is not in the proper form"
    end
 ];
 repeat (eapply semax_func_cons_ext_vacuous; [reflexivity | reflexivity | reflexivity | LookupID | LookupB | ]).

(**************MATERIAL FOR NEW TACTIC prove_semax_prog STARTS HERE ***************)

Lemma extract_prog_main t d p m w:
  prog_main (Clightdefs.mkprogram t d p m w) = m.
Proof.
  unfold Clightdefs.mkprogram.
  destruct (build_composite_env' t w).
  reflexivity.
Qed.

Lemma extract_prog_main' {F} defs publics main types compenv prf:
  @prog_main F {| prog_defs := defs; prog_public := publics; prog_main:=main; prog_types:=types;
                     prog_comp_env := compenv; prog_comp_env_eq := prf |} = main.
Proof. reflexivity. Qed.

Lemma extract_compEnv t a (H: build_composite_env t = Errors.OK a)
      d p m w:
  a = prog_comp_env (Clightdefs.mkprogram t d p m w).
Proof.
  unfold Clightdefs.mkprogram.
  destruct (build_composite_env' t w). 
  rewrite e in H. inv H. reflexivity.
Qed.

Ltac match_composite :=
  match goal with
  | |- {| co_su := ?co_su1;
         co_members := ?co_members1;
         co_attr := ?co_attr1;
         co_sizeof := ?co_size1 ;
         co_alignof := ?co_alignof1;
         co_rank := ?co_rank1;
         co_sizeof_pos := ?co_sizeof_pos_proof1;
         co_alignof_two_p := ?co_alignof_two_p_proof1;
         co_sizeof_alignof := ?co_sizeof_alignof_proof1
      |} =
      {| co_su := ?co_su2;
         co_members := ?co_members2;
         co_attr := ?co_attr2;
         co_sizeof := ?co_size2 ;
         co_alignof := ?co_alignof2;
         co_rank := ?co_rank2;
         co_sizeof_pos := ?co_sizeof_pos_proof2;
         co_alignof_two_p := ?co_alignof_two_p_proof2;
         co_sizeof_alignof := ?co_sizeof_alignof_proof2
      |} =>
    replace co_sizeof_pos_proof1
      with co_sizeof_pos_proof2;
    replace co_alignof_two_p_proof1
      with co_alignof_two_p_proof2;
    replace co_sizeof_alignof_proof1
      with co_sizeof_alignof_proof2
  end.

Lemma add_composite_definitions_nil env: add_composite_definitions env nil = Errors.OK env.
Proof. reflexivity. Qed.

Definition mk_OKComposite env su m a al PR1 PR2 PR3 : composite:=
    {|
       co_su := su;
       co_members := m;
       co_attr := a;
       co_sizeof := align (sizeof_composite env su m) al;
       co_alignof := al;
       co_rank := rank_members env m;
       co_sizeof_pos := PR1;
       co_alignof_two_p := PR2;
       co_sizeof_alignof := PR3 |}.
  
Lemma composite_abbrv env id su m a: composite_of_def env id su m a = 
  match env ! id with
  | Some _ => Errors.Error [Errors.MSG "Multiple definitions of struct or union "; Errors.CTX id]
  | None => if complete_members env m
            then let al := align_attr a (alignof_composite env m) in
            Errors.OK (mk_OKComposite env su m a al
                  ((fun (env0 : composite_env) (_ : ident) (su0 : struct_or_union) (m0 : members) (a0 : attr) =>
                         Ctypes.composite_of_def_obligation_1 env0 su0 m0 a0) env id su m a)
                  ((fun (env0 : composite_env) (_ : ident) (_ : struct_or_union) (m0 : members) (a0 : attr) =>
                            Ctypes.composite_of_def_obligation_2 env0 m0 a0) env id su m a)
                  ((fun (env0 : composite_env) (_ : ident) (su0 : struct_or_union) (m0 : members) (a0 : attr) =>
                             Ctypes.composite_of_def_obligation_3 env0 su0 m0 a0) env id su m a))
            else Errors.Error [Errors.MSG "Incomplete struct or union "; Errors.CTX id]
  end.
Proof. reflexivity. Qed.

Ltac solve_cenvcs_goal :=
apply (f_equal (@PTree.elements composite));
apply extract_compEnv;
  match goal with
  | |- build_composite_env ?com = Errors.OK ?cenv_cs =>
    unfold build_composite_env, com
  end;
 repeat lazymatch goal with
| |- add_composite_definitions ?env nil = _ =>
 let e := eval hnf in env in let e := eval simpl in e in 
 change env with e; reflexivity
| |- 
 add_composite_definitions ?env (Composite ?id ?su ?m ?a :: ?defs0) = _ =>
 let e := eval hnf in env in let e := eval simpl in e in 
 let c := constr:(composite_of_def e id su m a) in
 let c := eval hnf in c in 
change (add_composite_definitions env (Composite id su m a :: defs0))
 with (Errors.bind c
           (fun co => add_composite_definitions (PTree.set id co e) defs0));
 match c with Errors.OK
 {| co_su := _; co_members := ?m; co_attr := _;
   co_sizeof := ?s; co_alignof := ?a; co_rank := ?r;
   co_sizeof_pos := ?sp; co_alignof_two_p := ?atp;
   co_sizeof_alignof := ?sa |} =>
  let s' := eval compute in s in change s with s';
  let a' := eval compute in a in change a with a';
  let r' := eval compute in r in change r with r';
  replace sp with (Zgeb0_ge0 s' eq_refl) by apply proof_irr;
  replace atp with (prove_alignof_two_p a' eq_refl) by apply proof_irr;
  replace sa with (prove_Zdivide a' s' eq_refl) by apply proof_irr
 end;
 unfold Errors.bind at 1
| |- _ => fail "Unexpected error in solve_cenvcs_goal"
end.

Ltac prove_semax_prog_setup_globalenv :=
let P := fresh "P" in
let Gsymb := fresh "Gsymb" in let Gsymb' := fresh "Gsymb'" in 
let GS := fresh "GS" in
let Gdefs := fresh "Gdefs" in let Gdefs' := fresh "Gdefs'" in 
let GD := fresh "GD" in
 set (P := Genv.globalenv _);
 pose (Gsymb :=Genv.genv_symb P);
 pose (Gsymb' := @abbreviate _ Gsymb);
 assert (GS := eq_refl Gsymb');
 unfold Gsymb' at 1, abbreviate, Gsymb in GS;
 compute in Gsymb; subst Gsymb; subst Gsymb';
 pose (Gdefs :=Genv.genv_defs P);
 pose (Gdefs' := @abbreviate _ Gdefs);
 assert (GD := eq_refl Gdefs');
 unfold Gdefs' at 1, abbreviate, Gdefs in GD;
 compute in Gdefs; subst Gdefs; subst Gdefs';
 clearbody P.

Ltac prove_semax_prog_aux tac :=
  match goal with
    | |- semax_prog ?prog ?z ?Vprog ?Gprog =>
     let pr := eval unfold prog in prog in
     let x := old_with_library' pr Gprog
     in change ( SeparationLogicAsLogicSoundness.MainTheorem.CSHL_MinimumLogic.CSHL_Defs.semax_prog
                    prog z Vprog x)
  end;
 split3; [ | | split3; [ | | split]];
 [ fast_Qed_reflexivity || fail "duplicate identifier in prog_defs"
 | fast_Qed_reflexivity || fail "unaligned initializer"
 | solve [solve_cenvcs_goal || fail "comp_specs not equal"]
   (*compute; repeat f_equal; apply proof_irr] || fail "comp_specs not equal"*)
 |
 | fast_Qed_reflexivity || fail "match_globvars failed"
 | match goal with
     |- match initial_world.find_id (prog_main ?prog) ?Gprog with _ => _ end =>
     unfold prog at 1; (rewrite extract_prog_main || rewrite extract_prog_main');
     ((hnf; eexists;
      try match goal with |- snd ?A = _ => let j := fresh in set (j:=A); hnf in j; subst j; unfold snd at 1 end;
      try (unfold NDmk_funspec'; rewrite_old_main_pre); reflexivity) || 
        fail "Funspec of _main is not in the proper form")
    end
 ]; 
 match goal with |- semax_func ?V ?G ?g ?D ?G' =>
   let Gprog := fresh "Gprog" in 
   pose (Gprog := @abbreviate _ G); 
  change (semax_func V Gprog g D G')
 end;
  prove_semax_prog_setup_globalenv;
 tac.

Ltac finish_semax_prog := 
 repeat (eapply semax_func_cons_ext_vacuous; 
   [fast_Qed_reflexivity | reflexivity | LookupID | LookupB | ]).

Ltac prove_semax_prog := prove_semax_prog_aux finish_semax_prog.

(*******************************************)

Ltac reassociate_to c1 c2  n :=
 match n with 
 | O => constr:(Ssequence c1 c2)
 | S ?j => match c2 with Ssequence ?c3 ?c4 => reassociate_to (Ssequence c1 c3) c4 j end
 end.

Tactic Notation "assert_after" constr(n) constr(PQR) :=
 let n := match type of n with
              | Z => let j := constr:(Z.to_nat n) in let j := eval compute in j in j
              | _ => n
             end in
 match goal with
 | |- semax _ _ (Ssequence (Ssequence ?c1 ?c2) ?c3) _ =>
 let c := reassociate_to c1 c2 n
  in match c with (Ssequence ?d ?e) =>
           let f := constr:(Ssequence d (Ssequence e c3))
            in apply (semax_unfold_Ssequence _ f); [reflexivity | ]
      end
 | |- semax _ _ (Ssequence ?c1 ?c2) _ =>
 let c := reassociate_to c1 c2 n
  in  apply (semax_unfold_Ssequence c); [reflexivity | ]
 end;
 apply semax_seq' with PQR; abbreviate_semax.

Ltac do_funspec_sub :=
intros;
apply NDsubsume_subsume;
[ split; extensionality gv; reflexivity
| split; [ split; reflexivity | intros w; simpl in w; intros [g args]; normalize;
                                unfold_for_go_lower; simpl; entailer! ]
].

Ltac do_funspec_sub_nonND :=
   split; 
   [ split; try reflexivity 
   | intros ts w; simpl in w; intros [g args]; Intros;
      fold (@rmaps.dependent_type_functor_rec ts) in * ].