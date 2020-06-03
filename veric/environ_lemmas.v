Require Import VST.msl.msl_standard.
Require Import VST.veric.Clight_base.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.Clight_lemmas.
Require Import VST.veric.mpred.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.

Require Import VST.veric.seplog. (*For definition of tycontext*)

Lemma eqb_type_eq: forall t1 t2, eqb_type t1 t2 = proj_sumbool (type_eq t1 t2).
Proof.
intros.
case_eq (eqb_type t1 t2); intros.
apply eqb_type_true in H; subst; simpl; auto.
rewrite proj_sumbool_is_true; auto.
destruct (type_eq t1 t2); simpl; subst.
rewrite eqb_type_refl in H; auto.
auto.
Qed.

Lemma In_fst_split : forall A B i (l: list (A * B)), In i (fst (split l)) <-> exists b : B, In (i,b) l.
Proof.
intros. split; intros. induction l. inv H. simpl in H. remember (split l). destruct p. destruct a.
simpl in *. destruct H. subst. clear IHl. eauto.
destruct IHl. auto. exists x. auto.

induction l. destruct H. inv H. simpl in *. destruct H. destruct H. destruct a. inv H.
clear IHl. destruct (split l). simpl. auto. destruct (split l). destruct a. simpl.
right. apply IHl. eauto.
Qed.

Definition tycontext_evolve (Delta Delta' : tycontext) :=
 (forall id, match (temp_types Delta) ! id, (temp_types Delta') ! id with
                | Some t, Some t' => t=t'
                | None, None => True
                | _, _ => False
               end)
 /\ (forall id, (var_types Delta) ! id = (var_types Delta') ! id)
 /\ ret_type Delta = ret_type Delta'
 /\ (forall id, (glob_types Delta) ! id = (glob_types Delta') ! id)
 /\ (forall id, (glob_specs Delta) ! id = (glob_specs Delta') ! id)
 /\ (forall id, (annotations Delta) ! id = (annotations Delta') ! id).

Lemma tycontext_evolve_trans: forall Delta1 Delta2 Delta3,
   tycontext_evolve Delta1 Delta2 ->
   tycontext_evolve Delta2 Delta3 ->
   tycontext_evolve Delta1 Delta3.
Proof.
intros [A B C D E] [A1 B1 C1 D1 E1] [A2 B2 C2 D2 E2]
  [S1 [S2 [S3 [S4 [S5 S6]]]]]  [T1 [T2 [T3 [T4 [T5 T6]]]]];
 split; [| split; [|split; [|split; [|split]]]];
 unfold temp_types,var_types, ret_type in *; simpl in *;
 try congruence.
 clear - S1 T1.
 intro id; specialize (S1 id); specialize (T1 id).
 destruct (A!id) as [?|].
 destruct (A1!id) as [?|]; [ | contradiction]. subst t0.
 destruct (A2!id) as [?|]; [ | contradiction]. subst t0.
 auto.
 destruct (A1!id) as [?|]; [ contradiction| ].
 auto.
Qed.

Lemma tc_val_ptr_lemma {CS: compspecs} :
   forall rho m Delta id t a,
   typecheck_environ Delta rho ->
   denote_tc_assert (typecheck_expr Delta (Etempvar id (Tpointer t a))) rho m ->
   strict_bool_val (eval_id id rho) (Tpointer t a) = Some true ->
   tc_val (Tpointer t a) (eval_id id rho).
Proof.
intros. unfold strict_bool_val in *. unfold tc_val.
destruct (eval_id id rho); try congruence.
+ destruct Archi.ptr64; try discriminate;
    destruct (Int.eq i Int.zero); try congruence.
+ unfold is_pointer_or_integer, is_pointer_or_null.
  destruct Archi.ptr64; inv H1;   simple_if_tac; simpl; auto.
  destruct (Int64.eq i Int64.zero); try congruence.
+
   simple_if_tac; simpl; auto.
Qed.

Lemma typecheck_environ_put_te : forall ge te ve Delta id v ,
  typecheck_environ Delta (mkEnviron ge ve te) ->
  (forall t , ((temp_types Delta) ! id = Some t ->
     tc_val' t v)) ->
  typecheck_environ Delta (mkEnviron ge ve (Map.set id v te)).
Proof.
  intros. unfold typecheck_environ in *. simpl in *.
  intuition. clear H H3.
  destruct Delta. unfold temp_types in *; simpl in *.
  unfold typecheck_temp_environ.
  intros. rewrite Map.gsspec.
  if_tac.
  + subst. exists v; intuition.
  + simpl in *. specialize (H1 id0 _ H). auto.
Qed.

Lemma typecheck_environ_put_te' : forall ge te ve Delta id v ,
 typecheck_environ  Delta (mkEnviron ge ve te) ->
(forall t , ((temp_types Delta) ! id = Some t -> tc_val' t v)) ->
typecheck_environ Delta (mkEnviron ge ve (Map.set id v te)).
Proof.
intros.
assert (typecheck_environ Delta (mkEnviron ge ve (Map.set id v te))).
apply typecheck_environ_put_te; auto.

unfold typecheck_environ in *. simpl in *.
tauto.
Qed.

Lemma tycontext_evolve_refl : forall Delta, tycontext_evolve Delta Delta.
Proof.
intros.
split; auto.
intros. destruct ((temp_types Delta)!id); auto.
Qed.
