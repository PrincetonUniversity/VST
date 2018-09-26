Require Import VST.msl.msl_standard.
Require Import VST.veric.Clight_base.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.Clight_lemmas.
Require Import VST.veric.mpred.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.

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
(*
Lemma join_te_denote : forall te1 te2 id b t1,
(join_te te1 te2) ! id = Some (t1, b) ->
  (exists b1, te1 ! id = Some (t1, b || b1)) /\
  match te2 ! id with Some (t2,b2) => b = b && b2 | None => True end.
Proof.
intros.

unfold join_te in *. rewrite PTree.fold_spec in *.
rewrite  <- fold_left_rev_right in *.

assert (forall t : type * bool, In (id, t) (rev (PTree.elements te1)) -> te1 ! id = Some t).
intros. apply PTree.elements_complete. apply in_rev. auto.

assert (NOREP := PTree.elements_keys_norepet (te1)).

induction (rev (PTree.elements te1)). simpl in *.
rewrite PTree.gempty in *. congruence.

simpl in *. destruct a as [p [t b0]]. simpl in *.
destruct (te2 ! p) eqn:?.  destruct p0.
rewrite PTree.gsspec in H.
if_tac in H. subst. specialize (H0 (t,b0)). inv H.
 spec H0; auto.
 split. exists b0. rewrite H0. repeat f_equal. destruct b0,b1; simpl; auto.
 rewrite Heqo. destruct b0; simpl; auto. destruct b1; simpl; auto.

 auto. auto.
Qed.

Lemma typecheck_environ_join1:
  forall rho Delta1 Delta2,
        var_types Delta1 = var_types Delta2 ->
        glob_types Delta1 = glob_types Delta2 ->

        typecheck_environ Delta1 rho ->
        typecheck_environ (join_tycon Delta1 Delta2) rho.
Proof. intros.
 unfold typecheck_environ in *.
destruct H1 as [? [? ?]]. split3.
*
clear H2 H3.
destruct rho. simpl in *.
unfold typecheck_temp_environ in *. intros. unfold temp_types in *.
destruct Delta2 as [temps2 vars2 ret2 globty2 globsp2];
destruct Delta1 as [temps1 vars1 ret1 globty1 globsp1]; simpl in *.
apply join_te_denote in H2.
destruct H2. destruct H2.
edestruct H1. eauto. destruct H4. destruct H5.
destruct b; intuition. simpl in *. eauto. eauto.
*
unfold join_tycon.
destruct Delta2 as [temps2 vars2 ret2 globty2 globsp2];
destruct Delta1 as [temps1 vars1 ret1 globty1 globsp1]; simpl in *.
subst. auto.
*
unfold join_tycon.
destruct Delta2 as [temps2 vars2 ret2 globty2 globsp2];
destruct Delta1 as [temps1 vars1 ret1 globty1 globsp1]; simpl in *.
unfold glob_types in *; simpl in *; subst; auto.
Qed.
 *)

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

(*
Lemma initialized_tycontext_evolve:
  forall i Delta, tycontext_evolve Delta (initialized i Delta).
Proof.
intros i [A B C D E].
 unfold initialized;
 split; [| split; [|split; [|split; [ |split]]]]; intros; unfold temp_types, var_types, glob_types, ret_type;
 simpl.
 destruct (A ! id) as [[? ?]|] eqn:?; simpl.
 destruct (A!i) as [[? ?]|] eqn:?; simpl.
 destruct (eq_dec i id). subst. rewrite PTree.gss. inversion2 Heqo Heqo0.
 split; auto. destruct b; reflexivity.
 rewrite PTree.gso by auto. rewrite Heqo. split; auto.
 destruct b; simpl; auto. rewrite Heqo. destruct b; simpl; auto.
 destruct (A!i) as [[? ?]|] eqn:?; simpl.
 destruct (eq_dec i id). subst. congruence.
 rewrite PTree.gso by auto. rewrite Heqo. auto.
 rewrite Heqo. auto.
all: destruct (A!i) as [[? ?]|]; reflexivity.
Qed.
*)
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
(*
Lemma typecheck_environ_join2:
  forall rho Delta Delta1 Delta2,
        tycontext_evolve Delta Delta1 ->
        tycontext_evolve Delta Delta2 ->
        typecheck_environ Delta2 rho ->
        typecheck_environ (join_tycon Delta1 Delta2) rho.
Proof.
intros [ge ve te]  [A B C D E] [A1 B1 C1 D1 E1] [A2 B2 C2 D2 E2]
  [S1 [S2 [S3 [S4 S5]]]]  [T1 [T2 [T3 [T4 T5]]]]
  [U1 [U2 U3]];
 split; [|split];
 unfold temp_types,var_types, ret_type in *; simpl in *;
 subst C1 C2.
* clear - S1 T1 U1; unfold typecheck_temp_environ in *.
  intros.
  specialize (S1 id); specialize (T1 id); specialize (U1 id).
  apply join_te_denote in H. destruct H as [[b1 ?] ?].
  rewrite H in *. clear A1 H.
 destruct (A ! id) as [[? ?]|]; [ | contradiction].
 destruct S1; subst ty.
 destruct (A2!id) as [[? ?]|]; [ | contradiction].
 destruct T1; subst t0.
 destruct (U1 _ _ (eq_refl _)) as [v [? ?]].
 exists v; split; auto.
 destruct H3; auto; left.
 unfold is_true.
 destruct b; auto. destruct b2; inv H0. contradiction. apply I.
* unfold typecheck_var_environ in *; intros.
  rewrite <- S2. rewrite T2. rewrite U2. clear; intuition.
* unfold typecheck_glob_environ in *; intros.
  rewrite <- S4 in H. rewrite T4 in H. apply U3 in H. auto.
Qed.
*)
Lemma tc_val_ptr_lemma {CS: compspecs} :
   forall rho m Delta id t a,
   typecheck_environ Delta rho ->
   denote_tc_assert (typecheck_expr Delta (Etempvar id (Tpointer t a))) rho m ->
   (*(temp_types Delta) ! id =  Some (Tpointer t a, init) ->*) (*modified for init changes*)
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
intuition.
Qed.

Lemma tycontext_evolve_refl : forall Delta, tycontext_evolve Delta Delta.
Proof.
intros.
split; auto.
intros. destruct ((temp_types Delta)!id); auto.
Qed.

(*
Lemma tycontext_evolve_join:
  forall Delta Delta1 Delta2,
   tycontext_evolve Delta Delta1 ->
   tycontext_evolve Delta Delta2 ->
   tycontext_evolve Delta (join_tycon Delta1 Delta2).
Proof.
intros [A B C D E] [A1 B1 C1 D1 E1] [A2 B2 C2 D2 E2]
  [? [? [? [? [? ?]]]]] [? [? [? [? [? ?]]]]];
simpl in *;
 repeat split; auto.
 clear - H H5.
intro id; specialize (H id); specialize (H5 id).
 unfold temp_types in *; simpl in *.
 destruct (A ! id) as [[? ?]|].
 destruct (A1 ! id) as [[? ?]|] eqn:?; [ | contradiction].
 destruct (A2 ! id) as [[? ?]|] eqn:?; [ | contradiction].
 destruct H,H5; subst t1 t0.
 rewrite (join_te_eqv _ _ _ _ _ _ Heqo Heqo0).
 split; auto. destruct b,b0; inv H0; auto.
 rewrite join_te_denote2.
 unfold te_one_denote.
 destruct (A1 ! id) as [[? ?]|]; [contradiction|].
 auto.
Qed.

Lemma tycontext_evolve_update_tycon:
 forall c Delta, tycontext_evolve Delta (update_tycon Delta c)
 with tycontext_evolve_join_labeled:
 forall l Delta, tycontext_evolve Delta (join_tycon_labeled l Delta).
Proof.
clear tycontext_evolve_update_tycon.
induction c; simpl; intros; try destruct o; try apply tycontext_evolve_refl;
try apply initialized_tycontext_evolve.
eapply tycontext_evolve_trans; [ apply IHc1 | apply IHc2].
apply tycontext_evolve_join; auto.
auto.
auto.

clear tycontext_evolve_join_labeled.
induction l; simpl; auto; intros.
apply tycontext_evolve_refl.
apply tycontext_evolve_join; auto.
Qed.

Lemma join_context_com:
 forall D D1 D2, 
  tycontext_evolve D D1 ->
  tycontext_evolve D D2 ->
  tycontext_eqv (join_tycon D1 D2) (join_tycon D2 D1).
Proof.
intros.
hnf.
rewrite !var_types_update_dist.
rewrite !ret_type_update_dist.
rewrite !glob_types_update_dist.
rewrite !glob_specs_update_dist.
rewrite !annotations_update_dist.
destruct H as [? [? [? [? [? ?]]]]].
destruct H0 as [? [? [? [? [? ?]]]]].
repeat split; intros; try congruence.
rewrite !temp_types_update_dist.
rewrite !join_te_denote2.
unfold te_one_denote.
clear - H H0.
specialize (H id). specialize (H0 id).
destruct ((temp_types D)!id) as [[? ?]|]; try contradiction.
destruct ((temp_types D1)!id) as [[? ?]|];
destruct ((temp_types D2)!id) as [[? ?]|]; auto.
destruct H,H0. subst.
f_equal.
f_equal.
apply andb_comm.
destruct ((temp_types D1)!id) as [[? ?]|];
destruct ((temp_types D2)!id) as [[? ?]|]; try contradiction; auto.
Qed.

Lemma join_tycon_assoc:
 forall D1 D2 D3,
 tycontext_eqv
  (join_tycon D1 (join_tycon D2 D3))
  (join_tycon (join_tycon D1 D2) D3).
Proof.
intros.
hnf.
rewrite !var_types_update_dist.
rewrite !ret_type_update_dist.
rewrite !glob_types_update_dist.
rewrite !glob_specs_update_dist.
rewrite !annotations_update_dist.
split; auto.
intro.
destruct D1 as [a1 ].
destruct D2 as [a2 ].
destruct D3 as [a3 ].
simpl.
rewrite !join_te_denote2.
clear.
unfold te_one_denote.
destruct (a1 ! id) as [[? ?]|] eqn:H1; auto.
destruct (a2 ! id) as [[? ?]|] eqn:H2; auto.
destruct (a3 ! id) as [[? ?]|] eqn:H3; auto.
f_equal. f_equal.
apply andb_assoc.
Qed.

Lemma tycontext_eqv_refl: forall Delta : tycontext, 
   tycontext_eqv Delta Delta.
Proof.
intros.
repeat split.
Qed.

Lemma tycontext_eqv_trans: forall Delta1 Delta2 Delta3 : tycontext, 
   tycontext_eqv Delta1 Delta2 -> tycontext_eqv Delta2 Delta3 ->
   tycontext_eqv Delta1 Delta3.
Proof.
intros.
hnf in H,H0|-*.
intuition; try congruence.
Qed.

Lemma initialized_join_tycon:
  forall Delta1 Delta2 i,
tycontext_eqv (initialized i (join_tycon Delta1 Delta2))
  (join_tycon (initialized i Delta1) (initialized i Delta2)).
Proof.
intros.
unfold initialized.
destruct ((temp_types
     (join_tycon Delta1 Delta2)) ! i)
        as [[? ?]|] eqn:?H.
destruct ((temp_types Delta1) ! i)
       as [[? ?]|] eqn:?H.
destruct ((temp_types Delta2) ! i)
       as [[? ?]|] eqn:?H.
unfold join_tycon at 7.
rewrite !var_types_update_dist.
rewrite !ret_type_update_dist.
rewrite !glob_types_update_dist.
rewrite !glob_specs_update_dist.
rewrite !annotations_update_dist.
split; auto.
intro.
rewrite temp_types_update_dist.
unfold temp_types at 1 4.
destruct (ident_eq id i).
subst. 
rewrite join_te_denote2.
unfold te_one_denote.
rewrite !PTree.gss.
rewrite temp_types_update_dist in H.
rewrite join_te_denote2 in H.
unfold te_one_denote in H.
rewrite H0 in H. rewrite H1 in H. inv H.
reflexivity.
rewrite !join_te_denote2.
unfold te_one_denote.
rewrite !PTree.gso by auto.
rewrite join_te_denote2.
unfold te_one_denote.
auto.
rewrite !var_types_update_dist.
rewrite !ret_type_update_dist.
rewrite !glob_types_update_dist.
rewrite !glob_specs_update_dist.
rewrite !annotations_update_dist.
split; auto.
intro.
rewrite !temp_types_update_dist.
rewrite join_te_denote2.
destruct Delta1; simpl in *. destruct Delta2; simpl in *.
unfold te_one_denote.
rewrite join_te_denote2 in H.
unfold te_one_denote in H.
rewrite H0 in H. rewrite H1 in H. inv H.
clear.
destruct Delta2; simpl. intuition.
rewrite temp_types_update_dist in H.
rewrite join_te_denote2 in H.
unfold te_one_denote in H.
rewrite H0 in H. inv H.
rewrite temp_types_update_dist in H.
rewrite join_te_denote2 in H.
unfold te_one_denote in H.
destruct ((temp_types Delta1) ! i)
        as [[? ?]|] eqn:?H.
destruct ((temp_types Delta2) ! i)
        as [[? ?]|] eqn:?H.
inv H.
hnf.
rewrite !var_types_update_dist.
rewrite !ret_type_update_dist.
rewrite !glob_types_update_dist.
rewrite !glob_specs_update_dist.
rewrite !annotations_update_dist.
split.
intros.
rewrite !temp_types_update_dist.
simpl.
rewrite !join_te_denote2.
unfold te_one_denote.
destruct (ident_eq id i).
subst.
rewrite H0,H1.
rewrite PTree.gss. auto.
rewrite PTree.gso by auto.
auto.
destruct Delta2; simpl in *. intuition.
destruct ((temp_types Delta2) ! i)
        as [[? ?]|] eqn:?H.
hnf.
rewrite !var_types_update_dist.
rewrite !ret_type_update_dist.
rewrite !glob_types_update_dist.
rewrite !glob_specs_update_dist.
rewrite !annotations_update_dist.
split; auto.
intros.
rewrite !temp_types_update_dist.
simpl.
rewrite !join_te_denote2.
unfold te_one_denote.
destruct (ident_eq id i).
subst.
rewrite H0. auto.
destruct ((temp_types Delta1) ! id)
       as [[? ?]|] eqn:?H; auto.
destruct ((temp_types Delta2) ! id)
       as [[? ?]|] eqn:?H; auto.
rewrite PTree.gso by auto. rewrite H3. auto.
rewrite PTree.gso by auto. rewrite H3. auto.
apply tycontext_eqv_refl.
Qed.

*)