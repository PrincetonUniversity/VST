Require Import VST.veric.Clight_base.
Require Import VST.msl.msl_standard.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.Clight_lemmas.
Require Import VST.veric.mpred.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Export VST.veric.environ_lemmas.
Require Import VST.veric.binop_lemmas2.
Require Import VST.veric.binop_lemmas3.
Require Import VST.veric.binop_lemmas.
Require Import VST.veric.binop_lemmas4.
Require Import VST.veric.expr_lemmas2.
Require Export VST.veric.expr_lemmas3.
Require Export VST.veric.expr_lemmas4.
Require Import VST.veric.juicy_mem.
Import Cop.
Import Cop2.
Import Clight_Cop2.

(*
Lemma typecheck_environ_update_te:
  forall rho c Delta, typecheck_temp_environ (te_of rho) (temp_types (update_tycon Delta c))
     ->
typecheck_temp_environ  (te_of rho) (temp_types Delta)

with typecheck_ls_update_te : forall Delta ty b id l,
(temp_types Delta) ! id = Some (ty, b) ->
exists b2, (temp_types (join_tycon_labeled l Delta)) ! id = Some (ty, b2).
Proof.
intros.
unfold typecheck_temp_environ in H. unfold typecheck_temp_environ.
destruct c; intros; simpl in *; try solve[eapply H; apply H0].
*
destruct (eq_dec id i). subst.
destruct (H i true ty). unfold initialized. rewrite H0.
unfold temp_types. simpl. rewrite PTree.gsspec. rewrite peq_true.
auto. destruct H1. destruct H2. inv H2. exists x. auto.
apply H.
unfold initialized.
remember ((temp_types Delta) ! i). destruct o. destruct p.
unfold temp_types. simpl. rewrite PTree.gsspec.
rewrite peq_false by auto. apply H0. auto.
*
destruct o.
destruct (eq_dec id i). subst. destruct (H i true ty).
unfold initialized.
remember ((temp_types Delta) ! i). destruct o. destruct p.
unfold temp_types. simpl. inv H0.
rewrite PTree.gsspec. rewrite peq_true. eauto. congruence.
destruct H1. destruct H2. inv H2. eauto.
eapply H. unfold initialized.
remember ((temp_types Delta) ! i). destruct o. destruct p.
unfold temp_types. simpl. rewrite PTree.gsspec.
rewrite peq_false by auto. apply H0. auto. eauto.
*
destruct (update_tycon_te_same c1 _ _ _ _ H0).
destruct (update_tycon_te_same c2 _ _ _ _ H1).
destruct (H _ _ _ H2) as [v [? ?]]. exists v.
split; auto. destruct H4; auto. left. destruct b; simpl; auto.
*
destruct (update_tycon_te_same c1 _ _ _ _ H0).
destruct (update_tycon_te_same c2 _ _ _ _ H0).
specialize (H id ((b || x) && (b || x0))%bool ty ).
spec H.
 unfold join_tycon. remember (update_tycon Delta c1).
destruct t. remember (update_tycon Delta c2).
destruct t. unfold temp_types in *.
unfold update_tycon. simpl in *.
apply join_te_eqv; eauto.    destruct b; auto. simpl in *.
destruct H. exists x1. split. destruct H. auto. left. auto.
*
 edestruct (update_labeled_te_same l Delta id).  apply H0.
 edestruct H. apply H1.
 destruct H2. exists x0. split; auto. destruct b; simpl; auto.
* destruct (update_tycon_te_same c _ _ _ _ H0) as [bb HH].
  simpl in HH.
  destruct (H _ _ _ HH) as [v [AA BB]]. exists v; split; trivial.
  destruct BB. 2: right; trivial.
  destruct b; simpl in *. contradiction. left; trivial.
*
intros. destruct l; simpl in *.
exists b; assumption.
 destruct (update_tycon_te_same s _ _ _ _ H).
edestruct typecheck_ls_update_te. apply H.
rewrite temp_types_update_dist. erewrite join_te_eqv; eauto.
Qed.

Lemma typecheck_environ_update_ve : forall (rho : environ) (c : statement) (Delta : tycontext),
typecheck_var_environ (ve_of rho) (var_types (update_tycon Delta c)) ->
typecheck_var_environ (ve_of rho) (var_types Delta).
Proof.
intros.
intros id t; specialize (H id t).
induction c; simpl in *; try apply H;
try destruct o; try rewrite set_temp_ve in *;
 try apply H.
repeat rewrite update_tycon_same_ve in *; auto.
rewrite var_types_update_dist, update_tycon_same_ve in H; auto.
rewrite update_le_same_ve in H; auto.
auto.
Qed.


Lemma typecheck_environ_update_ge : forall (rho : environ) (c : statement) (Delta : tycontext),
typecheck_glob_environ (ge_of rho) (glob_types (update_tycon Delta c)) ->
typecheck_glob_environ (ge_of rho) (glob_types Delta).
Proof.
intros. destruct c; simpl in *; try apply H;
try destruct o; try rewrite set_temp_ge in *; try apply H;
unfold typecheck_glob_environ in *; intros; eapply H; try rewrite glob_types_update_dist;
try apply join_ge_eqv;
repeat rewrite update_tycon_same_ge in *; try rewrite update_le_same_ge;
eauto.
Qed.

Lemma typecheck_environ_update:
  forall rho c Delta, typecheck_environ (update_tycon Delta c) rho ->
       typecheck_environ Delta rho.
Proof.
intros. unfold typecheck_environ in *. intuition.
clear - H0. unfold typecheck_temp_environ in *.
eapply typecheck_environ_update_te; eauto.

clear -H. eapply typecheck_environ_update_ve; eauto.

eapply typecheck_environ_update_ge.
eauto.
Qed.
*)
Lemma tc_bool_val:
  forall v t,
       tc_val t v ->
       bool_type t = true ->
      exists b, strict_bool_val v t = Some b.
Proof.
intros.
unfold bool_type in H0.
destruct (eqb_type t int_or_ptr_type) eqn:J;
destruct t; try destruct f; inv H0;
destruct v; try solve [inv H]; simpl; eauto;
exists false;
unfold tc_val in H; try rewrite J in H;
try (inv H; try reflexivity).
Qed.

Lemma bool_val_strict: forall t v b, tc_val t v -> bool_type t = true -> bool_val t v = Some b ->
  strict_bool_val v t = Some b.
Proof.
  intros.
  assert (eqb_type t int_or_ptr_type = false) as Hf.
  { destruct t; auto.
    apply negb_true; auto. }
  destruct t, v; auto; try solve [destruct f; auto]; simpl in *; unfold bool_val in *;
    simpl in *; rewrite ?Hf in *; auto; try discriminate; simpl in *; try contradiction.
  destruct Archi.ptr64; inv H1.
  rewrite ?Int.eq_true, ?Int64.eq_true; auto.
Qed.

Lemma bool_val_Cop: forall t v m b b', bool_val t v = Some b -> Cop.bool_val v t m = Some b' ->
  b = b'.
Proof.
  destruct t, v; try discriminate; unfold bool_val; try destruct f; try discriminate;
    simpl; intros ???; try simple_if_tac; intro; inv H; unfold Cop.bool_val; simpl; intro X;
    inv X; auto;
  try solve [destruct i; inv H0; auto];
  try solve [revert H0; repeat simple_if_tac; intros; congruence].
Qed.

Lemma map_ptree_rel : forall id v te, Map.set id v (make_tenv te) = make_tenv (PTree.set id v te).
intros. unfold Map.set. unfold make_tenv. extensionality. rewrite PTree.gsspec; auto.
Qed.

Lemma cast_exists : forall {CS: compspecs} Delta e2 t rho phi
(TC: typecheck_environ Delta rho),
denote_tc_assert (typecheck_expr Delta e2) rho phi ->
denote_tc_assert (isCastResultType (typeof e2) t e2)
  rho phi ->
sem_cast (typeof e2) t (eval_expr e2 rho)  =
Some (force_val (sem_cast (typeof e2) t (eval_expr e2 rho))).
Proof.
intros.
assert (exists v, sem_cast (typeof e2) t (eval_expr e2 rho) = Some v). {
apply typecheck_expr_sound in H; [ | auto ].
rewrite isCastR in H0.
unfold sem_cast.
rename t into t0.
remember (typeof e2); remember (eval_expr e2 rho).
unfold sem_cast.
destruct Archi.ptr64 eqn:Hp.
*
destruct (eqb_type t int_or_ptr_type) eqn:J.
 +
  apply eqb_type_true in J. rewrite J in *.
  exists v.
  destruct v; try contradiction;
  destruct t0 as [ | [ | | | ] [ | ] ? | i1 ? | [ | ] ? | | | | | ]; try contradiction;
  try (hnf in H; rewrite eqb_type_refl in H; unfold is_pointer_or_integer in H;
       rewrite Hp in H; contradiction H);
  unfold classify_cast in *;
  destruct t0 as [ | [ | | | ] [ | ] ? | i1 ? | [ | ] ? | | | | | ]; try contradiction;
  try unfold int_or_ptr_type at 1 in H0; rewrite eqb_type_refl in H0|-*;
  unfold int_or_ptr_type at 1;
  destruct (eqb_type (Tpointer _ a) int_or_ptr_type) eqn:Heqb0; try contradiction;
  rewrite eqb_type_sym in Heqb0; rewrite Heqb0 in H0;
  simpl; simpl in H0; auto.
+
 unfold sem_cast_pointer, classify_cast in *. rewrite Hp, J in *.
 destruct (eqb_type t0 int_or_ptr_type) eqn:J0.
 -
  apply eqb_type_true in J0. subst t0.
  unfold int_or_ptr_type at 1 in H0. unfold int_or_ptr_type at 1.
  destruct t as [ | [ | | | ] [ | ] a | i a | [ | ] a | | | | | ]; destruct v; try contradiction.
 -
 destruct t0 as [ | [ | | | ] [ | ] ? | ? ? | [ | ] ? | | | | | ]; try contradiction; rewrite ?J0; eauto;
  destruct t as [ | [ | | | ] [ | ] ? | ? ? | [ | ] ? | | | | | ]; try contradiction; 
    destruct v; try contradiction; 
(*
 try (rewrite denote_tc_assert_andp in H0; simpl in H0);
 unfold is_pointer_type in H0; rewrite ?J in H0; rewrite ?J0 in H0;
*) simpl in *; rewrite ?J in *; rewrite ?J0 in *;
  try solve [eexists; simpl; eauto];
 try contradiction;
 try solve [
  unfold_lift in H0; simpl in H0; rewrite <- Heqv in H0; simpl in H0; 
  match type of H0 with (app_pred match ?ZZ with Some _ => _ | None => _ end _ /\ _) =>
    destruct ZZ eqn:H5
 end;
 destruct H0 as [H0 H0']; do 3 red in H0, H0';
 try contradiction;
 simpl;
 first [rewrite (float_to_int_ok _ _ H5)
        | rewrite (float_to_intu_ok _ _ H5)
        | rewrite (single_to_int_ok _ _ H5)
        | rewrite (single_to_intu_ok _ _ H5)
        ] ;
    [ eexists; reflexivity
    | split; omega ]].
 all: try (unfold is_pointer_or_null in H; rewrite Hp in H; contradiction).
all:  try (rewrite Hp; eexists; reflexivity).
*
destruct (eqb_type t int_or_ptr_type) eqn:J.
 +
  apply eqb_type_true in J. rewrite J in *.
  exists v.
  destruct v; try contradiction.
  destruct t0 as [ | [ | | | ] [ | ] ? | i1 ? | [ | ] ? | | | | | ]; try contradiction.
  unfold classify_cast in *. unfold int_or_ptr_type at 1 in H0.
  rewrite eqb_type_refl in H0|-*.
 unfold int_or_ptr_type at 1.
  destruct (eqb_type (Tpointer t0 a) int_or_ptr_type) eqn:?; try contradiction.
  rewrite eqb_type_sym in Heqb. rewrite Heqb in H0.
  simpl. simpl in H0.
  reflexivity.
  destruct t0 as [ | [ | | | ] [ | ] ? | i1 ? | [ | ] ? | | | | | ]; try contradiction.
  unfold classify_cast in *. unfold int_or_ptr_type at 1 in H0.
  rewrite eqb_type_refl in H0|-*.
 unfold int_or_ptr_type at 1.
  destruct (eqb_type (Tpointer t0 a) int_or_ptr_type) eqn:?; try contradiction.
  rewrite eqb_type_sym in Heqb0. rewrite Heqb0 in H0.
  simpl. simpl in H0. auto.
+
 unfold sem_cast_pointer, classify_cast in *. rewrite Hp, J in *.
 destruct (eqb_type t0 int_or_ptr_type) eqn:J0.
 -
  apply eqb_type_true in J0. subst t0.
  unfold int_or_ptr_type at 1 in H0. unfold int_or_ptr_type at 1.
  destruct t as [ | [ | | | ] [ | ] a | i a | [ | ] a | | | | | ]; destruct v; try contradiction.
 -
 simpl in *.
 destruct t0 as [ | [ | | | ] [ | ] ? | ? ? | [ | ] ? | | | | | ]; try contradiction; rewrite ?J0; eauto;
  destruct t as [ | [ | | | ] [ | ] ? | ? ? | [ | ] ? | | | | | ]; try contradiction; simpl in *;
    destruct v; try contradiction; 
  try solve [eexists; simpl; rewrite ?Hp; eauto];
 try (rewrite J in H); 
 try contradiction;
 try solve [
  unfold_lift in H0; simpl in H0; rewrite <- Heqv in H0; simpl in H0; 
  match type of H0 with (app_pred match ?ZZ with Some _ => _ | None => _ end _ /\ _) =>
    destruct ZZ eqn:H5
 end;
 destruct H0 as [H0 H0']; do 3 red in H0,H0';
 try contradiction;
 simpl;

 first [rewrite (float_to_int_ok _ _ H5)
        | rewrite (float_to_intu_ok _ _ H5)
        | rewrite (single_to_int_ok _ _ H5)
        | rewrite (single_to_intu_ok _ _ H5)
        ] ;
    [ eexists; reflexivity | omega];
  simpl; rewrite Hp; eauto];
  (hnf in H; rewrite Hp in H; contradiction H).
}
Opaque liftx.
destruct H1. rewrite H1. auto.
Qed.

Definition func_tycontext_t_denote :=
forall p t id ty ,  list_norepet (map fst p ++ map fst t ) ->
((make_tycontext_t p t) ! id = Some ty <-> (In (id,ty) p \/ In (id,ty) t)).

Definition func_tycontext_v_denote :=
forall v id ty, list_norepet (map fst v) ->
((make_tycontext_v v) ! id = Some ty <-> In (id,ty) v).

Lemma func_tycontext_v_sound : func_tycontext_v_denote.
unfold func_tycontext_v_denote. intros.
split; intros; induction v. simpl in *.
rewrite PTree.gempty in *. congruence.

simpl in *. destruct a. inv H. rewrite PTree.gsspec in *. if_tac in H0.
inv H0. auto. intuition.

inv H0.

simpl in *. destruct a. simpl in *. rewrite PTree.gsspec. destruct H0.
inv H0. if_tac. auto. intuition. inv H. if_tac. subst.
clear - H0 H3. rewrite in_map_iff in *. destruct H3. exists (i,ty). auto.
apply IHv; auto.
Qed.


Lemma set_inside : forall i0 t1 t p id,
list_disjoint (map fst p) (i0 :: map fst t) ->
(fold_right
          (fun param : ident * type =>
           PTree.set (fst param) (snd param, true))
          (PTree.set i0 (t1, false)
             (fold_right
                (fun (temp : ident * type) (tenv : PTree.t (type * bool)) =>
                 let (id, ty) := temp in PTree.set id (ty, false) tenv)
                (PTree.empty (type * bool)) t)) p) ! id =
(PTree.set i0 (t1, false) (
(fold_right
          (fun param : ident * type =>
           PTree.set (fst param) (snd param, true))
                (fold_right
                (fun (temp : ident * type) (tenv : PTree.t (type * bool)) =>
                 let (id, ty) := temp in PTree.set id (ty, false) tenv)
                (PTree.empty (type * bool)) t)) p)) ! id
.
Proof.
intros.
induction t.
  simpl in *. rewrite PTree.gsspec.
  if_tac.
    subst.
    induction p.
      simpl in *. rewrite PTree.gsspec. rewrite peq_true. auto.

      simpl in *. rewrite PTree.gsspec. if_tac. subst.
      clear - H. unfold list_disjoint in *. specialize (H (fst a) (fst a)).
      intuition. apply IHp. unfold list_disjoint in *. intros.
      apply H; simpl in *; auto.

    induction p.
       simpl in *. rewrite PTree.gsspec. if_tac. intuition.
       auto.

       simpl in *.  repeat rewrite PTree.gsspec in *. destruct a.
       simpl in *. if_tac. auto. rewrite IHp.  auto. unfold list_disjoint in *.
       intros. apply H; simpl in *; auto.

  simpl in *. rewrite PTree.gsspec in *. if_tac.
    subst.
    induction p.
      simpl in *. rewrite PTree.gsspec in *. rewrite peq_true in *.
      auto.

      simpl in *. rewrite PTree.gsspec in *. destruct a0 as (i,t0). simpl in *.
      if_tac. subst. clear - H. specialize (H i i). intuition.  apply IHp.
      unfold list_disjoint in *. intros. apply H; simpl in *; auto.
      intros. apply IHt. unfold list_disjoint in *. intros; simpl in *; apply H;      auto.
      auto. auto. intuition.

    destruct a. simpl in *. induction p.
      simpl in *. rewrite PTree.gsspec. if_tac; subst. intuition.
      repeat rewrite PTree.gsspec. auto.

      simpl in *. destruct a. simpl in *.
      spec IHt. unfold list_disjoint in *. intros; apply H; simpl in *; auto.
      intuition.
      repeat rewrite PTree.gsspec in *. if_tac.
        subst.  auto.

        apply IHp. unfold list_disjoint in *.   intros. apply H. simpl in *.
        auto.  auto. intros. auto.

Qed.

Lemma func_tycontext_t_sound : func_tycontext_t_denote.
Proof.
  unfold func_tycontext_t_denote.
  split; intros;
  unfold make_tycontext_t in *;
  apply list_norepet_app in H; destruct H as [? [? ?]].
  + induction t; induction p; simpl in *.
    - rewrite PTree.gempty in *; congruence.
    - left.
      destruct a; simpl in *. rewrite PTree.gsspec in *. if_tac in H0.
      inv H0. auto.
      inv H.  destruct IHp; auto. unfold list_disjoint.  intros. inv H4.
      destruct H.
    - right.
      destruct a. simpl in *. rewrite PTree.gsspec in *.
      if_tac in H0. subst. inv H0. auto. destruct IHt. inv H1; auto.
      unfold list_disjoint in *. intros. inv H4. auto. intuition. intuition.
    - simpl in *.
      rewrite PTree.gsspec in *.
      if_tac in H0.
      * destruct a0. simpl in *.
        subst. inv H0. intuition.
      * destruct a0. simpl in *.  destruct a. simpl in *.
        destruct IHp.
        ++ inv H; auto.
        ++ intro; intros. apply H2; simpl in *; auto.
        ++ auto.
        ++ intros. destruct IHt.
          -- inv H1; auto.
          -- intro; intros; apply H2; simpl in *; auto.
          -- auto.
          -- destruct H7.
            ** inv H7; intuition.
            ** auto.
          -- auto.
        ++ left.
           right. apply H4.
        ++ right. auto.
  + induction t; induction p; simpl in *.
    - intuition.
    - rewrite PTree.gsspec. if_tac.
      * subst. destruct a. simpl in *.
        destruct H0; [destruct H0 |].
       ++ inv H0. auto.
       ++ subst.
          clear - H H0. inv H. rewrite in_map_iff in *. destruct H3.
          exists (i,ty). auto.
       ++ inv H0.
      * destruct H0.
       ++ destruct a. destruct H0.
         -- subst. inv H0. intuition.
         -- simpl in *. apply IHp.
           ** inv H; auto.
           ** intro. intros. inv H5.
           ** left. subst. auto.
       ++ inv H0.
    - destruct H0; [| destruct H0].
      * inv H0.
      * destruct a. simpl in *. inv H0; subst.
        rewrite PTree.gsspec. rewrite peq_true. auto.
      * destruct a. simpl in *. rewrite PTree.gsspec.
        if_tac.
       ++ subst. clear -H0 H1. inv H1. rewrite in_map_iff in *.
          destruct H3. exists (i,ty); auto.
       ++ apply IHt. inv H1; auto.
          intro; auto. right. auto.
    - spec IHt; [inv H1; auto |].
      spec IHt; [intro; intros; apply H2; simpl in *; auto |].
      spec IHp; [inv H; auto |].
      spec IHp; [intro; intros; apply H2; simpl in *; auto |].
      destruct a. destruct a0. destruct H0.
      * simpl in *.
        destruct H0.
       ++ inv H0.
          rewrite PTree.gsspec in *. rewrite peq_true. auto.
       ++ subst.
          rewrite PTree.gsspec in *. if_tac.
         -- subst. inv H. rewrite in_map_iff in H5.
            destruct H5. exists (i0,ty); auto.
         -- spec IHp. auto. spec IHp; auto.
      * simpl in *. rewrite PTree.gsspec. if_tac.
       ++ subst. destruct H0.
         -- inv H0. specialize (H2 i0 i0). destruct H2; simpl; auto.
         -- subst.
            spec IHt; [auto |].
            rewrite PTree.gsspec in *. rewrite peq_true in *. auto.
       ++ destruct H0.
         -- inv H0.
            spec IHp; [auto |].
            spec IHp; [| auto].
            intros; auto. destruct H5.
           ** clear - H5 H2.
              apply list_disjoint_cons_left, list_disjoint_sym in H2.
              eapply list_disjoint_notin in H2; [| left; eauto].
              destruct H2. apply in_map_iff. exists (id, ty). auto.
           ** clear - H5 H1. inv H1. destruct H2. apply in_map_iff. exists (id, ty). auto.
         -- subst.
            spec IHp; [auto |].
            spec IHp; [| auto].
            spec IHt; [auto |].
            rewrite PTree.gsspec in *.
            if_tac in IHt.
           ** intuition.
           ** intros. auto.
Qed.

Definition cast_no_val_change (from: type)(to:type) : bool :=
match from, to with
| Tint _ _ _, Tint I32 _ _ => true
| Tpointer _ _, Tpointer _ _ => 
    eqb_type from to || 
    negb (eqb_type from int_or_ptr_type) && 
    negb (eqb_type to int_or_ptr_type)
| Tfloat F64 _ , Tfloat F64 _ => true
| Tfloat F32 _ , Tfloat F32 _ => true
| _, _ => false
end.

Lemma cast_no_change : forall v from to m,
tc_val from v ->
is_true (cast_no_val_change from to) ->
Cop.sem_cast v from to m = Some v.
Proof.
  intros. apply is_true_e in H0.
  unfold cast_no_val_change in H0.
  unfold tc_val in H.
  destruct (eqb_type from int_or_ptr_type) eqn:J;
  destruct v; destruct from as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
  simpl in H; try tauto;
  destruct to as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
  simpl in *; try congruence; auto.
Qed.

Lemma tc_exprlist_length : forall {CS: compspecs} Delta tl el rho phi,
denote_tc_assert (typecheck_exprlist Delta tl el) rho phi ->
length tl = length el.
Proof.
intros. generalize dependent el. induction tl; intros. simpl in *. destruct el. inv H. auto.
inv H. simpl in H. destruct el; try solve [inv H]. simpl in *.
rewrite !denote_tc_assert_andp in H.
f_equal; apply IHtl.
destruct H; auto.
Qed.

Lemma neutral_cast_tc_val : forall {CS: compspecs} e t rho phi Delta,
true = is_neutral_cast (implicit_deref (typeof e)) t ->
denote_tc_assert (isCastResultType (implicit_deref (typeof e)) t  e) rho phi ->
denote_tc_assert (typecheck_expr Delta e) rho phi ->
typecheck_environ Delta rho ->
tc_val t (eval_expr e rho).
Proof.
intros.
rewrite isCastR in H0.
apply typecheck_expr_sound in H1; auto.
pose (AA := typeof e).
pose (BB := t).
Transparent Int.repr.
unfold classify_cast in *.
unfold tc_val, is_neutral_cast, implicit_deref, is_pointer_type, is_int_type in *.
destruct (typeof e)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ] ;
destruct t as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ]; 
try congruence;
repeat match goal with |- context [eqb_type ?A ?B] =>
  let J := fresh "J" in destruct (eqb_type A B) eqn:J;
  try rewrite J in *
end;
(*
repeat match goal with H: context [eqb_type ?A ?B] |- _ =>
  let J := fresh "J" in destruct (eqb_type A B) eqn:J;
   try rewrite J in *
end;
*)
try solve [
 simpl in H; simpl in H0;
try congruence; 
remember (eval_expr e rho); destruct v;
simpl in H0; try congruence; auto;
simpl in *; try congruence; super_unfold_lift;
try rewrite <- Heqv in *;  try unfold denote_tc_iszero in *;
try change Byte.min_signed with (-128) in *;
try change Byte.max_signed with 127 in *;
try change (Z.neg (shift_pos 15 1)) with (-32768);
try change Byte.max_unsigned with 255 in *;
try omega;
try apply H0;
try solve [destruct H1; subst; try split; compute; congruence]
].
change (negb true) with false in H.
rewrite andb_false_r in H. rewrite orb_false_r in H.
symmetry in H.
rewrite H in *.
apply eqb_type_true in H. rewrite H in *.
rewrite J in *.
simpl in H0. auto.
change (negb false) with true in H.
rewrite andb_true_r in H.
symmetry in H.
apply orb_true_iff in H.
destruct H.
apply eqb_type_true in H. rewrite H in *.
rewrite J in *.
rewrite eqb_type_refl in *. rewrite eqb_reflx in *.
auto.
destruct (eqb_type (Tpointer t0 a) int_or_ptr_type) eqn:?J; inv H.
rewrite eqb_reflx in H0. 
auto.
Qed.

Opaque Int.repr.

Definition typecheck_tid_ptr_compare
Delta id :=
match (temp_types Delta) ! id with
| Some t => is_int_type t
| None => false
end.

Lemma typecheck_tid_ptr_compare_sub:
   forall Delta Delta',
    tycontext_sub Delta Delta' ->
    forall id, typecheck_tid_ptr_compare Delta id = true ->
                typecheck_tid_ptr_compare Delta' id = true.
Proof.
unfold typecheck_tid_ptr_compare;
intros.
destruct H as [? _].
specialize (H id).
destruct ((temp_types Delta) ! id) as [? |]; try discriminate.
destruct ((temp_types Delta') ! id) as [? |]; try contradiction.
 destruct H; subst; auto.
Qed.

Lemma int64_eq_e:
 forall i j, Int64.eq i j = true -> i=j.
Proof.
intros.
pose proof (Int64.eq_spec i j). rewrite H in H0; auto.
Qed.

Lemma tc_val_sem_cast:
  forall {CS: compspecs} t2 e2 rho phi Delta,
      typecheck_environ Delta rho ->
      denote_tc_assert (typecheck_expr Delta e2) rho phi ->
      denote_tc_assert (isCastResultType (typeof e2) t2  e2) rho phi ->
      tc_val t2 (force_val (sem_cast (typeof e2) t2 (eval_expr e2 rho))).
Proof. intros ? ? ? ? ? ? H2 H5 H6.
assert (H7 := cast_exists _ _ _ _ phi H2 H5 H6).
assert (H8 := typecheck_expr_sound _ _ _ _ H2 H5).
clear - H7 H6 H8.
Transparent liftx.
revert H7; case_eq (sem_cast (typeof e2) t2 (eval_expr e2 rho) ); intros; inv H7.
simpl.
rewrite isCastR in H6.
unfold tc_val, sem_cast, classify_cast in *.
destruct (eqb_type t2 int_or_ptr_type) eqn:J.
apply eqb_type_true in J; subst t2.
simpl in *.
destruct (eqb_type (typeof e2) int_or_ptr_type) eqn:J0.
apply eqb_type_true in J0; rewrite J0 in *.
simpl in *.
destruct (eval_expr e2 rho); inv H; auto.
destruct (typeof e2) as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
inv H6; try inv H8; try inv H2; auto.
destruct (eqb_type (typeof e2) int_or_ptr_type) eqn:J0.
apply eqb_type_true in J0; rewrite J0 in *.
simpl in *.
destruct t2 as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ]; contradiction.

unfold sem_cast_pointer in *;
destruct t2 as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ] eqn:T2;
destruct Archi.ptr64 eqn:Hp;
try rewrite denote_tc_assert_andp in H6;
try contradiction;
destruct (typeof e2) as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ] eqn:Te2;
auto; try contradiction;  repeat rewrite if_true in * by auto;
    repeat match goal with
    | H: app_pred (denote_tc_assert (tc_bool _ _) _) _ |- _ => 
                      apply tc_bool_e in H
   end;
 try solve [
destruct (eval_expr e2 rho); simpl in H6,H8,H|-*;
 try inv H8; try inv H;
 try contradiction;
 try match goal with
    H: match ?A with Some _ => _ | None => _ end = _ |- _ => 
          destruct A eqn:?; inv H
    end;
 try apply I;
 try match goal with
  | |- context [if ?A then _ else _] =>
     destruct A; simpl; auto; try apply I
  | |- context [Int.sign_ext ?n ?i] =>
  apply (sign_ext_range' n i);  compute; split; congruence
  | |- context [Int.zero_ext ?n ?i] =>
  apply (zero_ext_range' n i);  compute; split; congruence
  end].

all: try solve [clear H6; simpl in H; destruct (eval_expr e2 rho); inv H; assumption].

all: try (
unfold is_pointer_type in H6; rewrite ?J,?J0 in H6; simpl in H6;
simpl in H6; rewrite denote_tc_assert_iszero' in H6; simpl in H6;
unfold denote_tc_iszero in H6; unfold_lift in H6;
destruct (eval_expr e2 rho); try contradiction; inv H; apply I).


all:
try (
unfold is_pointer_type in H6; rewrite ?J,?J0 in H6; simpl in H6;
simpl in H6; rewrite denote_tc_assert_iszero' in H6; simpl in H6; 
unfold denote_tc_iszero in H6; unfold_lift in H6;
destruct (eval_expr e2 rho); try contradiction; inv H;
apply is_true_e in H6; first [apply int_eq_e in H6 | apply int64_eq_e in H6; rewrite Int64.repr_unsigned in H6]; subst;
hnf; rewrite Hp; solve [auto]).

all:
try (
unfold is_pointer_type in H6; rewrite ?J,?J0 in H6; simpl in H6;
simpl in H6; rewrite denote_tc_assert_iszero' in H6; simpl in H6;
unfold denote_tc_iszero in H6; unfold_lift in H6;
destruct (eval_expr e2 rho); try contradiction; inv H;
simpl in H8; rewrite Hp in H8; try contradiction H8;
apply is_true_e in H6; first [apply int_eq_e in H6 | apply int64_eq_e in H6; rewrite Int64.repr_unsigned in H6]; subst;
inv H8).

all:
try (unfold is_pointer_type in H6; rewrite ?J,?J0 in H6; simpl in H6;
simpl in H6; rewrite denote_tc_assert_iszero' in H6; simpl in H6; 
unfold denote_tc_iszero in H6; unfold_lift in H6;
destruct (eval_expr e2 rho); try contradiction; inv H;
apply is_true_e in H6; first [apply int_eq_e in H6 | apply int64_eq_e in H6; rewrite Int64.repr_unsigned in H6]; subst;
simpl in H8; rewrite Hp in H8; inv H8).

all: 
try (simpl eqb_type in H6; cbv iota in H6;
unfold is_pointer_type in H6; rewrite J in H6; simpl in H6;
rewrite denote_tc_assert_iszero' in H6; simpl in H6;
unfold denote_tc_iszero in H6; unfold_lift in H6;
inv H; destruct (eval_expr e2 rho); try contradiction;
do 3 red in H6;
apply is_true_e in H6; apply int64_eq_e in H6; subst; hnf; rewrite Hp; auto).

all: try (inv H1; reflexivity).

Qed.







