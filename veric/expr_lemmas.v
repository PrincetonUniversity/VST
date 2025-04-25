Require Import VST.veric.Clight_base.
Require Import VST.veric.Clight_lemmas.
Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import VST.veric.res_predicates.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
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
Require Import VST.veric.seplog. (*For definition of typecheck_environ*)
Import Cop.
Import Cop2.
Import Clight_Cop2.
Import Ctypes.
Import LiftNotation.

Transparent intsize_eq.

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
    simpl in *; rewrite -> ?Hf in *; auto; try discriminate; simpl in *; try contradiction.
  destruct Archi.ptr64; inv H1.
  rewrite -> ?Int.eq_true, ?Int64.eq_true; auto.
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

Lemma map_ptree_rel : forall id v te, Map.set id v (make_tenv te) = make_tenv (Maps.PTree.set id v te).
intros. unfold Map.set. unfold make_tenv. extensionality. rewrite Maps.PTree.gsspec; auto.
Qed.

Section mpred.

Context `{!heapGS Σ}.

Lemma cast_exists : forall {CS: compspecs} Delta e2 t rho
(TC: typecheck_environ Delta rho),
denote_tc_assert (typecheck_expr Delta e2) rho ∧
denote_tc_assert (isCastResultType (typeof e2) t e2) rho ⊢
⌜sem_cast (typeof e2) t (eval_expr e2 rho) =
Some (force_val (sem_cast (typeof e2) t (eval_expr e2 rho)))⌝.
Proof.
intros.
iIntros "H".
iDestruct (typecheck_expr_sound _ _ (Ecast e2 t) with "[H]") as %H; first done.
{ unfold typecheck_expr at 2; fold typecheck_expr.
  by rewrite denote_tc_assert_andp. }
simpl in H.
unfold force_val1 in H; super_unfold_lift.
destruct (sem_cast _ _ _); [auto | apply tc_val_Vundef in H; contradiction].
Qed.

End mpred.

Definition func_tycontext_t_denote :=
forall p t id ty ,  list_norepet (map fst p ++ map fst t ) ->
((make_tycontext_t p t) !! id = Some ty <-> (In (id,ty) p \/ In (id,ty) t)).

Definition func_tycontext_v_denote :=
forall v id ty, list_norepet (map fst v) ->
((make_tycontext_v v) !! id = Some ty <-> In (id,ty) v).

Lemma func_tycontext_v_sound : func_tycontext_v_denote.
unfold func_tycontext_v_denote. intros.
split; intros; induction v. simpl in *.
setoid_rewrite Maps.PTree.gempty in H0. congruence.

simpl in *. destruct a. inv H. setoid_rewrite Maps.PTree.gsspec in H0. if_tac in H0.
inv H0. auto. tauto.

inv H0.

simpl in *. destruct a. simpl in *. setoid_rewrite Maps.PTree.gsspec. destruct H0.
inv H0. if_tac. auto. tauto. inv H. if_tac. subst.
clear - H0 H3. rewrite in_map_iff in H3. destruct H3. exists (i,ty). auto.
apply IHv; auto.
Qed.


(*Lemma set_inside : forall i0 t1 t p id,
list_disjoint (map fst p) (i0 :: map fst t) ->
(fold_right
          (fun param : ident * type =>
           Maps.PTree.set (fst param) (snd param, true))
          (Maps.PTree.set i0 (t1, false)
             (fold_right
                (fun (temp : ident * type) (tenv : Maps.PTree.t (type * bool)) =>
                 let (id, ty) := temp in Maps.PTree.set id (ty, false) tenv)
                (Maps.PTree.empty (type * bool)) t)) p) !! id =
(Maps.PTree.set i0 (t1, false) (
(fold_right
          (fun param : ident * type =>
           Maps.PTree.set (fst param) (snd param, true))
                (fold_right
                (fun (temp : ident * type) (tenv : Maps.PTree.t (type * bool)) =>
                 let (id, ty) := temp in Maps.PTree.set id (ty, false) tenv)
                (Maps.PTree.empty (type * bool)) t)) p)) !! id
.
Proof.
intros.
induction t.
  simpl in *. setoid_rewrite Maps.PTree.gsspec.
  if_tac.
    subst.
    induction p.
      simpl in *. setoid_rewrite Maps.PTree.gsspec. rewrite peq_true. auto.

      simpl in *. setoid_rewrite Maps.PTree.gsspec. if_tac. subst.
      clear - H. unfold list_disjoint in *. specialize (H (fst a) (fst a)).
      contradiction H; simpl; auto.
      apply IHp. unfold list_disjoint in *. intros.
      apply H; simpl in *; auto.

    induction p.
       simpl in *. setoid_rewrite Maps.PTree.gsspec. if_tac. tauto.
       auto.

       simpl in *. setoid_rewrite Maps.PTree.gsspec. destruct a.
       simpl in *. if_tac. auto. setoid_rewrite IHp. auto. unfold list_disjoint in *.
       intros. apply H; simpl in *; auto.

  simpl in *. setoid_rewrite Maps.PTree.gsspec. if_tac.
    subst.
    induction p.
      simpl in *. setoid_rewrite Maps.PTree.gsspec. rewrite -> peq_true in *.
      auto.

      simpl in *. setoid_rewrite Maps.PTree.gsspec. setoid_rewrite Maps.PTree.gsspec in IHp. setoid_rewrite Maps.PTree.gsspec in IHt. rewrite Maps.PTree.gsspec in IHt.
      destruct a0 as (i,t0). simpl in *.
      if_tac. subst. clear - H. specialize (H i i). contradiction H; simpl; auto.
      apply IHp.
      unfold list_disjoint in *. intros. apply H; simpl in *; auto.
      intros. apply IHt. unfold list_disjoint in *. intros; simpl in *; apply H;  auto.
      auto. auto. tauto.

    destruct a. simpl in *. induction p.
      simpl in *. setoid_rewrite Maps.PTree.gsspec. if_tac; subst. tauto.
      repeat setoid_rewrite Maps.PTree.gsspec. auto.

      simpl in *. destruct a. simpl in *.
      spec IHt. unfold list_disjoint in *. intros; apply H; simpl in *; auto.
      tauto.
      setoid_rewrite Maps.PTree.gsspec. setoid_rewrite Maps.PTree.gsspec in IHp. if_tac.
        subst.  auto.

        apply IHp. unfold list_disjoint in *.   intros. apply H. simpl in *.
        auto. auto. intros. rewrite if_false; auto. rewrite /lookup /ptree_lookup. reflexivity.

Qed.*)

Lemma func_tycontext_t_sound : func_tycontext_t_denote.
Proof.
  unfold func_tycontext_t_denote.
  split; intros;
  unfold make_tycontext_t in *;
  apply list_norepet_app in H; destruct H as [? [? ?]].
  + induction t; induction p; simpl in *.
    - setoid_rewrite Maps.PTree.gempty in H0; congruence.
    - left.
      destruct a; simpl in *. setoid_rewrite Maps.PTree.gsspec in H0. if_tac in H0.
      inv H0. auto.
      inv H.  destruct IHp; auto. unfold list_disjoint.  intros. inv H4.
      destruct H.
    - right.
      destruct a. simpl in *. setoid_rewrite Maps.PTree.gsspec in H0.
      if_tac in H0. subst. inv H0. auto. destruct IHt. inv H1; auto.
      unfold list_disjoint in *. intros. inv H4. auto. tauto. tauto.
    - simpl in *.
      setoid_rewrite Maps.PTree.gsspec in H0. setoid_rewrite Maps.PTree.gsspec in IHt.
      if_tac in H0.
      * destruct a0. simpl in *.
        subst. inv H0. tauto.
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
            ** inv H7; tauto.
            ** auto.
          -- auto.
        ++ left.
           right. apply H4.
        ++ right. auto.
  + induction t; induction p; simpl in *.
    - tauto.
    - setoid_rewrite Maps.PTree.gsspec. if_tac.
      * subst. destruct a. simpl in *.
        destruct H0; [destruct H0 |].
       ++ inv H0. auto.
       ++ subst.
          clear - H H0. inv H. rewrite in_map_iff in H3. destruct H3.
          exists (i,ty). auto.
       ++ inv H0.
      * destruct H0.
       ++ destruct a. destruct H0.
         -- subst. inv H0.
         -- simpl in *. apply IHp.
           ** inv H; auto.
           ** intro. intros. inv H5.
           ** left. subst. auto.
       ++ inv H0.
    - destruct H0; [| destruct H0].
      * inv H0.
      * destruct a. simpl in *. inv H0; subst.
        setoid_rewrite Maps.PTree.gsspec. rewrite peq_true. auto.
      * destruct a. simpl in *. setoid_rewrite Maps.PTree.gsspec.
        if_tac.
       ++ subst. clear -H0 H1. inv H1. rewrite in_map_iff in H3.
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
          setoid_rewrite Maps.PTree.gsspec. rewrite peq_true. auto.
       ++ subst.
          setoid_rewrite Maps.PTree.gsspec. setoid_rewrite Maps.PTree.gsspec in IHt. if_tac.
         -- subst. inv H. rewrite in_map_iff in H5.
            destruct H5. exists (i0,ty); auto.
         -- spec IHp. auto. spec IHp; auto.
      * simpl in *. setoid_rewrite Maps.PTree.gsspec. if_tac.
       ++ subst. destruct H0.
         -- inv H0. specialize (H2 i0 i0). destruct H2; simpl; auto.
         -- subst.
            spec IHt; [auto |].
            setoid_rewrite Maps.PTree.gsspec in IHt. rewrite -> peq_true in *. auto.
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
            setoid_rewrite Maps.PTree.gsspec in IHt.
            if_tac in IHt.
           ** tauto.
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

Section mpred.

Context `{!heapGS Σ}.

Lemma tc_exprlist_length : forall {CS: compspecs} Delta tl el rho,
denote_tc_assert (typecheck_exprlist Delta tl el) rho ⊢
⌜length tl = length el⌝.
Proof.
intros. generalize dependent el. induction tl; intros. simpl in *. destruct el; auto.
simpl. destruct el; try iIntros "[]". simpl.
rewrite !denote_tc_assert_andp IHtl.
by iIntros "(_ & ->)".
Qed.

Lemma neutral_cast_tc_val : forall {CS: compspecs} e t rho Delta,
true = is_neutral_cast (implicit_deref (typeof e)) t ->
typecheck_environ Delta rho ->
denote_tc_assert (typecheck_expr Delta e) rho ⊢
⌜tc_val t (eval_expr e rho)⌝.
Proof.
intros.
rewrite typecheck_expr_sound; last done.
iIntros (?); iPureIntro; eapply neutral_cast_subsumption'; eauto.
Qed.

Definition typecheck_tid_ptr_compare
Delta (id : ident) :=
match (temp_types Delta) !! id with
| Some t => is_int_type t
| None => false
end.

Lemma typecheck_tid_ptr_compare_sub:
   forall Delta Delta',
    tycontext_sub Delta Delta' ->
    forall id : ident, typecheck_tid_ptr_compare Delta id = true ->
                typecheck_tid_ptr_compare Delta' id = true.
Proof.
unfold typecheck_tid_ptr_compare;
intros.
destruct H as [? _].
specialize (H id).
destruct ((temp_types Delta) !! id) as [? |]; try discriminate.
destruct ((temp_types Delta') !! id) as [? |]; try contradiction.
 destruct H; subst; auto.
Qed.

Lemma int64_eq_e:
 forall i j, Int64.eq i j = true -> i=j.
Proof.
intros.
pose proof (Int64.eq_spec i j). rewrite H in H0; auto.
Qed.

Lemma tc_val_sem_cast:
  forall {CS: compspecs} t2 e2 rho Delta,
      typecheck_environ Delta rho ->
      denote_tc_assert (typecheck_expr Delta e2) rho ∧
      denote_tc_assert (isCastResultType (typeof e2) t2 e2) rho ⊢
      ⌜tc_val t2 (force_val (sem_cast (typeof e2) t2 (eval_expr e2 rho)))⌝.
Proof.
intros.
iIntros "H"; iApply (typecheck_expr_sound _ _ (Ecast e2 t2)); first done.
unfold typecheck_expr at 2; fold typecheck_expr.
by rewrite denote_tc_assert_andp.
Qed.

Section CENV_SUB.

Lemma cenv_sub_complete_type:
  forall cs1 cs2, cenv_sub (@cenv_cs cs1) (@cenv_cs cs2) ->
  forall t, complete_type (@cenv_cs cs1) t = true -> 
      complete_type (@cenv_cs cs2) t = true.
Proof.
intros until t.
apply complete_type_stable.
intros.
specialize (H id).
hnf in H. rewrite H0 in H. auto.
Qed.

Lemma cenv_sub_e:
  forall env1 env2, cenv_sub env1 env2 ->
    forall i c,  env1 !! i = Some c -> env2 !! i = Some c.
Proof.
intros.
specialize (H i).
hnf in H. rewrite H0 in H; auto.
Qed.

Lemma eval_expr_cenv_sub_eq {CS CS'} (CSUB: cenv_sub (@cenv_cs CS) (@cenv_cs CS')) rho:
  forall e, @eval_expr CS e rho <> Vundef -> 
    @eval_expr CS e rho = @eval_expr CS' e rho
 with eval_lvalue_cenv_sub_eq {CS CS'} (CSUB: cenv_sub (@cenv_cs CS) (@cenv_cs CS')) rho:
  forall e, @eval_lvalue CS e rho <> Vundef -> 
    @eval_lvalue CS e rho = @eval_lvalue CS' e rho.
Proof.
-
clear eval_expr_cenv_sub_eq.
induction e; simpl; intros; auto; super_unfold_lift.
 + (* unop *)
  forget (@eval_expr CS e rho) as v;
  forget (@eval_expr CS' e rho) as v'.
  clear - CSUB IHe H.
  unfold eval_unop, sem_unary_operation in *.
  destruct u; simpl in *; auto; unfold bool_val in *; simpl in *;
  destruct (typeof e)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ]; auto;
  destruct v; simpl in *;  try solve [contradiction H; auto];
  try solve [ rewrite <- IHe by (intro Hx; inv Hx); auto].
  simple_if_tac; auto.
  contradiction H; auto.
 + (* binop *)
  forget (@eval_expr CS e1 rho) as v1;
  forget (@eval_expr CS' e1 rho) as v1'.
  forget (@eval_expr CS e2 rho) as v2;
  forget (@eval_expr CS' e2 rho) as v2'.
  clear - CSUB IHe1 IHe2 H.
  destruct (Val.eq v1 Vundef); [ | destruct (Val.eq v2 Vundef)].
  * subst.
   exfalso; apply H; clear.
   unfold sem_binary_operation'.
   destruct b; auto;
  destruct (typeof e1)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ]; auto;
  destruct (typeof e2)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ]; auto;
  destruct v2; auto;
  unfold sem_add; 
  simpl; unfold sem_add_int_ptr, sem_add_ptr_int, sem_add_long_ptr, sem_add_ptr_long,
      sem_sub_pi, sem_sub_pl, sem_sub_pp;
  try simple_if_tac; auto;
  try solve [unfold sem_cmp; simpl; simple_if_tac; auto].
 * subst.
   exfalso; apply H; clear.
   unfold sem_binary_operation'.
   destruct b; auto;
  destruct (typeof e1)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ]; auto;
  destruct (typeof e2)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ]; auto;
  try (destruct v1; reflexivity);
  unfold sem_add, sem_cmp; 
  simpl; unfold sem_add_int_ptr, sem_add_ptr_int, sem_add_long_ptr, sem_add_ptr_long,
      sem_sub_pi, sem_sub_pl, sem_sub_pp;
  try simple_if_tac; auto;
  try (destruct v1; reflexivity).
 *
   rewrite <- (IHe1 n) in *.
   rewrite <- (IHe2 n0) in *.
  clear IHe1 IHe2.
  destruct b; auto;
  unfold sem_binary_operation' in *; simpl in *;
  unfold sem_add, sem_sub in *; simpl in *;
  destruct (typeof e1)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ]; auto;
  destruct (typeof e2)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ]; auto;
  simpl in *;
  unfold sem_add_int_ptr, sem_add_ptr_int, sem_add_long_ptr, sem_add_ptr_long,
      sem_sub_pi, sem_sub_pl, sem_sub_pp in *.
all: try (
  destruct (complete_type (@cenv_cs CS) t) eqn:H5;
    [ | contradiction H; reflexivity];
  rewrite (cenv_sub_complete_type _ _ CSUB _ H5); auto);
  try (
  unfold Cop.sem_add_ptr_int, Cop.sem_add_ptr_long;
  rewrite (cenv_sub_sizeof CSUB _ H5); auto).
 + (* cast *)
  forget (@eval_expr CS e rho) as v;
  forget (@eval_expr CS' e rho) as v'.
  clear - CSUB IHe H.
  destruct (Val.eq v Vundef).
  *
    subst. clear IHe.  exfalso; apply H; clear H.
  unfold sem_cast.
  destruct (classify_cast (typeof e) t); auto.
  * rewrite <- IHe; auto.
 + (* field *)
  specialize (eval_lvalue_cenv_sub_eq _ _ CSUB rho e).
  destruct (Val.eq (@eval_expr CS e rho) Vundef).
  *
  clear IHe.
  exfalso; apply H; clear H;
  unfold eval_field;
  destruct (typeof e); auto;
  destruct ((@cenv_cs CS) !! i0) eqn:?H; auto;
  destruct (field_offset (@cenv_cs CS) i (co_members c)) as [ [? [|]] | ] eqn:?H; auto;
  destruct (union_field_offset (@cenv_cs CS) i (co_members c)) as [ [? [|]] | ] eqn:?H; auto;
  clear - e0;
  induction e; simpl in *; auto; rewrite ?e0; auto.
 * 
  rewrite <- eval_lvalue_cenv_sub_eq; auto.
  -- 
   unfold eval_field in *.
   destruct (typeof e); auto.
   ++
   destruct ((@cenv_cs CS) !! i0) eqn:?H; auto;
     [ |  contradiction H; destruct (@eval_lvalue CS e rho); reflexivity].
   assert (H1 := CSUB i0); hnf in H1; rewrite H0 in H1; rewrite H1.
   destruct (field_offset (@cenv_cs CS) i (co_members c)) as [[? [|]] | ] eqn:H2;
     [ | contradiction H; destruct (@eval_lvalue CS e rho); reflexivity .. ].
   rewrite <- (field_offset_stable (@cenv_cs CS) (@cenv_cs CS')) in H2; 
    try eassumption.
    rewrite H2; auto.
    intros. specialize (CSUB id). hnf in CSUB; rewrite H3 in CSUB; auto.
     apply co_consistent_complete;  apply (cenv_consistent i0); auto. 
  ++
    destruct ((@cenv_cs CS) !! i0) eqn:?H; auto;
     [ |  contradiction H; destruct (@eval_lvalue CS e rho); reflexivity].
   assert (H1 := CSUB i0); hnf in H1; rewrite H0 in H1; rewrite H1.
   destruct (union_field_offset (@cenv_cs CS) i (co_members c)) as [[? [|]] | ] eqn:H2;
     [ | contradiction H; destruct (@eval_lvalue CS e rho); reflexivity .. ].  
   rewrite <- (union_field_offset_stable (@cenv_cs CS) (@cenv_cs CS')) in H2; 
    try eassumption.
    rewrite H2; auto.
    intros. specialize (CSUB id). hnf in CSUB; rewrite H3 in CSUB; auto.
     apply co_consistent_complete;  apply (cenv_consistent i0); auto. 
  --
  contradict H. rewrite H.
  clear.
  unfold eval_field.
  destruct (typeof e); simpl; auto.
  destruct ((@cenv_cs CS) !! i0); auto.
  destruct (field_offset (@cenv_cs CS) i (co_members c)) as [[? [|]] | ] ; auto.
  destruct ((@cenv_cs CS) !! i0); auto.
  destruct (union_field_offset (@cenv_cs CS) i (co_members c)) as [[? [|]] | ] ; auto.
 + unfold expr.sizeof.
   destruct (complete_type (@cenv_cs CS) t) eqn:?H.
  rewrite (cenv_sub_complete_type _ _ CSUB _ H0); auto.
  rewrite (cenv_sub_sizeof CSUB _ H0); auto.
  contradiction H; auto.
 + unfold expr.alignof.
   destruct (complete_type (@cenv_cs CS) t) eqn:?H.
  rewrite (cenv_sub_complete_type _ _ CSUB _ H0); auto.
  rewrite (cenv_sub_alignof CSUB _ H0); auto.
  contradiction H; auto.
-
  clear eval_lvalue_cenv_sub_eq.
  induction e; intros; auto.
  simpl. auto.
  simpl.
  unfold_lift.
  assert (@eval_lvalue CS e rho <> Vundef). {
    clear - H.
    contradict H.
    simpl; unfold_lift.
  destruct (typeof e); simpl; auto.
  destruct ((@cenv_cs CS) !! i0); auto.
  destruct (field_offset (@cenv_cs CS) i (co_members c)) as [[? [|]] | ] ; auto.
   rewrite H; auto.
  destruct ((@cenv_cs CS) !! i0); auto.
  destruct (union_field_offset (@cenv_cs CS) i (co_members c)) as [[? [|]] | ] ; auto.
   rewrite H; auto.
  }
  specialize (IHe H0).
  rewrite <- IHe.
  unfold eval_field.
  destruct (typeof e) eqn:H9; simpl; auto;
  destruct ((@cenv_cs CS) !! i0) eqn:?H; auto;
   try solve [contradiction H; simpl; unfold_lift; rewrite H9; simpl; rewrite H1; reflexivity];
  rewrite (cenv_sub_e _ _ CSUB _ _ H1).
  destruct (field_offset (@cenv_cs CS) i (co_members c))  as [[? [|]] | ] eqn:?H; auto;
  rewrite (field_offset_stable (@cenv_cs CS)); try rewrite H2; auto;
  try solve [apply cenv_sub_e; auto]; 
  try solve [apply co_consistent_complete;  apply (cenv_consistent i0); auto]. 
  destruct (union_field_offset (@cenv_cs CS) i (co_members c))  as [[? [|]] | ] eqn:?H; auto;
  rewrite (union_field_offset_stable (@cenv_cs CS)); try rewrite H2; auto;
  try solve [apply cenv_sub_e; auto]; 
  try solve [apply co_consistent_complete;  apply (cenv_consistent i0); auto]. 
Qed.


Lemma eval_expr_cenv_sub_Vint {CS CS'} (CSUB: cenv_sub (@cenv_cs CS) (@cenv_cs CS')) rho:
  forall e i, @eval_expr CS e rho = Vint i -> @eval_expr CS' e rho = Vint i.
Proof.
 intros. 
 rewrite <- (@eval_expr_cenv_sub_eq _ _ CSUB rho e); auto; congruence.
Qed.
Lemma eval_expr_cenv_sub_Vlong {CS CS'} (CSUB: cenv_sub (@cenv_cs CS) (@cenv_cs CS')) rho: forall e i, 
    @eval_expr CS e rho = Vlong i -> @eval_expr CS' e rho = Vlong i.
 intros. 
 rewrite <- (@eval_expr_cenv_sub_eq _ _ CSUB rho e); auto; congruence.
Qed.
Lemma eval_expr_cenv_sub_Vptr {CS CS'} (CSUB: cenv_sub (@cenv_cs CS) (@cenv_cs CS')) rho: forall e b i, 
    @eval_expr CS e rho = Vptr b i -> @eval_expr CS' e rho = Vptr b i.
 intros. 
 rewrite <- (@eval_expr_cenv_sub_eq _ _ CSUB rho e); auto; congruence.
Qed.
Lemma eval_expr_cenv_sub_Vfloat {CS CS'} (CSUB: cenv_sub (@cenv_cs CS) (@cenv_cs CS')) rho: forall e f, 
    @eval_expr CS e rho = Vfloat f -> @eval_expr CS' e rho = Vfloat f.
 intros. 
 rewrite <- (@eval_expr_cenv_sub_eq _ _ CSUB rho e); auto; congruence.
Qed.
Lemma eval_expr_cenv_sub_Vsingle {CS CS'} (CSUB: cenv_sub (@cenv_cs CS) (@cenv_cs CS')) rho: forall e f, 
    @eval_expr CS e rho = Vsingle f -> @eval_expr CS' e rho = Vsingle f.
 intros. 
 rewrite <- (@eval_expr_cenv_sub_eq _ _ CSUB rho e); auto; congruence.
Qed.

Lemma denote_tc_iszero_eval_expr_cenv_sub {CS CS'} (CSUB : cenv_sub (@cenv_cs CS) (@cenv_cs CS')) rho e:
  (` denote_tc_iszero) (@eval_expr CS e) rho ⊢
  (` denote_tc_iszero) (@eval_expr CS' e) rho.
Proof.
  unfold denote_tc_iszero, liftx, lift in *; simpl in *.
  remember (@eval_expr CS e rho) as v; symmetry in Heqv.
  destruct v; simpl; try iIntros "[]".
  by rewrite (eval_expr_cenv_sub_Vint CSUB _ _ _ Heqv).
  by rewrite (eval_expr_cenv_sub_Vlong CSUB _ _ _ Heqv).
Qed.

Lemma denote_tc_nonzero_eval_expr_cenv_sub {CS CS'} (CSUB : cenv_sub (@cenv_cs CS) (@cenv_cs CS')) rho e:
    (` denote_tc_nonzero) (@eval_expr CS e) rho ⊢
    (` denote_tc_nonzero) (@eval_expr CS' e) rho.
Proof.
  unfold denote_tc_nonzero, liftx, lift in *; simpl in *.
  remember (@eval_expr CS e rho) as v; symmetry in Heqv.
  destruct v; simpl; try iIntros "[]".
  by rewrite (eval_expr_cenv_sub_Vint CSUB _ _ _ Heqv).
  by rewrite (eval_expr_cenv_sub_Vlong CSUB _ _ _ Heqv).
Qed.

Lemma isptr_eval_expr_cenv_sub {CS CS'} (CSUB : cenv_sub (@cenv_cs CS) (@cenv_cs CS')) rho e
    (E : isptr (@eval_expr CS e rho)):
  isptr (@eval_expr CS' e rho).
Proof.
  remember (@eval_expr CS e rho) as v; symmetry in Heqv.
  destruct v; simpl in E; try contradiction.
  rewrite (eval_expr_cenv_sub_Vptr CSUB _ _ _ _ Heqv); trivial. 
Qed.

Lemma isint_eval_expr_cenv_sub {CS CS'} (CSUB : cenv_sub (@cenv_cs CS) (@cenv_cs CS')) rho e
    (E: is_int I32 Signed (@eval_expr CS e rho)):
  is_int I32 Signed (@eval_expr CS' e rho).
Proof.
  remember (@eval_expr CS e rho) as v; symmetry in Heqv.
  destruct v; simpl in E; try contradiction.
  rewrite (eval_expr_cenv_sub_Vint CSUB _ _ _ Heqv); trivial. 
Qed.

Lemma islong_eval_expr_cenv_sub {CS CS'} (CSUB : cenv_sub (@cenv_cs CS) (@cenv_cs CS')) rho e
    (E: is_long (@eval_expr CS e rho)):
  is_long (@eval_expr CS' e rho).
Proof.
  remember (@eval_expr CS e rho) as v; symmetry in Heqv.
  destruct v; simpl in E; try contradiction.
  rewrite (eval_expr_cenv_sub_Vlong CSUB _ _ _ Heqv); trivial. 
Qed.

Lemma denote_tc_test_eq_eval_expr_cenv_sub {CS CS'} (CSUB : cenv_sub (@cenv_cs CS) (@cenv_cs CS')) rho e1 e2:
    (` denote_tc_test_eq) (@eval_expr CS e1) (@eval_expr CS e2) rho ⊢
    (` denote_tc_test_eq) (@eval_expr CS' e1) (@eval_expr CS' e2) rho.
Proof.
  unfold liftx, lift in *; simpl in *.
  remember (@eval_expr CS e1 rho) as v1; symmetry in Heqv1.
  remember (@eval_expr CS e2 rho) as v2; symmetry in Heqv2.
  destruct v1; destruct v2; simpl; try iIntros "[]"; simpl;
  rewrite
     ?(eval_expr_cenv_sub_Vint CSUB _ _ _ Heqv1)
     ?(eval_expr_cenv_sub_Vlong CSUB _ _ _ Heqv1)
     ?(eval_expr_cenv_sub_Vint CSUB _ _ _ Heqv2)
     ?(eval_expr_cenv_sub_Vlong CSUB _ _ _ Heqv2)
     ?(eval_expr_cenv_sub_Vptr CSUB _ _ _ _ Heqv1)
     ?(eval_expr_cenv_sub_Vptr CSUB _ _ _ _ Heqv2); simpl; trivial.
Qed. 

Lemma denote_tc_test_order_eval_expr_cenv_sub {CS CS'} (CSUB : cenv_sub (@cenv_cs CS) (@cenv_cs CS')) rho e1 e2:
    (` denote_tc_test_order) (@eval_expr CS e1) (@eval_expr CS e2) rho ⊢
    (` denote_tc_test_order) (@eval_expr CS' e1) (@eval_expr CS' e2) rho.
Proof.
  unfold liftx, lift in *; simpl in *.
  remember (@eval_expr CS e1 rho) as v1; symmetry in Heqv1.
  remember (@eval_expr CS e2 rho) as v2; symmetry in Heqv2.
  destruct v1; destruct v2; simpl; try iIntros "[]"; simpl;
  rewrite
     ?(eval_expr_cenv_sub_Vint CSUB _ _ _ Heqv1)
     ?(eval_expr_cenv_sub_Vlong CSUB _ _ _ Heqv1)
     ?(eval_expr_cenv_sub_Vint CSUB _ _ _ Heqv2)
     ?(eval_expr_cenv_sub_Vlong CSUB _ _ _ Heqv2)
     ?(eval_expr_cenv_sub_Vptr CSUB _ _ _ _ Heqv1)
     ?(eval_expr_cenv_sub_Vptr CSUB _ _ _ _ Heqv2); simpl; trivial.
Qed.

Lemma denote_tc_igt_eval_expr_cenv_sub {CS CS'} (CSUB : cenv_sub (@cenv_cs CS) (@cenv_cs CS')) rho e i:
    (` denote_tc_igt i) (@eval_expr CS e) rho ⊢
    (` denote_tc_igt i) (@eval_expr CS' e) rho.
Proof.
  unfold liftx, lift in *; simpl in *.
  remember (@eval_expr CS e rho) as v; symmetry in Heqv.
  destruct v; simpl; try iIntros "[]"; simpl.
  rewrite (eval_expr_cenv_sub_Vint CSUB _ _ _ Heqv); simpl; trivial.
Qed.

Lemma denote_tc_lgt_eval_expr_cenv_sub {CS CS'} (CSUB : cenv_sub (@cenv_cs CS) (@cenv_cs CS')) rho e i:
    (` denote_tc_lgt i) (@eval_expr CS e) rho ⊢
    (` denote_tc_lgt i) (@eval_expr CS' e) rho.
Proof.
  unfold liftx, lift in *; simpl in *.
  remember (@eval_expr CS e rho) as v; symmetry in Heqv.
  destruct v; simpl; try iIntros "[]"; simpl.
  rewrite (eval_expr_cenv_sub_Vlong CSUB _ _ _ Heqv); simpl; trivial.
Qed.

Lemma denote_tc_Zge_eval_expr_cenv_sub {CS CS'} (CSUB : cenv_sub (@cenv_cs CS) (@cenv_cs CS')) rho e z:
    (` denote_tc_Zge z) (@eval_expr CS e) rho ⊢
    (` denote_tc_Zge z) (@eval_expr CS' e) rho.
Proof.
  unfold liftx, lift in *; simpl in *.
  remember (@eval_expr CS e rho) as v; symmetry in Heqv.
  destruct v; simpl; try iIntros "[]"; simpl.
  + rewrite (eval_expr_cenv_sub_Vfloat CSUB _ _ _ Heqv); simpl; trivial.
  + rewrite (eval_expr_cenv_sub_Vsingle CSUB _ _ _ Heqv); simpl; trivial.
Qed.

Lemma denote_tc_Zle_eval_expr_cenv_sub {CS CS'} (CSUB : cenv_sub (@cenv_cs CS) (@cenv_cs CS')) rho e z:
    (` denote_tc_Zle z) (@eval_expr CS e) rho ⊢
    (` denote_tc_Zle z) (@eval_expr CS' e) rho.
Proof.
  unfold liftx, lift in *; simpl in *.
  remember (@eval_expr CS e rho) as v; symmetry in Heqv.
  destruct v; simpl; try iIntros "[]"; simpl.
  + rewrite (eval_expr_cenv_sub_Vfloat CSUB _ _ _ Heqv); simpl; trivial.
  + rewrite (eval_expr_cenv_sub_Vsingle CSUB _ _ _ Heqv); simpl; trivial.
Qed.

Lemma istrue_sameblock_eval_expr_cenv_sub {CS CS'} (CSUB : cenv_sub (@cenv_cs CS) (@cenv_cs CS')) rho e1 e2
    (E: is_true (sameblock (@eval_expr CS e1 rho) (@eval_expr CS e2 rho))):
  is_true (sameblock (@eval_expr CS' e1 rho) (@eval_expr CS' e2 rho)).
Proof.
  unfold is_true, sameblock in *; simpl in *.
  remember (@eval_expr CS e1 rho) as v1; symmetry in Heqv1.
  remember (@eval_expr CS e2 rho) as v2; symmetry in Heqv2.
  destruct v1; destruct v2; simpl in E; try contradiction; simpl;
  try rewrite (eval_expr_cenv_sub_Vptr CSUB _ _ _ _ Heqv1);
  try rewrite (eval_expr_cenv_sub_Vptr CSUB _ _ _ _ Heqv2); simpl; trivial.
Qed.

Lemma denote_tc_nodivover_eval_expr_cenv_sub {CS CS'} (CSUB : cenv_sub (@cenv_cs CS) (@cenv_cs CS')) rho e1 e2:
      (` denote_tc_nodivover) (@eval_expr CS e1) (@eval_expr CS e2) rho ⊢
      (` denote_tc_nodivover) (@eval_expr CS' e1) (@eval_expr CS' e2) rho.
Proof.
  unfold liftx, lift, denote_tc_nodivover in *; simpl in *.
  remember (@eval_expr CS e1 rho) as v1; symmetry in Heqv1.
  remember (@eval_expr CS e2 rho) as v2; symmetry in Heqv2.
  destruct v1; destruct v2; simpl; try iIntros "[]"; simpl;
  try rewrite (eval_expr_cenv_sub_Vint CSUB _ _ _ Heqv1);
  try rewrite (eval_expr_cenv_sub_Vlong CSUB _ _ _ Heqv1);
  try rewrite (eval_expr_cenv_sub_Vint CSUB _ _ _ Heqv2);
  try rewrite (eval_expr_cenv_sub_Vlong CSUB _ _ _ Heqv2); simpl; trivial.
Qed.

Lemma denote_tc_nosignedover_eval_expr_cenv_sub {CS CS'} (CSUB : cenv_sub (@cenv_cs CS) (@cenv_cs CS')) rho e1 e2 (z:Z -> Z -> Z) (s: signedness):
      liftx (denote_tc_nosignedover z s) (@eval_expr CS e1) (@eval_expr CS e2) rho ⊢
      liftx (denote_tc_nosignedover z s) (@eval_expr CS' e1) (@eval_expr CS' e2) rho.
Proof.
  unfold liftx, lift, denote_tc_nodivover in *; simpl in *.
  remember (@eval_expr CS e1 rho) as v1; symmetry in Heqv1.
  remember (@eval_expr CS e2 rho) as v2; symmetry in Heqv2.
  destruct v1; destruct v2; simpl; try iIntros "[]"; simpl;
  try rewrite (eval_expr_cenv_sub_Vint CSUB _ _ _ Heqv1);
  try rewrite (eval_expr_cenv_sub_Vlong CSUB _ _ _ Heqv1);
  try rewrite (eval_expr_cenv_sub_Vint CSUB _ _ _ Heqv2);
  try rewrite (eval_expr_cenv_sub_Vlong CSUB _ _ _ Heqv2); simpl; trivial.
Qed.

Lemma denote_tc_assert_cenv_sub {CS CS'} (CSUB: cenv_sub (@cenv_cs CS) (@cenv_cs CS')) rho: forall a, 
    denote_tc_assert(CS := CS) a rho ⊢ denote_tc_assert(CS := CS') a rho.
Proof.
  induction a; simpl; intros; trivial.
  + unfold_lift; by rewrite IHa1 IHa2.
  + unfold_lift; by rewrite IHa1 IHa2.
  + apply (denote_tc_nonzero_eval_expr_cenv_sub CSUB).
  + apply (denote_tc_iszero_eval_expr_cenv_sub CSUB).
  + iIntros "%"; iPureIntro; apply (isptr_eval_expr_cenv_sub CSUB); trivial.
  + iIntros "%"; iPureIntro; apply (isint_eval_expr_cenv_sub CSUB); trivial.
  + iIntros "%"; iPureIntro; apply (islong_eval_expr_cenv_sub CSUB); trivial.
  + apply (denote_tc_test_eq_eval_expr_cenv_sub CSUB).
  + apply (denote_tc_test_order_eval_expr_cenv_sub CSUB).
  + apply (denote_tc_igt_eval_expr_cenv_sub CSUB).
  + apply (denote_tc_lgt_eval_expr_cenv_sub CSUB).
  + apply (denote_tc_Zge_eval_expr_cenv_sub CSUB).
  + apply (denote_tc_Zle_eval_expr_cenv_sub CSUB).
  + iIntros "%"; iPureIntro; apply (istrue_sameblock_eval_expr_cenv_sub CSUB); trivial.
  + apply (denote_tc_nodivover_eval_expr_cenv_sub CSUB).
  + destruct (typeof e) as [ | _ [ | ] _ | | | | | | | ],
       (typeof e0) as [ | _ [ | ] _ | | | | | | | ];
   try (apply (denote_tc_nosignedover_eval_expr_cenv_sub CSUB); trivial).
Qed.

(*Lemma denote_tc_assert_cenv_sub' {CS CS'} (CSUB: cenv_sub (@cenv_cs CS) (@cenv_cs CS')) rho w Delta: forall a, 
    @denote_tc_assert CS (@typecheck_expr CS Delta a) rho w ->
    @denote_tc_assert CS' (@typecheck_expr CS' Delta a) rho w.
Proof. 
  induction a; simpl; intros; trivial.
  + destruct t; auto.
    destruct i0; auto.
  + destruct t; auto.
    destruct f0; auto.
  + destruct t; auto.
    destruct f0; auto.
  + destruct t; auto.
  + destruct t; auto.
  - destruct i0; auto;
    destruct s; auto. 
  - destruct f; auto.
  - destruct (get_var_type Delta i); auto. simpl in *.
    destruct t0; auto. 
    destruct (eqb_type t t0 && (Zeq_bool z z0 && eqb_attr a a0)); auto.
  - destruct (get_var_type Delta i); auto. simpl in *.
    destruct t1; auto.
    destruct ((eqb_typelist t t1 && eqb_type t0 t2 && eqb_calling_convention c c0)); auto.
  + destruct ((temp_types Delta) !! i); auto.
    destruct (is_neutral_cast t0 t || same_base_type t0 t); auto.    
  + destruct t; auto; simpl in *.
  - destruct i; destruct s; auto.
  - destruct f; auto.
  - repeat rewrite denote_tc_assert_andp.
    repeat rewrite denote_tc_assert_andp in H. destruct H as [[? ?] ?].
    split.
    * split; auto.
      destruct (is_pointer_type (typeof a)); auto.
    * 
Abort.*)

Lemma bool_val_cenv_sub {CS CS'} (CSUB: cenv_sub (@cenv_cs CS) (@cenv_cs CS'))
  rho b v (Hb : bool_val (typeof b) (@eval_expr CS b rho) = Some v):
  bool_val (typeof b) (@eval_expr CS' b rho) = Some v.
Proof.
  unfold bool_val in *.
  destruct (typeof b); trivial.
  +  unfold bool_val_i in *. remember (@eval_expr CS b rho) as r; symmetry in Heqr; destruct r; inv Hb.
     rewrite ?(eval_expr_cenv_sub_Vint CSUB _ _ _ Heqr);
     rewrite ? (eval_expr_cenv_sub_Vptr CSUB _ _ _ _ Heqr); 
     trivial.
  + unfold bool_val_l in *.
      remember (@eval_expr CS b rho) as r; symmetry in Heqr; destruct r; inv Hb;
     rewrite ? (eval_expr_cenv_sub_Vlong CSUB _ _ _ Heqr); 
     rewrite ? (eval_expr_cenv_sub_Vptr CSUB _ _ _ _ Heqr); 
     trivial.
  + destruct f.
 - unfold bool_val_s in *. remember (@eval_expr CS b rho) as r; symmetry in Heqr; destruct r; inv Hb.
  rewrite (eval_expr_cenv_sub_Vsingle CSUB _ _ _ Heqr); trivial.
  - unfold bool_val_f in *. remember (@eval_expr CS b rho) as r; symmetry in Heqr; destruct r; inv Hb.
  rewrite (eval_expr_cenv_sub_Vfloat CSUB _ _ _ Heqr); trivial.
  + destruct (eqb_type (Tpointer t a) int_or_ptr_type). inv Hb.
  unfold bool_val_p in *.
  remember (@eval_expr CS b rho) as r; symmetry in Heqr; destruct r; inv Hb;
  rewrite ?(eval_expr_cenv_sub_Vint CSUB _ _ _ Heqr);
  rewrite ?(eval_expr_cenv_sub_Vlong CSUB _ _ _ Heqr);
  rewrite ?(eval_expr_cenv_sub_Vptr CSUB _ _ _ _ Heqr); trivial.
Qed.

(*Lemma sem_binary_operation_cenv_sub {ge ge'} (CSUB:cenv_sub ge ge') op v1 t1 v2 t2 m v:
  sem_binary_operation ge op v1 t1 v2 t2 m = Some v ->
  sem_binary_operation ge' op v1 t1 v2 t2 m = Some v.
Proof.
Abort.*)

Lemma typecheck_expr_sound_cenv_sub {CS CS'} (CSUB: cenv_sub (@cenv_cs CS) (@cenv_cs CS'))
      Delta rho (D:typecheck_environ Delta rho): forall e, 
    denote_tc_assert(CS := CS) (typecheck_expr(CS := CS) Delta e) rho ⊢
    ⌜@eval_expr CS e rho = @eval_expr CS' e rho⌝.
Proof.
intros.
rewrite typecheck_expr_sound; last done.
iIntros (H0); iPureIntro.
assert (@eval_expr CS e rho <> Vundef). {
  intros H1. rewrite H1 in H0. apply tc_val_Vundef in H0. auto.
}
apply eval_expr_cenv_sub_eq; auto.
Qed.

Lemma typecheck_exprlist_sound_cenv_sub {CS CS'} (CSUB: cenv_sub (@cenv_cs CS) (@cenv_cs CS'))
      Delta rho (D:typecheck_environ Delta rho): forall types e, 
    denote_tc_assert(CS := CS) (typecheck_exprlist(CS := CS) Delta types e) rho ⊢
    ⌜@eval_exprlist CS types e rho = @eval_exprlist CS' types e rho⌝.
Proof.
induction types; destruct e; intros; auto.
unfold typecheck_exprlist; fold typecheck_exprlist.
rewrite denote_tc_assert_andp.
rewrite (typecheck_expr_sound_cenv_sub CSUB); last done.
rewrite IHtypes /=; unfold_lift.
by unfold force_val1; iIntros "[-> ->]".
Qed.

End CENV_SUB.

End mpred.
