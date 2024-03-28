Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.mapsto_memory_block.
Import LiftNotation.


(***************************************

Load/store lemmas about mapsto:
  semax_load_37
  semax_load_37'
  semax_cast_load_37
  semax_cast_load_37'

***************************************)


Definition semax_load_37 := @semax_load.

Lemma derives_trans: forall {prop:bi} (P Q R:prop),
  (P ⊢ Q) -> (Q ⊢ R) -> (P ⊢ R).
Proof. intros. rewrite H H0 //. Qed.

Lemma semax_load_37' :
  forall `{!VSTGS OK_ty Σ} {OK_spec: ext_spec OK_ty} {cs: compspecs},
forall E (Delta: tycontext) sh id P Q R e1 t2 (v2: val),
    typeof_temp Delta id = Some t2 ->
    is_neutral_cast (typeof e1) t2 = true ->
    readable_share sh ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) ⊢
        ((tc_lvalue Delta e1) ∧
         (local `(tc_val (typeof e1) v2)) ∧
         (assert_of (`(mapsto sh (typeof e1)) (eval_lvalue e1) `(v2)) ∗ True)) ->
    semax E Delta (▷ PROPx P (LOCALx Q (SEPx R)))
       (Sset id e1)
       (normal_ret_assert
         (PROPx P
           (LOCALx (temp id v2 :: remove_localdef_temp id Q)
             (SEPx R)))).
Proof.
  intros.
  rename H1 into H_READABLE; rename H2 into H1.
  eapply semax_pre_post'; [ | | apply semax_load with sh t2; auto].
  + instantiate (1:= PROPx (tc_val (typeof e1) v2 :: P) (LOCALx Q (SEPx R))).
    apply later_left2.
    match goal with |- ?A ⊢ _ => rewrite <- (andp_dup A) end.
    eapply derives_trans.
    apply bi.and_mono; [apply derives_refl | apply H1].
    clear H.
    go_lowerx.
    gather_prop.
    apply bi.pure_elim_l; intro.
    apply bi.and_intro.
    apply bi.pure_intro; repeat split; try eassumption.
    apply bi.and_intro.
    rewrite bi.and_elim_r. rewrite bi.and_elim_l; auto.
    rewrite bi.and_elim_l; auto.
  + rewrite bi.and_elim_r.
    apply (derives_trans _ (⌜tc_val (typeof e1) v2⌝ ∧
                            (∃ old : val,
                              local ((` eq) (eval_id id) (` v2)) ∧ 
                              (assert_of (subst id (` old) (PROPx P (LOCALx Q (SEPx R)))))))).
    - apply bi.and_intro.
      * apply bi.exist_elim; intros.
        rewrite bi.and_elim_r.        
        constructor => rho; simpl.
        unfold subst.
        rewrite <- insert_prop.
        rewrite bi.and_elim_l.
        rewrite monPred_at_pure.
        rewrite -monPred_at_pure. (* this generalizes the index of bi_pure*)
        apply derives_refl.
      * apply bi.exist_mono. intro old.
        apply bi.and_mono; [done |].
        constructor => rho; simpl.
        unfold subst.
        rewrite <- insert_prop.
        rewrite bi.and_elim_r.
        done.
    - apply bi.pure_elim_l; intro.
      rewrite <- bi.and_exist_l.
      rewrite <- insert_local.
      apply bi.and_mono; auto.
      * simpl; unfold local, lift1; unfold_lift.
        raise_rho.
        intros; apply bi.pure_mono.
        intros; split; [congruence |].
        intro; clear H3; subst; revert H2. apply tc_val_Vundef.
      * rewrite -remove_localdef_temp_PROP.
        apply bi.exist_mono => ?; done.
  + eapply derives_trans; [eapply derives_trans; [| apply H1] | clear H1].
    - apply bi.and_mono; auto.
      rewrite <- insert_prop.
      rewrite bi.and_elim_r; auto.
    - rewrite bi.and_elim_r. rewrite bi.and_elim_r.
      iIntros "[H1 H2]"; iFrame.
Qed.

Definition semax_cast_load_37 := @semax_cast_load.

Lemma semax_cast_load_37' :
  forall `{!VSTGS OK_ty Σ} {OK_spec: ext_spec OK_ty} {cs: compspecs},
forall E (Delta: tycontext) sh id P Q R e1 t1 (v2: val),
    typeof_temp Delta id = Some t1 ->
    cast_pointer_to_bool (typeof e1) t1 = false ->
    readable_share sh ->
    (ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) ⊢
      ((tc_lvalue Delta e1) ∧
       (local (`(tc_val t1 (eval_cast (typeof e1) t1 v2)))) ∧
       (assert_of (`(mapsto sh (typeof e1)) (eval_lvalue e1) `(v2)) ∗ True))) ->
    semax E Delta (▷ PROPx P (LOCALx Q (SEPx R)))
       (Sset id (Ecast e1 t1))
       (normal_ret_assert
         (PROPx P
           (LOCALx (temp id (eval_cast (typeof e1) t1 v2) :: remove_localdef_temp id Q)
             (SEPx R)))).
Proof.
  intros until 1. intros HCAST H_READABLE H1. pose proof I.
  eapply semax_pre_post'; [ | | apply @semax_cast_load with (sh:=sh)(v2:= v2); auto].
  + instantiate (1:= PROPx (tc_val t1 (force_val (sem_cast (typeof e1) t1 v2)) :: P) (LOCALx Q (SEPx R))).
    apply later_left2.
    match goal with |- ?A ⊢ _ => rewrite <- (andp_dup A) end.
    eapply derives_trans.
    apply bi.and_mono; [apply derives_refl | apply H1].
    clear H1.
    go_lowerx.
    gather_prop.
    apply bi.pure_elim_l; intro.
    apply bi.and_intro.
    apply bi.pure_intro; repeat split; eassumption.
    apply bi.and_intro.
    rewrite bi.and_elim_r. rewrite bi.and_elim_l; auto.
    rewrite bi.and_elim_l; auto.
  + intros. rewrite bi.and_elim_r.
    eapply (derives_trans _ (⌜tc_val t1 (force_val (sem_cast (typeof e1) t1 v2))⌝ ∧
                             (∃ old : val,
                                local ((` eq) (eval_id id) (` (eval_cast (typeof e1) t1 v2))) ∧
                                (assert_of (subst id (` old) (PROPx P (LOCALx Q (SEPx R)))))))).
    - apply bi.and_intro.
      * apply bi.exist_elim; intros.
        rewrite bi.and_elim_r.
        constructor => rho; simpl.
        unfold subst.
        rewrite <- insert_prop.
        rewrite bi.and_elim_l.
        rewrite monPred_at_pure.
        rewrite -monPred_at_pure. (* this generalizes the index of bi_pure*)
        apply derives_refl.
      * apply bi.exist_mono. intro old.
        apply bi.and_mono; [done |].
        constructor => rho; simpl.
        unfold subst.
        rewrite <- insert_prop.
        rewrite bi.and_elim_r.
        done.
    - apply bi.pure_elim_l; intro.
      rewrite <- bi.and_exist_l.
      rewrite <- insert_local.
      apply bi.and_mono; auto.
      * simpl; unfold local, lift1; unfold_lift.
        constructor => ?; simpl; apply bi.pure_mono.
        unfold force_val1 in *.
        intros; split; [congruence |].
        intro; clear H3; revert H2; rewrite H4. apply tc_val_Vundef.
      * apply remove_localdef_temp_PROP.
  + eapply derives_trans; [eapply derives_trans; [| apply H1] | clear H1].
    - apply bi.and_mono; auto.
      rewrite <- insert_prop.
      rewrite bi.and_elim_r; auto.
    - rewrite bi.and_elim_r. rewrite bi.and_elim_r.
      iIntros "[H1 H2]"; iFrame.
Qed.

(***************************************

Load/store lemmas about mapsto:
  semax_load_nth_ram.
  semax_cast_load_nth_ram.
  semax_store_nth_ram.

***************************************)

Lemma semax_load_nth_ram :
  forall `{!VSTGS OK_ty Σ} {OK_spec: ext_spec OK_ty} {cs: compspecs}
    E n (Delta: tycontext) sh id P Q R e1 Pre t1 t2 v p,
    typeof e1 = t1 ->
    typeof_temp Delta id = Some t2 ->
    is_neutral_cast (typeof e1) t2 = true ->
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) ⊢
       local (`(eq p) (eval_lvalue e1)) ->
    nth_error R n = Some Pre ->
    readable_share sh ->
    (Pre ⊢ mapsto sh t1 p v ∗ True) ->
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) ⊢
      ((tc_lvalue Delta e1) ∧ local (`(tc_val t1 v))) ->
    semax E Delta (▷ PROPx P (LOCALx Q (SEPx R)))
      (Sset id e1)
      (normal_ret_assert
         (PROPx P
           (LOCALx (temp id v :: remove_localdef_temp id Q)
             (SEPx R)))).
Proof.
  intros.
  subst; eapply semax_load_37'; eauto.
  rewrite bi.and_assoc.
  apply bi.and_intro; auto.
  rewrite (add_andp _ _ H2).
  rewrite bi.and_comm. rewrite bi.and_assoc.
  erewrite SEP_nth_isolate, <- insert_SEP by eauto.
  rewrite <- local_lift2_and.
  rewrite <- local_sepcon_assoc1.
  set (PROPx P (LOCALx Q (SEPx (replace_nth n R emp)))) as PQR.
  apply (derives_trans _ ((assert_of (`(mapsto sh (typeof e1)) (eval_lvalue e1) (` v)) ∗ True)
                          ∗ PQR)).
  + apply bi.sep_mono; [| apply derives_refl].
    unfold local; super_unfold_lift; raise_rho.
    normalize.
  + rewrite -bi.sep_assoc.
    apply bi.sep_mono; auto.
Qed.

Lemma semax_cast_load_nth_ram :
  forall `{!VSTGS OK_ty Σ} {OK_spec: ext_spec OK_ty} {cs: compspecs}
    E n (Delta: tycontext) sh id P Q R e1 Pre t1 t2 v p,
    typeof e1 = t1 ->
    typeof_temp Delta id = Some t2 ->
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) ⊢
      local (`(eq p) (eval_lvalue e1)) ->
    nth_error R n = Some Pre ->
    cast_pointer_to_bool t1 t2 = false ->
    readable_share sh ->
    (Pre ⊢ mapsto sh t1 p v ∗ True) ->
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) ⊢
     ((tc_lvalue Delta e1) ∧ local (`(tc_val t2 (eval_cast t1 t2 v)))) ->
    semax E Delta (▷ PROPx P (LOCALx Q (SEPx R)))
     (Sset id (Ecast e1 t2))
     (normal_ret_assert
         (PROPx P
           (LOCALx (temp id (eval_cast t1 t2 v) :: remove_localdef_temp id Q)
             (SEPx R)))).
Proof.
  intros.
  subst; eapply semax_cast_load_37'; eauto.
  rewrite bi.and_assoc.
  apply bi.and_intro; auto.
  rewrite (add_andp _ _ H1).
  rewrite bi.and_comm. rewrite bi.and_assoc.
  erewrite SEP_nth_isolate, <- insert_SEP by eauto.
  rewrite <- local_lift2_and.
  rewrite <- local_sepcon_assoc1.
  apply (derives_trans _ ((assert_of (`( mapsto sh (typeof e1)) (eval_lvalue e1) `( v)) ∗ True) ∗
                          PROPx P (LOCALx Q (SEPx (replace_nth n R emp))))).
  + apply bi.sep_mono; [| apply derives_refl].
    unfold local, lift1; unfold_lift; raise_rho; simpl.
    normalize.
  + rewrite -bi.sep_assoc.
    apply bi.sep_mono; auto.
Qed.

Lemma semax_store_nth_ram:
  forall `{!VSTGS OK_ty Σ} {OK_spec: ext_spec OK_ty} {cs: compspecs}
    E n Delta P Q R e1 e2 Pre Post p v sh t1,
    typeof e1 = t1 ->
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) ⊢
       local (`(eq p) (eval_lvalue e1)) ->
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) ⊢
       local (`(eq v) (eval_expr (Ecast e2 t1))) ->
    nth_error R n = Some Pre ->
    writable_share sh ->
    (Pre ⊢ mapsto_ sh t1 p ∗ (mapsto sh t1 p v -∗ Post)) ->
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) ⊢
     ((tc_lvalue Delta e1) ∧ (tc_expr Delta (Ecast e2 t1))) ->
    semax E Delta
     (▷ PROPx P (LOCALx Q (SEPx R)))
     (Sassign e1 e2)
     (normal_ret_assert
        (PROPx P (LOCALx Q (SEPx (replace_nth n R Post))))).
Proof.
  intros.
  eapply semax_pre_simple; [| eapply semax_post'; [| apply semax_store; eauto]].
  + apply later_left2.
    apply bi.and_intro;  [subst; auto |].
    simpl lifted.
    rewrite (add_andp _ _ H0).
    rewrite (add_andp _ _ H1).
    erewrite SEP_nth_isolate, <- insert_SEP by eauto.
    rewrite !(bi.and_comm _ (local _)).
    rewrite <- (andp_dup (local (`(eq p) (eval_lvalue e1)))), <-bi.and_assoc.
    do 3 rewrite <- local_sepcon_assoc2.  rewrite <- local_sepcon_assoc1.
    apply (derives_trans _ (((assert_of (`( mapsto_ sh (typeof e1)) (eval_lvalue e1))) ∗ 
                             (assert_of (`(bi_wand (mapsto sh t1 p v) Post)))) ∗
                            ((local ((` (eq p)) (eval_lvalue e1))) ∧
                             (local ((` (eq v)) (eval_expr (Ecast e2 t1))) ∧
                             (local (tc_environ Delta)) ∧ 
                             PROPx P (LOCALx Q (SEPx (replace_nth n R emp))))))).
    - apply bi.sep_mono; [| apply derives_refl].
      unfold local, lift1; unfold_lift; raise_rho; simpl.
      subst t1.
      normalize.
    - rewrite -bi.sep_assoc.
      apply derives_refl.
  + rewrite bi.sep_assoc.
    rewrite ->!local_sepcon_assoc2, <- !local_sepcon_assoc1.
    erewrite SEP_replace_nth_isolate with (Rn' := Post), <- insert_SEP by eauto.
    apply bi.sep_mono; auto.
    change (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2)))
      with (eval_expr (Ecast e2 (typeof e1))).
    Opaque eval_lvalue eval_expr.
    unfold local, lift1; unfold_lift; raise_rho; simpl.
    normalize.
    Transparent eval_lvalue eval_expr.
    subst t1.
    apply modus_ponens_wand.
Qed.

Lemma semax_store_nth_ram_union_hack:
  forall `{!VSTGS OK_ty Σ} {OK_spec: ext_spec OK_ty} {cs: compspecs}
    E n Delta P Q R e1 e2 Pre Post p v v' ch ch' sh t1 t2,
    typeof e1 = t1 ->
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) ⊢
       local (`(eq p) (eval_lvalue e1)) ->
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) ⊢
       local (`(eq v) (eval_expr (Ecast e2 t1))) ->
    nth_error R n = Some Pre ->
    writable_share sh ->
    (numeric_type t1 && numeric_type t2)%bool = true ->
    decode_encode_val_ok ch ch' ->
    access_mode t1 = By_value ch ->
    access_mode t2 = By_value ch' ->
    decode_encode_val v ch ch' v' ->
    (Pre ⊢ ((mapsto_ sh t1 p ∧ mapsto_ sh t2 p) ∗ (mapsto sh t2 p v' -∗ Post))) ->
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) ⊢
     ((tc_lvalue Delta e1) ∧ (tc_expr Delta (Ecast e2 t1))) ->
    semax E Delta
     (▷ PROPx P (LOCALx Q (SEPx R)))
     (Sassign e1 e2)
     (normal_ret_assert
        (PROPx P (LOCALx Q (SEPx (replace_nth n R Post))))).
Proof.
  intros * ? ? ? ? ? NT OK; intros.
  eapply semax_pre_simple; [| eapply semax_post'; [| apply semax_store_union_hack; subst; eauto]].
  + apply later_left2.
    apply bi.and_intro;  [subst; auto |].
    simpl lifted.
    rewrite (add_andp _ _ H0).
    rewrite (add_andp _ _ H1).
    erewrite SEP_nth_isolate, <- insert_SEP by eauto.
    rewrite !(bi.and_comm _ (local _)).
    rewrite -(andp_dup (local (`(eq p) (eval_lvalue e1)))) -bi.and_assoc.
    do 3 rewrite <- local_sepcon_assoc2.  rewrite <- local_sepcon_assoc1.
    eapply derives_trans.
    - apply bi.sep_mono; [| apply derives_refl].
      instantiate (1 := ((assert_of (`(mapsto_ sh (typeof e1)) (eval_lvalue e1))) ∧ 
                                 (assert_of (`(mapsto_ sh t2) (eval_lvalue e1)))) ∗ (assert_of `(bi_wand (mapsto sh t2 p v') Post))).
      unfold local, lift1; unfold_lift; raise_rho; simpl.
      subst t1.
      normalize.
    - rewrite -bi.sep_assoc.
      apply derives_refl.
  +
    rewrite (@bi.and_exist_l _ _).
    apply bi.exist_elim; intro v''.
    rewrite bi.and_assoc. rewrite (bi.and_comm (local _)).
    rewrite -bi.and_assoc.
    erewrite SEP_replace_nth_isolate with (Rn' := Post), <- insert_SEP by eauto.
    set (PQ := (PROPx P _)). clearbody PQ.
    change (`(force_val1 (sem_cast (typeof e2) t1)) (eval_expr e2))
    with (eval_expr (Ecast e2 t1)).
    Opaque eval_lvalue eval_expr.
    unfold local, lift1; unfold_lift; simpl.
    normalize.
    Transparent eval_lvalue eval_expr.
    subst t1.
    assert (v''=v'). eapply juicy_mem_lemmas.decode_encode_val_fun; eauto.
    subst v''.    
    rewrite bi.sep_assoc.
    apply bi.sep_mono; auto.
    apply modus_ponens_wand.
Qed.

