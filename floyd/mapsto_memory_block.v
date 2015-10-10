Require Import floyd.base.
Require Import floyd.assert_lemmas.
Require Import floyd.client_lemmas.
Require Import floyd.nested_pred_lemmas.

Local Open Scope logic.

(******************************************

Basic lemmas about local_facts, isptr, offset_zero

******************************************)

Lemma local_facts_isptr: forall P (p: val), P p |-- !! isptr p -> P p = !! (isptr p) && P p.
Proof.
  intros.
  apply pred_ext.
  + apply andp_right.
    exact H.
    cancel.
  + apply andp_left2.
    cancel.
Qed.

Lemma local_facts_offset_zero: forall P, (forall p, P p |-- !! isptr p) -> (forall p, P p = P (offset_val Int.zero p)).
Proof.
  intros.
  pose proof (H p).
  pose proof (H Vundef).
  destruct p; simpl in *; apply pred_ext; normalize.
  + eapply derives_trans. exact H0. normalize.
  + eapply derives_trans. exact H1. normalize.
  + eapply derives_trans. exact H0. normalize.
  + eapply derives_trans. exact H1. normalize.
  + eapply derives_trans. exact H0. normalize.
  + eapply derives_trans. exact H1. normalize.
  + eapply derives_trans. exact H0. normalize.
  + eapply derives_trans. exact H1. normalize.
Qed.

(******************************************

Lemmas about mapsto and mapsto_.

******************************************)

Lemma mapsto_local_facts:
  forall sh t v1 v2,  mapsto sh t v1 v2 |-- !! isptr v1.
  (* could make this slightly stronger by adding the fact
     (tc_val t v2 \/ v2=Vundef)  *)
Proof.
intros.
unfold mapsto.
destruct (access_mode t); try apply FF_left.
destruct (type_is_volatile t); try apply FF_left.
destruct v1; try apply FF_left.
apply prop_right; split; auto; apply Coq.Init.Logic.I.
Qed.

Lemma mapsto__local_facts:
  forall sh t v1, mapsto_ sh t v1 |-- !! isptr v1.
Proof. intros. apply mapsto_local_facts. Qed.
Hint Resolve mapsto_local_facts mapsto__local_facts : saturate_local.

Lemma mapsto_offset_zero:
  forall sh t v1 v2, mapsto sh t v1 v2 = mapsto sh t (offset_val Int.zero v1) v2.
Proof.
  intros.
  change (mapsto sh t (offset_val Int.zero v1) v2) with ((fun v0 => mapsto sh t v0 v2) (offset_val Int.zero v1)).
  rewrite <- local_facts_offset_zero.
  reflexivity.
  intros.
  eapply derives_trans; [  apply mapsto_local_facts | ].
  normalize.   
Qed.

Lemma mapsto__offset_zero:
  forall sh t v1, mapsto_ sh t v1 = mapsto_ sh t (offset_val Int.zero v1).
Proof.
  unfold mapsto_.
  intros.
  apply mapsto_offset_zero.
Qed.

Lemma mapsto_isptr: forall sh t v1 v2, mapsto sh t v1 v2 = !! (isptr v1) && mapsto sh t v1 v2.
Proof.
  intros.
  change (mapsto sh t v1 v2) with ((fun v1 => mapsto sh t v1 v2) v1).
  rewrite <- local_facts_isptr.
  reflexivity.
  eapply derives_trans; [apply mapsto_local_facts | normalize].
Qed.

Lemma mapsto__isptr: forall sh t v1, mapsto_ sh t v1 = !! (isptr v1) && mapsto_ sh t v1.
Proof.
  intros.
  apply pred_ext; normalize. apply andp_right; auto.
  eapply derives_trans; [apply mapsto__local_facts | normalize].
Qed.

(******************************************

Lemmas about memory_block

******************************************)

Lemma memory_block_zero_Vptr: forall sh b z, memory_block sh 0 (Vptr b z) = emp.
Proof.
  intros. unfold memory_block.
  change (nat_of_Z 0) with (0%nat).
  unfold memory_block'.
  pose proof Int.unsigned_range z.
  assert (Int.unsigned z <= Int.modulus) by omega.
  apply pred_ext; normalize.
Qed.
Hint Rewrite memory_block_zero_Vptr: norm.

Lemma memory_block_local_facts: forall sh n p, memory_block sh n p |-- !! (isptr p).
Proof.
  intros.
  destruct p; simpl; normalize.
Qed.
Hint Resolve memory_block_local_facts : saturate_local.

Lemma memory_block_offset_zero:
  forall sh n v, memory_block sh n v = memory_block sh n (offset_val Int.zero v).
Proof.
  intros.
  rewrite <- local_facts_offset_zero.
  reflexivity.
  apply memory_block_local_facts.
Qed.

Lemma memory_block_isptr: forall sh n p, memory_block sh n p = !!(isptr p) && memory_block sh n p.
Proof.
  intros.
  rewrite <- local_facts_isptr.
  reflexivity.
  apply memory_block_local_facts.
Qed.

Lemma memory_block_zero: forall sh p, memory_block sh 0 p = !! isptr p && emp.
Proof.
  intros.
  rewrite memory_block_isptr.
  destruct p;
  try rewrite memory_block_zero_Vptr;
  simpl;
  change (!!False) with FF;
  repeat rewrite FF_andp;
  auto.
Qed.

Lemma access_mode_by_value: forall t, type_is_by_value t = true -> exists ch, access_mode t = By_value ch.
Proof.
  intros.
  assert (forall ch', exists ch, By_value ch' = By_value ch).
    intros. exists ch'. reflexivity.
  destruct t; inversion H; simpl.
  - destruct i, s; apply H0.
  - apply H0.
  - destruct f; apply H0.
  - apply H0.
Qed.

Lemma repr_unsigned: forall i, Int.repr (Int.unsigned i) = i.
Proof.
  intros.
  apply Int.eqm_repr_eq.
  apply Int.eqm_refl.
Qed.

Lemma mapsto_by_value: forall sh t p v, mapsto sh t p v = !! (type_is_by_value t = true) && mapsto sh t p v.
Proof.
  intros.
  apply pred_ext; normalize.
  apply andp_right; [|cancel].
  unfold mapsto.
  destruct t; simpl; normalize; try (apply prop_right; auto).
Qed.

(******************************************

Lemmas of size_compatible and align_compatible

******************************************)

Section COMPSPECS.

Context {cs: compspecs}.

Lemma memory_block_mapsto_:
  forall sh t p, 
   type_is_by_value t = true ->
   type_is_volatile t = false ->
   legal_alignas_type t = true ->
   size_compatible t p ->
   align_compatible t p ->
   memory_block sh (sizeof cenv_cs t) p = mapsto_ sh t p.
Proof.
  intros.
  assert (isptr p \/ ~isptr p) by (destruct p; simpl; auto).
  destruct H4. destruct p; try contradiction.
    simpl in H2, H3.
    destruct (access_mode_by_value _ H) as [ch ?].
    apply legal_alignas_type_spec in H1.
    erewrite size_chunk_sizeof in H2 |- * by eauto.
    pose proof Z.divide_trans _ _ _ H1 H3.
    erewrite align_chunk_alignof in H6 by eauto.
    rewrite seplog.mapsto__memory_block with (ch := ch); auto.
  apply pred_ext; saturate_local; try contradiction.
Qed.

Lemma memory_block_size_compatible:
  forall sh t p,
  sizeof cenv_cs t < Int.modulus ->
  memory_block sh (sizeof cenv_cs t) p = 
  !! (size_compatible t p) && memory_block sh (sizeof cenv_cs t) p.
Proof.
  intros.
  unfold memory_block, size_compatible.
  apply pred_ext; destruct p; normalize.
Qed.

(*
Lemma mapsto_align_compatible:
  forall sh t p v, legal_alignas_type t = true ->
  mapsto sh t p v = !!( align_compatible t p) && mapsto sh t p v.
Proof.
  intros.
  unfold mapsto, align_compatible.
  destruct (access_mode t) eqn:?, (type_is_volatile t), p;
  apply pred_ext; normalize.
  unfold address_mapsto, res_predicates.address_mapsto.
  apply andp_right; [|cancel].
  erewrite align_chunk_alignof; [| eassumption | eapply legal_alignas_access_by_value; eauto].
  apply orp_left.
  + change (@predicates_hered.exp compcert_rmaps.RML.R.rmap
        compcert_rmaps.R.ag_rmap (list Memdata.memval)) with (@exp mpred _ (list Memdata.memval)).
    normalize.
    change (@predicates_hered.andp compcert_rmaps.RML.R.rmap
        compcert_rmaps.R.ag_rmap) with (@andp mpred _ ).
    change (@predicates_hered.prop compcert_rmaps.RML.R.rmap
        compcert_rmaps.R.ag_rmap) with (@prop mpred _ ).
    normalize.
  + change (@predicates_hered.exp compcert_rmaps.RML.R.rmap
        compcert_rmaps.R.ag_rmap (list Memdata.memval)) with (@exp mpred _ (list Memdata.memval)).
    normalize.
    change (@predicates_hered.andp compcert_rmaps.RML.R.rmap
        compcert_rmaps.R.ag_rmap) with (@andp mpred _ ).
    change (@predicates_hered.prop compcert_rmaps.RML.R.rmap
        compcert_rmaps.R.ag_rmap) with (@prop mpred _ ).
    normalize.
Qed.

Lemma mapsto_size_compatible_aux: forall t, type_is_by_value t = true -> legal_alignas_type t = true -> alignof cenv_cs t < Int.modulus.
Proof.
  unfold legal_alignas_type.
  intros. 
  destruct t; inversion H.
Transparent alignof.
  + destruct i, s; unfold alignof; simpl in *;
    rewrite nested_pred_ind in H0; simpl in H0; unfold align_attr;
    destruct (attr_alignas a); try inversion H0; try reflexivity.
  + destruct s; unfold alignof; simpl in *;
    rewrite nested_pred_ind in H0; simpl in H0; unfold align_attr;
    destruct (attr_alignas a); try inversion H0; try reflexivity.
  + destruct f; unfold alignof; simpl in *;
    rewrite nested_pred_ind in H0; simpl in H0; unfold align_attr;
    destruct (attr_alignas a); try inversion H0; try reflexivity.
  + unfold alignof; simpl in *;
    rewrite nested_pred_ind in H0; simpl in H0; unfold align_attr;
    destruct (attr_alignas a); try inversion H0; try reflexivity.
Opaque alignof.
Qed.

Lemma mapsto_size_compatible:
  forall sh t p v, legal_alignas_type t = true ->
  sizeof cenv_cs t = alignof cenv_cs t ->
  mapsto sh t p v = !!(size_compatible t p) && mapsto sh t p v.
Proof.
  intros.
  apply pred_ext; normalize.
  apply andp_right; [|cancel].
  rewrite mapsto_align_compatible by assumption.
  unfold size_compatible, align_compatible.
  pose proof alignof_pos cenv_cs t.
  rewrite mapsto_by_value.
  normalize; apply prop_right.
  destruct p; auto.
  destruct (alignof_two_p cenv_cs t).
  rewrite H0.
  pose proof mapsto_size_compatible_aux t H3 H.
  rewrite H4 in *.
  clear t H H0 H3 H4.
  pose proof Int.unsigned_range i.
  unfold Int.modulus in *.
  destruct H2 as [K ?].
  rewrite H0 in *; clear H0.
  rewrite !two_power_nat_two_p in *.
  pose proof Zle_0_nat x.
  pose proof Zle_0_nat Int.wordsize.
  forget (Z.of_nat x) as X.
  forget (Z.of_nat Int.wordsize) as Y.
  destruct (zle Y X).
  + pose proof two_p_monotone Y X (conj H2 l).
    omega.
  + replace Y with ((Y-X) + X) in H by omega.
    rewrite two_p_is_exp in H by omega.
    destruct H.
    apply Z.mul_lt_mono_pos_r in H3; [|omega].
    replace Y with ((Y-X) + X) by omega.
    rewrite two_p_is_exp by omega.
    rewrite Zmult_succ_l_reverse.
    apply Z.mul_le_mono_pos_r; omega.
Qed.
*)
Global Opaque memory_block.

End COMPSPECS.

(******************************************

Other lemmas

******************************************)

Lemma mapsto_tuint_tint:
  forall sh, mapsto sh tuint = mapsto sh tint.
Proof.
intros.
extensionality v1 v2.
reflexivity.
Qed.

Lemma mapsto_mapsto__int32:
  forall sh p v s1 s2,
  mapsto sh (Tint I32 s1 noattr) p v |-- mapsto_ sh (Tint I32 s2 noattr) p.
Proof.
intros.
eapply derives_trans; [ apply mapsto_mapsto_ | ].
destruct s1,s2; fold tuint; fold tint; 
  repeat rewrite mapsto_tuint_tint; auto.
Qed.


Lemma mapsto_mapsto_int32:
  forall sh p v s1 s2,
  mapsto sh (Tint I32 s1 noattr) p v |-- mapsto sh (Tint I32 s2 noattr) p v.
Proof.
intros.
destruct s1,s2; fold tuint; fold tint; 
  repeat rewrite mapsto_tuint_tint; auto.
Qed.


(* We do these as Hint Extern, instead of Hint Resolve,
  to limit their application and make them fail faster *)

Hint Extern 1 (mapsto _ _ _ _ |-- mapsto_ _ _ _) =>
    (apply mapsto_mapsto_) : cancel.

Hint Extern 1 (mapsto _ _ _ _ |-- mapsto_ _ _ _) =>
   (apply mapsto_mapsto__int32)  : cancel.

Hint Extern 1 (mapsto _ _ _ _ |-- mapsto _ _ _ _) =>
   (apply mapsto_mapsto_int32)  : cancel.

Lemma mapsto_null_mapsto_pointer:
  forall t sh v, 
             mapsto sh tint v nullval = 
             mapsto sh (tptr t) v nullval.
Proof.
intros.
unfold mapsto.
simpl.
destruct v; auto. f_equal; auto.
if_tac; [| auto].
f_equal. f_equal. f_equal.
apply prop_ext; split; intro; hnf in *|-*; auto.
Qed.

Lemma offset_val_force_ptr:
  offset_val Int.zero = force_ptr.
Proof. extensionality v. destruct v; try reflexivity.
simpl. rewrite Int.add_zero; auto.
Qed.

Hint Rewrite <- offset_val_force_ptr : norm.
Hint Extern 0 (legal_alignas_type _ = true) => reflexivity : cancel.

Lemma mapsto_force_ptr: forall sh t v v', 
  mapsto sh t (force_ptr v) v' = mapsto sh t v v'.
Proof.
intros.
destruct v; simpl; auto.
Qed.

Hint Rewrite mapsto_force_ptr: norm.

(***************************************

Auxilliary Lemmas

***************************************)

Lemma remove_PROP_LOCAL_left: forall P Q R S, R |-- S -> PROPx P (LOCALx Q R) |-- S.
Proof.
  intros.
  go_lower.
  normalize.
Qed.

Lemma remove_PROP_LOCAL_left': forall P Q R S, R |-- S -> PROPx P (LOCALx Q SEP (R)) |-- S.
Proof.
  intros.
  go_lower.
  normalize.
Qed.

Lemma SEP_nth_isolate:
  forall n R Rn, nth_error R n = Some Rn ->
      SEPx R = SEPx (Rn :: replace_nth n R emp).
Proof.
 unfold SEPx.
 induction n; destruct R; intros; inv H; extensionality rho.
 simpl; rewrite emp_sepcon; auto.
 unfold replace_nth; fold @replace_nth.
 transitivity (m rho * fold_right sepcon emp R rho).
 reflexivity.
 rewrite (IHn R Rn H1).
 simpl.
 rewrite <- sepcon_assoc.
 rewrite (sepcon_comm (Rn rho)).
 simpl.
 repeat rewrite sepcon_assoc.
 f_equal. rewrite sepcon_comm; reflexivity.
Qed.

Lemma nth_error_SEP_sepcon_TT: forall P Q R n Rn S,
  PROPx P (LOCALx Q (SEPx (Rn :: nil))) |-- S ->
  nth_error R n = Some Rn ->
  PROPx P (LOCALx Q (SEPx R)) |-- S * TT.
Proof.
  intros.
  erewrite SEP_nth_isolate by eauto.
  unfold PROPx, LOCALx, SEPx in *.
  unfold local, lift1 in H |- *.
  unfold_lift in H.
  unfold_lift.
  simpl in H |- *.
  intros rho.
  specialize (H rho).
  rewrite <- !andp_assoc in H |- *.
  rewrite <- !prop_and in H |- *.
  rewrite sepcon_emp in H.
  rewrite <- sepcon_andp_prop'.
  apply sepcon_derives.
  exact H.
  apply prop_right.
  auto.
Qed.

Lemma SEP_replace_nth_isolate:
  forall n R Rn Rn', 
       nth_error R n = Some Rn ->
      SEPx (replace_nth n R Rn') = SEPx (Rn' :: replace_nth n R emp).
Proof.
 unfold SEPx.
 intros.
 revert R H.
 induction n; destruct R; intros; inv H; intros; extensionality rho.
 simpl; rewrite emp_sepcon; auto.
 unfold replace_nth; fold @replace_nth.
 transitivity (m rho * fold_right sepcon emp (replace_nth n R Rn') rho).
 reflexivity.
 rewrite (IHn R H1). clear IHn.
 simpl.
 repeat rewrite <- sepcon_assoc.
 rewrite (sepcon_comm (Rn' rho)).
 rewrite sepcon_assoc.
 reflexivity.
Qed.

Lemma local_andp_lemma:
  forall P Q, P |-- local Q -> P = local Q && P.
Proof.
intros.
apply pred_ext.
apply andp_right; auto.
apply andp_left2; auto.
Qed.

Lemma SEP_TT_right:
  forall R, R |-- SEP(TT).
Proof. intros. go_lowerx. rewrite sepcon_emp. apply TT_right.
Qed.

Lemma replace_nth_SEP: forall P Q R n Rn Rn', Rn |-- Rn' -> PROPx P (LOCALx Q (SEPx (replace_nth n R Rn))) |-- PROPx P (LOCALx Q (SEPx (replace_nth n R Rn'))).
Proof.
  simpl.
  intros.
  specialize (H x).
  normalize.
      autorewrite with subst norm1 norm2; normalize.
  revert R.
  induction n.
  + destruct R.
    - simpl. cancel.
    - simpl. cancel.
  + destruct R.
    - simpl. cancel.
    - intros. simpl in *. cancel.
Qed.

Lemma replace_nth_SEP': forall P Q R n Rn Rn', PROPx P (LOCALx Q (SEP (Rn))) |-- Rn' -> (PROPx P (LOCALx Q (SEPx (replace_nth n R Rn)))) |-- (PROPx P (LOCALx Q (SEPx (replace_nth n R Rn')))).
Proof.
  simpl.
  intros.
  specialize (H x).
  normalize. 
      autorewrite with subst norm1 norm2; normalize.
    autorewrite with subst norm1 norm2 in H; normalize in H.
  revert R.
  induction n.
  + destruct R.
    - simpl. cancel.
    - simpl. cancel.
  + destruct R.
    - simpl. cancel.
    - intros. simpl in *. cancel.
Qed.

Lemma replace_nth_SEP_andp_local': forall P Q R n Rn (Rn': environ -> mpred) Rn'' x,
  nth_error R n = Some Rn ->
  (PROPx P (LOCALx Q (SEPx (replace_nth n R ((`prop Rn'') && Rn'))))) x
  = (PROPx P (LOCALx (Rn'' :: Q) (SEPx (replace_nth n R Rn')))) x.
Proof.
  intros.
  normalize.
      autorewrite with subst norm1 norm2; normalize.
  assert ((@fold_right (environ -> mpred) (environ -> mpred)
              (@sepcon (environ -> mpred) (@LiftNatDed' mpred Nveric)
                 (@LiftSepLog' mpred Nveric Sveric))
              (@emp (environ -> mpred) (@LiftNatDed' mpred Nveric)
                 (@LiftSepLog' mpred Nveric Sveric))
              (@replace_nth (lifted (LiftEnviron mpred)) n R
                 (@andp (lifted (LiftEnviron mpred))
                    (@LiftNatDed' mpred Nveric)
                    (@liftx (Tarrow Prop (LiftEnviron mpred))
                       (@prop (lift_T (LiftEnviron mpred)) Nveric) Rn'') Rn'))
              x) =
   (@andp mpred Nveric
           (@prop mpred Nveric
              (Rn'' x))
           (@fold_right (environ -> mpred) (environ -> mpred)
              (@sepcon (environ -> mpred) (@LiftNatDed' mpred Nveric)
                 (@LiftSepLog' mpred Nveric Sveric))
              (@emp (environ -> mpred) (@LiftNatDed' mpred Nveric)
                 (@LiftSepLog' mpred Nveric Sveric))
              (@replace_nth (lifted (LiftEnviron mpred)) n R Rn') x))); 
  [| rewrite H0; apply pred_ext; normalize].

  revert R H.
  induction n; intros.
  + destruct R; inversion H.
    subst l.
    simpl. normalize.
      autorewrite with subst norm1 norm2; normalize.
  + destruct R; inversion H.
    pose proof IHn R H1.
    unfold replace_nth in *.
    fold (@replace_nth (LiftEnviron mpred)) in *.
    simpl fold_right in *.
    rewrite <- sepcon_andp_prop, H0.
    reflexivity.
Qed.

Lemma replace_nth_SEP_andp_local: forall P Q R n Rn (Rn': environ -> mpred) Rn'',
  nth_error R n = Some Rn ->
  (PROPx P (LOCALx Q (SEPx (replace_nth n R ((`prop Rn'') && Rn')))))
  = (PROPx P (LOCALx (Rn'' :: Q) (SEPx (replace_nth n R Rn')))).
Proof.
  intros.
  extensionality.
  eapply replace_nth_SEP_andp_local'.
  exact H.
Qed.

Lemma LOCAL_2_hd: forall P Q R Q1 Q2,
  (PROPx P (LOCALx (Q1 :: Q2 :: Q) (SEPx R))) = 
  (PROPx P (LOCALx (Q2 :: Q1 :: Q) (SEPx R))).
Proof.
  intros.
  extensionality.
  apply pred_ext; normalize;
      autorewrite with subst norm1 norm2; normalize.
Qed.

Lemma eq_sym_LOCAL: forall P Q R id v, 
  PROPx P (LOCALx (`eq v (eval_id id) :: Q) (SEPx R)) = 
  PROPx P (LOCALx (`eq (eval_id id) v:: Q) (SEPx R)).
Proof.
  intros.
  extensionality; apply pred_ext; normalize;
      autorewrite with subst norm1 norm2; 
      normalize;
      autorewrite with subst norm1 norm2; 
      normalize.
Qed.

Lemma eq_sym_LOCAL': forall P Q R id v, 
  PROPx P (LOCALx (`(eq v) (eval_id id) :: Q) (SEPx R)) = 
  PROPx P (LOCALx (`eq (eval_id id) `v:: Q) (SEPx R)).
Proof.
  intros.
  normalize.
Qed.

(* This lemma is for load_37 *)
Lemma eq_sym_post_LOCAL: forall P Q R id v,
  (EX  old : val, PROPx P
  (LOCALx (`eq (subst id `old v) (eval_id id)::map (subst id `old) Q) (SEPx (map (subst id `old) R)))) = 
  (EX  old : val, PROPx P
  (LOCALx (`eq (eval_id id) (subst id `old v)::map (subst id `old) Q) (SEPx (map (subst id `old) R)))).
Proof.
  intros.
  apply pred_ext; normalize; apply (exp_right old);
  rewrite eq_sym_LOCAL; apply derives_refl.
Qed.

(* This lemma is for load_37' *)
Lemma eq_sym_post_LOCAL': forall P Q R id v,
  (EX  old : val, PROPx P
  (LOCALx (`(eq v) (eval_id id) :: map (subst id `old) Q) (SEPx (map (subst id `old) R)))) = 
  (EX  old : val, PROPx P
  (LOCALx (`eq (eval_id id) `v ::  map (subst id `old) Q) (SEPx (map (subst id `old) R)))).
Proof.
  intros.
  apply pred_ext; normalize; apply (exp_right old);
  rewrite eq_sym_LOCAL'; apply derives_refl.
Qed.

(******************************************

Definition of at_offset.

at_offset is the elementary definition. All useful lemmas about at_offset will be proved here. 

******************************************)

Definition at_offset (P: val -> mpred) (z: Z): val -> mpred :=
 fun v => P (offset_val (Int.repr z) v).

Arguments at_offset P z v : simpl never.

Lemma at_offset_eq: forall P z v,
  at_offset P z v = P (offset_val (Int.repr z) v).
Proof.
intros; auto.
Qed.

Lemma lifted_at_offset_eq: forall (P: val -> mpred) z v,
  `(at_offset P z) v = `P (`(offset_val (Int.repr z)) v).
Proof.
  intros.
  unfold liftx, lift in *. simpl in *.
  extensionality p.
  apply at_offset_eq.
Qed.

Lemma at_offset_eq2: forall pos pos' P, 
  forall p, at_offset P (pos + pos') p = at_offset P pos' (offset_val (Int.repr pos) p).
Proof.
  intros.
  rewrite at_offset_eq.
  rewrite at_offset_eq. 
  unfold offset_val.
  destruct p; auto.
  rewrite int_add_assoc1.
  reflexivity.
Qed.

Lemma at_offset_eq3: forall P z b ofs,
  at_offset P z (Vptr b (Int.repr ofs)) = P (Vptr b (Int.repr (ofs + z))).
Proof.
  intros.
  rewrite at_offset_eq.
  unfold offset_val.
  solve_mod_modulus.
  reflexivity.
Qed.

Lemma at_offset_derives: forall P Q p , (forall p, P p |-- Q p) -> forall pos, at_offset P pos p |-- at_offset Q pos p.
Proof.
  intros.
  rewrite !at_offset_eq.
  apply H.
Qed.

(******************************************

Definitions of spacer and withspacer

Comment: spacer only has offset_zero property but does not have local_facts
and isptr property.

******************************************)

Definition spacer (sh: share) (be: Z) (ed: Z) : val -> mpred :=
  if Z.eq_dec (ed - be) 0
  then fun _ => emp
  else
    at_offset (memory_block sh (ed - be)) be.
(* Arguments spacer sh be ed / _ . *)

Definition withspacer sh (be: Z) (ed: Z) P (p: val): mpred :=
   if Z.eq_dec (ed - be) 0
   then P p
   else P p * spacer sh be ed p.

Lemma withspacer_spacer: forall sh be ed P p,
   withspacer sh be ed P p = spacer sh be ed p * P p.
Proof.
  intros.
  unfold withspacer, spacer.
  if_tac.
  + normalize.
  + simpl; apply sepcon_comm.
Qed.

Lemma spacer_offset_zero:
  forall sh be ed v, spacer sh be ed v = spacer sh be ed (offset_val Int.zero v).
Proof.
  intros;
  unfold spacer.
  destruct (Z.eq_dec (ed - be) 0);  auto.
  repeat rewrite at_offset_eq;
  try rewrite offset_offset_val; try  rewrite Int.add_zero_l; auto.
Qed.

Lemma withspacer_add:
  forall sh pos be ed P p,
  withspacer sh (pos + be) (pos + ed) (fun p0 => P (offset_val (Int.repr pos) p)) p = 
  withspacer sh be ed P (offset_val (Int.repr pos) p).
Proof.
  intros.
  rewrite !withspacer_spacer.
  unfold spacer.
  simpl.
  replace (pos + ed - (pos + be)) with (ed - be) by omega.
  if_tac; [reflexivity|].
  rewrite !at_offset_eq.
  replace (offset_val (Int.repr (pos + be)) p) with
          (offset_val (Int.repr be) (offset_val (Int.repr pos) p)).
  reflexivity.
  destruct p; simpl; try reflexivity.
  rewrite int_add_assoc1.
  reflexivity.
Qed.

Lemma offset_val_preserve_isptr: forall p pos, !! (isptr (offset_val pos p)) |-- !! (isptr p).
Proof.
  intros.
  destruct p; simpl; apply derives_refl.
Qed.

Lemma at_offset_preserve_local_facts: forall P pos, (forall p, P p |-- !!(isptr p)) -> (forall p, at_offset P pos p |-- !!(isptr p)).
Proof.
  intros.
  rewrite at_offset_eq.
  specialize (H (offset_val (Int.repr pos) p)).
  eapply derives_trans; [exact H |]. 
  apply offset_val_preserve_isptr.
Qed.

Lemma withspacer_preserve_local_facts: forall sh be ed P, (forall p, P p |-- !! (isptr p)) -> (forall p, withspacer sh be ed P p |-- !! (isptr p)).
Proof.
  intros.
  rewrite withspacer_spacer.
  simpl; rewrite sepcon_comm. 
  apply (derives_left_sepcon_right_corable (!!isptr p) (P p) _); [apply corable_prop|].
  apply H.
Qed.

Transparent memory_block.

Lemma spacer_memory_block:
  forall sh be ed v, isptr v -> 
 spacer sh be ed v = memory_block sh (ed - be) (offset_val (Int.repr be) v).
Proof.
  intros.
  destruct v; inv H.
  unfold spacer.
  destruct (Z.eq_dec (ed - be) 0);
  try solve [rewrite e; simpl offset_val; rewrite memory_block_zero_Vptr; auto].
  rewrite at_offset_eq.
  destruct be; auto.
Qed.

Hint Rewrite at_offset_eq3 : at_offset_db.
Hint Rewrite withspacer_spacer : at_offset_db.
Hint Rewrite spacer_memory_block using (simpl; auto): at_offset_db.

Opaque memory_block.

