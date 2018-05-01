(* Additional lemmas / proof rules about VST stack *)

Require Import VST.floyd.proofauto.
Require Export sha.general_lemmas.
Require Import sha.common_lemmas.
Local Open Scope logic.

Lemma force_lengthn_long {A}: forall n (l:list A) d, (n <= length l)%nat -> force_lengthn n l d = firstn n l.
Proof. induction n; simpl; intros. trivial.
  destruct l; simpl in H. omega.
  rewrite IHn; trivial. omega.
Qed.

Lemma data_at_triv {cs} sh t v v': v=v' -> @data_at cs sh t v |-- @data_at cs sh t v'.
Proof. intros; subst. auto. Qed.

Lemma sizeof_Tarray {cs: composite_env} k: Z.max 0 k = k -> sizeof (Tarray tuchar k noattr) = k.
Proof. intros K; simpl; rewrite K. destruct k; trivial. Qed.

(*Require Import replace_refill_reptype_lemmas.*)
(*
Lemma data_at_Tarray_split3a {cs}: forall sh t n a i v,
  0 <= i <= n ->
  @data_at cs sh (Tarray t n a) v =
  @data_at cs sh (Tarray t n a) (upd_Znth i v (Znth i v (default_val _))) v.
    @data_at cs sh (Tarray t n a) (force_lengthn (nat_of_Z i) v (default_val _) ++
      (Znth i v (default_val _)) :: skipn (nat_of_Z (i + 1)) v).
Proof.
  intros.
  apply data_at_Tarray_ext.
  intros j ?H.
  unfold Znth.
  if_tac; [omega |].
  if_tac; [omega |].
  unfold nat_of_Z.
  destruct (Z_dec i j) as [[? | ?] | ?].
  + assert ((Z.to_nat i < Z.to_nat j)%nat) by (apply Z2Nat.inj_lt in l; omega).
    rewrite app_nth2 by (rewrite force_lengthn_length_n; omega).
    rewrite force_lengthn_length_n.
    simpl.
    destruct ((Z.to_nat j - Z.to_nat i)%nat) eqn:?H; [omega |].
    rewrite nth_skipn.
    f_equal.
    f_equal.
    change (i + 1) with (Z.succ i).
    rewrite Z2Nat.inj_succ by omega.
    omega.
  + assert ((Z.to_nat j < Z.to_nat i)%nat) by (apply Z2Nat.inj_lt; omega).
    rewrite app_nth1 by (rewrite force_lengthn_length_n; omega).
    rewrite nth_force_lengthn by omega.
    reflexivity.
  + subst.
    rewrite app_nth2 by (rewrite force_lengthn_length_n; omega).
    rewrite force_lengthn_length_n.
    rewrite minus_diag.
    simpl.
    reflexivity.
Qed.
*)
Lemma skipn_force_lengthn_app {A} n (l m:list A) a:
        skipn n (force_lengthn n l a ++ m) = m.
  intros. rewrite skipn_app1.
  specialize (skipn_exact_length (force_lengthn n l a)).
           rewrite force_lengthn_length_n. intros X; rewrite X; trivial.
  rewrite force_lengthn_length_n; omega.
Qed.

Lemma sepcon_fold: forall Frame P rho,
Frame = cons `(P) nil ->
P |-- fold_right
      (fun (P Q : environ -> mpred) (rho0 : environ) => P rho0 * Q rho0)
      `(emp) Frame rho.
Proof. intros. subst. simpl. entailer. Qed.

Lemma nth_mapVint: forall i (l:list Z) (Hi: (0 <= i < length l)%nat),
  exists n, nth i (map Vint (map Int.repr l)) Vundef = Vint n.
Proof. intros i.
  induction i; simpl; intros.
    destruct l; simpl in *. omega. eexists; reflexivity.
    destruct l; simpl in *. omega.
      destruct (IHi l). omega. rewrite H. eexists; reflexivity.
Qed.

Lemma nth_mapVint' {z}: forall i (l:list Z)
  (Hi: (0 <= i < length l)%nat),
  nth i (map Vint (map Int.repr l)) Vundef =
  Vint (Int.repr (nth i l z)).
Proof. intros i.
  induction i; simpl; intros.
    destruct l; simpl in *. omega. trivial.
    destruct l; simpl in *. omega.
      rewrite (IHi l). trivial. omega.
Qed.

Lemma nth_mapVintZ: forall i (l:list Z) (Hi: 0 <= i < Zlength l),
  exists n, nth (Z.to_nat i) (map Vint (map Int.repr l)) Vundef = Vint n.
Proof. intros.
  eapply nth_mapVint. rewrite Zlength_correct in Hi.
  destruct Hi; split.   omega.
unfold Z.of_nat in H0. unfold Z.to_nat.
destruct l; simpl in *. omega.
destruct i; try omega.
rewrite <- SuccNat2Pos.id_succ.
apply Pos2Nat.inj_lt.
apply H0.
Qed.

(*Same proof as semax_loadstore_array*)(*
Lemma NEWsemax_loadstore_array:
  forall {Espec: OracleKind},
 forall n k vi lo hi t1 (contents: Z -> reptype t1) v1 v2 (Delta: tycontext) e1 ei e2 sh P Q R,
  (*H0*) reptype t1 = val ->
  (*H1*) type_is_by_value t1 ->
  (*H2*) legal_alignas_type t1 = true ->
  (*H3*) typeof e1 = tarray t1 k->
  (*H4*) typeof ei = tint ->
  (*H8*) PROPx P (LOCALx Q (SEPx R)) |--  rel_expr e1 v1 && rel_expr ei (Vint (Int.repr vi))
           && rel_expr (Ecast e2 t1) v2 ->
  (*H7*) nth_error R n = Some (`(array_at t1 sh contents lo hi v1)) ->
  (*H *) writable_share sh ->
  (*H5*) tc_val t1 v2 ->
  (*H6*) in_range lo hi vi ->
   @semax Espec Delta (|> PROPx P (LOCALx Q (SEPx R))) (Sassign (Ederef (Ebinop Oadd e1 ei (tptr t1)) t1) e2)
          (normal_ret_assert
           (PROPx P (LOCALx Q (SEPx
            (replace_nth n R `(array_at t1 sh (upd contents vi (valinject _ v2)) lo hi v1)))))).
Proof.
intros until R.
intros H0 H1 H2 H3 H4 H8 H7 H H5 H6.
eapply semax_post_flipped'.
apply semax_loadstore_array'; eauto.
apply derives_trans with (!! isptr v1 && PROPx P (LOCALx Q (SEPx R))).
rewrite (SEP_nth_isolate _ _ _ H7).
repeat rewrite <- insert_SEP.
rewrite array_at_isptr. normalize.
normalize.
destruct v1; try contradiction.
instantiate (2:=v1).
simpl eval_binop. rewrite mul_repr.
apply andp_right; auto.
eapply derives_trans; [ apply H8 |].
intro rho. simpl.
repeat apply andp_right.
apply rel_lvalue_deref.
eapply rel_expr_binop.
repeat apply andp_left1. apply derives_refl.
apply andp_left1. apply andp_left2. apply derives_refl.
intro; rewrite H4; simpl. rewrite H3; simpl.
  unfold Cop.sem_add; simpl. rewrite mul_repr. auto.
 apply andp_left2. auto.
rewrite (SEP_nth_isolate _ _ _ H7).
repeat rewrite <- insert_SEP.
apply derives_refl.
rewrite (SEP_replace_nth_isolate _ _ _ `(array_at t1 sh (upd contents vi (valinject t1 v2)) lo hi v1) H7).
rewrite insert_SEP.
auto.
Qed.*)
(*
Lemma array_at_local_facts':
  forall (t : type) (sh : Share.t) (f : Z -> reptype t) (lo hi : Z) (v : val),
  array_at t sh f lo hi v |-- array_at t sh f lo hi v && !!isptr v && !!offset_in_range (sizeof t * lo) v &&
!!offset_in_range (sizeof t * hi) v && !!align_compatible t v.
Proof. intros. unfold array_at. entailer. Qed.
*)
(*
Lemma split_offset_array_at_: forall (ty : type) (sh : Share.t)
         (z lo hi : Z) (v : val),
       z <= lo <= hi ->
       sizeof ty > 0 ->
       legal_alignas_type ty = true ->
       array_at_ ty sh z hi v =
       !! offset_in_range (sizeof ty * z) v &&
       !! offset_in_range (sizeof ty * hi) v &&
       array_at_ ty sh z lo v *
       array_at_ ty sh 0 (hi - lo)
       (offset_val (Int.repr (sizeof ty * lo)) v).
Proof.
  intros. unfold array_at_.
  rewrite <- split_offset_array_at; trivial.
Qed.
*)
(*
Lemma offset_val_array_at0:
 forall t sh f lo hi v,
  sizeof t > 0 -> hi >= 0 ->
  legal_alignas_type t = true ->
  array_at t sh (fun i => f (i-lo)%Z) lo (lo + hi) v
  |--
  array_at t sh f 0 hi (offset_val (Int.repr (sizeof t * lo)) v).
Proof.
  intros.
  rewrite (split_offset_array_at t _ _ lo lo); trivial.
  rewrite array_at_emp.
  entailer. rewrite Zplus_comm. rewrite Z.add_simpl_r.
  apply array_lemmas.array_at_ext'. intros. rewrite Z.add_simpl_r. trivial.
  omega.
Qed.

Lemma offset_val_array_at1:
 forall t sh f g k lo hi ofs v,
    sizeof t > 0 -> hi >= 0 ->
    legal_alignas_type t = true ->
    k = lo + hi ->
    g = (fun i => f (i-lo)%Z) ->
    ofs = Int.repr (sizeof t * lo) ->
  array_at t sh g lo k v |--
  array_at t sh f 0 hi ((offset_val ofs) v).
Proof.
  intros. subst. apply offset_val_array_at0; trivial.
Qed.
*)
(*
Lemma split_memory_block p hi v sh:
      0 <= p <= hi -> isptr v ->
      memory_block sh (Int.repr hi) v =
      !!offset_in_range (sizeof tuchar * 0) v &&
      !!offset_in_range (sizeof tuchar * hi) v &&
      memory_block sh (Int.repr p) v * memory_block sh (Int.repr (hi-p)) (offset_val (Int.repr p) v).
Proof. intros.
rewrite memory_block_array_tuchar'; try omega; trivial.
rewrite memory_block_array_tuchar'; try omega; trivial.
rewrite memory_block_array_tuchar'; try omega.
rewrite (split_offset_array_at_ _ _ _ p).
   assert (K: (sizeof tuchar * p = p)%Z).
      assert (sizeof tuchar =1 ). reflexivity.
  rewrite H1. omega.
  rewrite K; trivial.
 assumption. simpl; omega. reflexivity. apply isptr_offset_val'; trivial.
Qed.
*)
Lemma isptrD v: isptr v -> exists b ofs, v = Vptr b ofs.
Proof. intros. destruct v; try contradiction. exists b, i; trivial. Qed.

(*
Lemma mysemax_frame_PQR:
  forall R2 Espec Delta R1 P Q P' Q' R1' c,
     closed_wrt_modvars c (LOCALx nil (SEPx R2)) ->
     @semax Espec Delta (PROPx P (LOCALx Q (SEPx R1))) c
                     (normal_ret_assert (PROPx P' (LOCALx Q' (SEPx R1')))) ->
     @semax Espec Delta (PROPx P (LOCALx (Q) (SEPx (R1++R2)))) c
                     (normal_ret_assert (PROPx P' (LOCALx (Q') (SEPx (R1'++R2))))).
Proof.
intros. specialize (semax_frame_PQR nil R2 Espec Delta R1 P Q P' Q' R1' c).
repeat rewrite app_nil_r. intros. apply H1; trivial. Qed.

Ltac frame_SEP'' L :=
 grab_indexes_SEP L;
 match goal with
 | |- @semax _ _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
  rewrite <- (firstn_skipn (length L) R);
    simpl length; unfold firstn, skipn;
    eapply (mysemax_frame_PQR);
      [ unfold closed_wrt_modvars;  auto 50 with closed
     | ]
 | |- (PROPx _ (LOCALx _ (SEPx ?R))) |-- _ =>
  rewrite <- (firstn_skipn (length L) R);
    simpl length; unfold firstn, skipn;
    apply derives_frame_PQR
end.
*)

Ltac myframe_SEP'' L :=  (* this should be generalized to permit framing on LOCAL part too *)
 grab_indexes_SEP L;
 match goal with
 | |- @semax _ _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ =>
  rewrite <- (firstn_skipn (length L) R);
  rewrite <- (firstn_skipn (length Q) Q);
    simpl length; unfold firstn, skipn;
    eapply (semax_frame_PQR nil);
      [ unfold closed_wrt_modvars;  auto 50 with closed
     | ]
 | |- (PROPx _ (LOCALx _ (SEPx ?R))) |-- _ =>
  rewrite <- (firstn_skipn (length L) R);
    simpl length; unfold firstn, skipn;
    apply derives_frame_PQR
end.
