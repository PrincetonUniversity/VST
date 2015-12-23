Require Import floyd.proofauto.
Local Open Scope logic.
Require Import Coq.Lists.List. Import ListNotations.
Require Import general_lemmas.

Require Import split_array_lemmas.
Require Import ZArith. 
Require Import tweetNaclBase.
Require Import Salsa20.
Require Import verif_salsa_base.
Require Import tweetnaclVerifiableC.
Require Import Snuffle. 
Require Import spec_salsa. Opaque Snuffle.Snuffle.

Ltac my_store_tac := 
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
    let v := fresh "v" in evar (v: reptype (nested_field_type t_root gfs0));
    let n := fresh "n" in
    let H := fresh "H" in
    sc_new_instantiate P Q R R Delta e1 gfs tts lr p sh t_root gfs0 v n (0%nat) H;

    try (unify v (default_val (nested_field_type t_root gfs0));
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
    subst gfs;

    eapply (semax_SC_field_store Delta sh n p)
      with (lr0 := lr) (t_root0 := t_root) (gfs2 := gfs0) (gfs3 := gfs1);
    subst p;
      [ reflexivity | reflexivity | reflexivity
      | reflexivity | reflexivity | reflexivity | reflexivity
      | reflexivity | exact HLE 
      | exact HRE | exact H_Denote | solve [auto]
      | solve_store_rule_evaluation
      | subst e1 gfs0 gfs1 efs tts t_root sh v0 lr n;
        pre_entailer;
        try quick_typecheck3; 
        clear HLE HRE H_Denote H;
        unfold tc_efield; try solve[entailer!]; 
        simpl app; simpl typeof
      | subst e1 gfs0 gfs1 efs tts t_root sh v0 lr n;
        clear HLE HRE H_Denote H(*;
        solve_legal_nested_field_in_entailment*)
     ]
end.

Lemma Int64_sub_sub a b c: 
      Int64.min_signed <= - c <= Int64.max_signed ->
      Int64.min_signed <= - b <= Int64.max_signed ->
      (*0 <= - c <= Int64.max_unsigned -> 0 <= - b <= Int64.max_unsigned->*)
      Int64.sub a (Int64.repr (b + c)) =
      Int64.sub (Int64.sub a (Int64.repr b)) (Int64.repr c).
Proof. intros.
  rewrite Int64.sub_add_opp.
  rewrite Int64.sub_add_opp.
  rewrite Int64.sub_add_opp. rewrite Int64.add_assoc. f_equal.
  rewrite Int64.neg_repr.
  rewrite Int64.neg_repr.
  rewrite Int64.neg_repr.
  rewrite Int64.add_signed.
  rewrite Int64.signed_repr; trivial.
  rewrite Int64.signed_repr; trivial. f_equal. omega.
Qed.

Lemma sublist_hi_plus {A} (l:list A) lo a b: 0<=lo<=a -> 0<=b -> sublist lo (a + b) l =
   sublist lo a l ++ sublist a (a+b) l.
Proof. intros.
  unfold sublist.
  assert (X: a+b -lo = a-lo + b) by omega. rewrite X; clear X.
  rewrite Z2Nat.inj_add, <- firstn_app; try omega. f_equal.
  assert (Y: a + b - a = b) by omega. rewrite Y; clear Y.
  rewrite skipn_skipn, Z2Nat.inj_sub; try omega.
  f_equal. f_equal. rewrite <- le_plus_minus; trivial.
  apply Z2Nat.inj_le; omega.
Qed.

Lemma sublist0_hi_plus {A} (l:list A) a b: 0<=a -> 0<=b -> sublist 0 (a + b) l =
   sublist 0 a l ++ sublist a (a+b) l.
Proof. intros.
  apply sublist_hi_plus; omega.
Qed.

Lemma byte_unsigned_range_3 b: 0 <= Byte.unsigned b <= Int.max_unsigned.
Proof.
  destruct (Byte.unsigned_range_2 b). unfold Byte.max_unsigned in H0; simpl in H0.
  rewrite int_max_unsigned_eq; omega.
Qed.

Lemma Int_unsigned_repr_byte b: Int.unsigned (Int.repr (Byte.unsigned b)) = Byte.unsigned b.
Proof. rewrite Int.unsigned_repr. trivial.
  apply byte_unsigned_range_3 .
Qed. 

Lemma zero_ext8_byte b: Int.zero_ext 8 (Int.repr (Byte.unsigned b)) = Int.repr (Byte.unsigned b).
  apply zero_ext_inrange.
  rewrite Int.unsigned_repr. apply Byte.unsigned_range_2.
  apply byte_unsigned_range_3. 
Qed.

Lemma Zlxor_range_byte b1 b2: 0<= Z.lxor (Byte.unsigned b1) (Byte.unsigned b2) <= Byte.max_unsigned.
Proof.
  destruct (Byte.unsigned_range_2 b1).
  destruct (Byte.unsigned_range_2 b2).
  split. apply Z.lxor_nonneg. omega. 
  apply Byte.Ztestbit_le. omega. clear.
  intros i I H. rewrite Z.lxor_spec in H.
  destruct (zlt i 8).
  + clear - I l.  
    destruct (zeq i 0); subst. reflexivity.
    destruct (zeq i 1); subst. reflexivity.
    destruct (zeq i 2); subst. reflexivity.
    destruct (zeq i 3); subst. reflexivity.
    destruct (zeq i 4); subst. reflexivity.
    destruct (zeq i 5); subst. reflexivity.
    destruct (zeq i 6); subst. reflexivity.
    destruct (zeq i 7); subst. reflexivity. omega. 
  + rewrite (isbyteZ_testbit _ i) in H; trivial. 2: apply Byte.unsigned_range.
    rewrite (isbyteZ_testbit _ i) in H; trivial. 2: apply Byte.unsigned_range.
    inv H.
Qed.

Lemma Znth_sublist':
  forall (A : Type) (lo i hi : Z) (al : list A) (d : A),
  0 <= lo ->
  Zlength al <= hi ->
  0 <= i <= hi - lo -> Znth i (sublist lo hi al) d = Znth (i + lo) al d.
Proof. intros. unfold Znth. destruct (zlt i 0). omega.
destruct (zlt (i + lo) 0). omega. unfold sublist.
destruct (zeq i (hi-lo)).
Focus 2. rewrite nth_firstn. 2: apply Z2Nat.inj_lt; try omega. rewrite nth_skipn, Z2Nat.inj_add; trivial. omega.
rewrite <- e. rewrite nth_overflow. Focus 2. rewrite firstn_length, skipn_length. apply Min.le_min_l.
rewrite nth_overflow; trivial. subst i.
assert(hi - lo + lo= hi). omega. rewrite H2.
apply Z2Nat.inj_le in H0; try omega. rewrite ZtoNat_Zlength in H0. apply H0.
apply Zlength_nonneg.
Qed.

Lemma xor_byte_int b1 b2: Int.xor (Int.repr (Byte.unsigned b1)) (Int.repr (Byte.unsigned b2)) =
      Int.repr (Byte.unsigned (Byte.xor b1 b2)).
Proof.
unfold Byte.xor, Int.xor.
  rewrite Byte.unsigned_repr. 
  rewrite Int.unsigned_repr.
  rewrite Int.unsigned_repr; trivial.
  apply byte_unsigned_range_3.
  apply byte_unsigned_range_3.
  apply Zlxor_range_byte.
Qed.

Lemma Zlength_combinelist {A} f xs ys l:
      combinelist A f xs ys = Some l -> Zlength l = Zlength ys.
Proof. intros H; symmetry in H.
  apply combinelist_length in H. rewrite Zlength_correct, H. rewrite Zlength_correct; reflexivity.
Qed. 

Lemma Tarray_0_emp sh v c: data_at sh (Tarray tuchar 0 noattr) v c |--  emp.
  unfold data_at. unfold field_at, data_at', at_offset; simpl.
  unfold array_pred, unfold_reptype, aggregate_pred.array_pred. entailer.
Qed. 
Lemma Tarray_0_emp' sh c: field_compatible (Tarray tuchar 0 noattr) nil c ->
  emp |-- data_at sh (Tarray tuchar 0 noattr) nil c.
Proof. intros.
  unfold data_at. unfold field_at, data_at', at_offset; simpl.
  unfold array_pred, unfold_reptype, aggregate_pred.array_pred. simpl.
  entailer.
Qed. 
Lemma Tarray_0_emp_iff sh c: field_compatible (Tarray tuchar 0 noattr) [] c ->
  data_at sh (Tarray tuchar 0 noattr) nil c = emp.
Proof. intros. apply pred_ext. apply Tarray_0_emp. apply Tarray_0_emp'; trivial.
Qed.

Lemma Tarray_0_emp_ sh c: data_at_ sh (Tarray tuchar 0 noattr) c |--  emp.
  unfold data_at_. unfold field_at_, field_at, data_at', at_offset; simpl.
  unfold array_pred, unfold_reptype, aggregate_pred.array_pred. entailer.
Qed. 
Lemma Tarray_0_emp'_ sh c: field_compatible (Tarray tuchar 0 noattr) nil c ->
  emp |-- data_at_ sh (Tarray tuchar 0 noattr) c.
Proof. intros.
  unfold data_at_, field_at_, field_at, data_at', at_offset; simpl.
  unfold array_pred, unfold_reptype, aggregate_pred.array_pred. simpl.
  entailer.
Qed. 
Lemma Tarray_0_emp_iff_ sh c: field_compatible (Tarray tuchar 0 noattr) [] c ->
  data_at_ sh (Tarray tuchar 0 noattr) c = emp.
Proof. intros. apply pred_ext. apply Tarray_0_emp_. apply Tarray_0_emp'_; trivial.
Qed.

Definition bxorlist := combinelist _ Byte.xor. 
Definition xorlist := combinelist _ Int.xor.

Lemma bxorlist_app xs2 ys2: forall xs1 ys1 zs1 zs2,
      bxorlist xs1 ys1 = Some zs1 -> bxorlist xs2 ys2 = Some zs2 ->
      bxorlist (xs1 ++ xs2) (ys1 ++ ys2) = Some(zs1 ++ zs2).
Proof. 
  induction xs1; intros; destruct ys1; simpl in *; inv H.
  apply H0. 
  unfold bind in *. remember (bxorlist xs1 ys1) as d.
  symmetry in Heqd; destruct d; inv H2.
  rewrite (IHxs1 _ _ _ Heqd H0); reflexivity.
Qed.

Lemma Int64_ltu_false x y: Int64.ltu x y = false ->
      0 <= Int64.unsigned y <= Int64.unsigned x.
Proof. 
  unfold Int64.ltu; intros. if_tac in H. discriminate.
  split. apply Int64.unsigned_range. omega.
Qed.

Definition op_Z_ulong (op: Z->Z->Prop) (x: Z) (y: val) :=
 match y with Vlong y' => op x (Int64.unsigned y') | _ => False end.

Lemma op_Z_ulong_Vlong_repr:
  forall op i n, 
   0 <= n <= Int64.max_unsigned ->
    op_Z_ulong op i (Vlong (Int64.repr n)) = op i n.
Proof.
 intros.
 unfold op_Z_ulong. rewrite Int64.unsigned_repr by auto.
 auto.
Qed.
(*Hint Rewrite op_Z_ulong_Vint_repr using ???(repable_signed) : norm.*)

Lemma int_max_unsigned_int64_max_unsigned: Int.max_unsigned < Int64.max_unsigned.
Proof. cbv; trivial. Qed.

Lemma int_max_signed_int64_max_signed: Int.max_signed < Int64.max_signed.
Proof. cbv; trivial. Qed.

(*Two rules for loops where loop variable is of type tuint and hi is of type tulong.
  The rules correspond to semax_for_simple_u and semax_for_simple_bound_u, respectively.
  Note that the actual value of hi must satisfy 
     (RANGE: 0 <= n <= Int.max_unsigned) in the second rule*)
Lemma semax_for_simple_tulongHi_tuintLoop : 
 forall Inv Espec {cs: compspecs} Delta Pre
           (P:  Z -> list Prop) Q1 (Q: Z -> list localdef) (R: Z -> list mpred)
           _i init hi body Post (*s1*) s2 s3
     (INV: Inv = EX i:Z, local Q1 && PROPx (P i)  (LOCALx (Q i) (SEPx (R i))))
     (TI: (temp_types (update_tycon Delta init)) ! _i = Some (tuint, true))
(*     (Thi: typeof hi = Tint I32 s1 noattr)*)
     (Thi: typeof hi = tulong)
     (CLOQ: forall i, Forall (closed_wrt_vars (eq _i)) (Q1 :: map locald_denote (Q i))),
     @semax cs Espec Delta Pre init
      (normal_ret_assert 
        (EX i:Z, local Q1 && PROPx ((0 <=i <= Int.max_unsigned) :: P i)
              (LOCALx (temp _i (Vint (Int.repr i)) :: Q i) (SEPx (R i))))) ->
     (forall i, PROPx ((0 <= i <= Int.max_unsigned) :: P i) 
       (LOCALx (tc_env (update_tycon Delta init) :: temp _i (Vint (Int.repr i))  :: Q i)
       (SEPx (R i))) |-- 
           (tc_expr (update_tycon Delta init) (Ebinop Olt (Etempvar _i tuint) hi (Tint I32 s3 noattr)))) ->
     (EX i:Z, local (`(op_Z_ulong Z.ge i) (eval_expr hi)) && local Q1 &&
                PROPx ((0 <= i <= Int.max_unsigned) :: P i) (LOCALx (tc_env (update_tycon Delta init)
                                   :: temp _i (Vint (Int.repr i)) 
                                  :: (Q i)) (SEPx (R i)))
            |-- Post EK_normal None)    ->
     (forall i,
     @semax cs Espec (update_tycon Delta init)
        (local (`(op_Z_ulong Z.lt i) (eval_expr hi)) && local Q1 &&
         PROPx ((0 <= i <= Int.max_unsigned) :: P i)
         (LOCALx (temp _i (Vint (Int.repr i))  :: (Q i))
         (SEPx (R i))))
        body
        (normal_ret_assert (local Q1 && PROPx ((0 <= i+1 <= Int.max_unsigned) :: P (i+1))  (LOCALx (temp _i (Vint (Int.repr i))  :: Q (i+1)) (SEPx (R (i+1))))))) ->
     @semax cs Espec Delta Pre 
       (Sfor init
                (Ebinop Olt (Etempvar _i tuint) hi (Tint I32 s3 noattr))
                body 
                (Sset _i (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) (Tint I32 s2 noattr)) tuint))) Post.
Proof.
intros.
unfold Sfor.
eapply semax_seq'; [ eassumption | ].
simpl.
clear Pre H.
assert (H0': forall i : Z,
     PROPx ((0 <= i <= Int.max_unsigned) :: P i)
       (LOCALx
          (tc_env (update_tycon Delta init)
           :: temp _i (Vint (Int.repr i)) :: Q i) (SEPx (R i)))
     |-- tc_expr (update_tycon Delta init)
           ((Eunop Cop.Onotbool (Ebinop Olt (Etempvar _i tuint) hi (Tint I32 s3 noattr)) tint))). {
 intros; eapply derives_trans; [apply H0 | ].
 clear.
 intro rho; unfold tc_expr; simpl;
 rewrite ?denote_tc_assert_andp;
 repeat apply andp_derives; auto.
}
clear H0. rename H0' into H0.
apply (@semax_loop Espec cs _ _
            (EX i:Z, local Q1 && PROPx ((0 <= i+1 <= Int.max_unsigned) :: P (i+1)) 
                (LOCALx (temp _i (Vint (Int.repr i))  :: Q (i+1))
                (SEPx (R (i+1))))));
 [apply semax_pre_simple with ( (tc_expr (update_tycon Delta init) (Eunop Cop.Onotbool (Ebinop Olt (Etempvar _i tuint) hi (Tint I32 s3 noattr)) tint))
                                      &&
                          (EX i:Z,   local Q1 && PROPx ((0 <= i <= Int.max_unsigned) :: P i)  (LOCALx (temp _i (Vint (Int.repr i))  :: Q i) (SEPx (R i)))))
 | ].
*
replace (fun a : environ =>
 EX  x : Z, local Q1 a && 
 PROPx ((0 <= x <= Int.max_unsigned) :: P x)
   (LOCALx (temp _i (Vint (Int.repr x)) :: Q x) (SEPx (R x))) a)
   with (EX  x : Z, local Q1 && PROPx ((0 <= x <= Int.max_unsigned) :: P x)
   (LOCALx (temp _i (Vint (Int.repr x)) :: Q x) (SEPx (R x))))
 by (extensionality; reflexivity).
apply andp_right; [ | apply andp_left2; auto].
repeat rewrite exp_andp2. apply exp_left; intro i. 
eapply derives_trans; [ | apply (H0 i)].
go_lowerx; normalize. apply andp_right; auto. apply prop_right; repeat (split; auto).
destruct H4; auto.
destruct H4; auto.
*
rewrite exp_andp2.
apply extract_exists_pre. intro i.
apply semax_seq with (local (`(typed_true (typeof (Ebinop Olt (Etempvar _i tuint) hi (Tint I32 s3 noattr))))
                             (eval_expr (Ebinop Olt (Etempvar _i tuint) hi tuint))) && local Q1 &&
          PROPx ((0 <= i <= Int.max_unsigned) :: P i)
          (LOCALx (temp _i (Vint (Int.repr i)) :: (Q i))
             (SEPx (R i)))).
+ eapply semax_ifthenelse; auto.
  - rewrite andp_comm.
    simpl typeof.
    eapply semax_post; [ | apply semax_skip].
    intros.
    apply andp_left2.
    unfold normal_ret_assert; normalize.
    unfold overridePost. rewrite if_true by auto.
    normalize. autorewrite with norm1 norm2; normalize.
    apply andp_right. apply andp_right. apply andp_left1; auto.
    apply andp_left2; apply andp_left1; auto.
    apply andp_left2; apply andp_left2; auto.
  - rewrite andp_comm.
    eapply semax_pre_post; [ | intros; apply andp_left2; auto | apply semax_break].
    unfold overridePost. rewrite if_false by discriminate.
    unfold loop1_ret_assert.
    simpl typeof.
    eapply derives_trans; [ | eassumption].
    apply exp_right with i; auto.
    simpl eval_expr.
    go_lowerx.
    repeat apply andp_right; try apply prop_right; auto.

    rename H5 into H5'; rename H3 into H5.
    unfold_lift in H5.
    rewrite <- H7 in H5. rewrite Thi in H5. simpl in H5.
    destruct (eval_expr hi rho); simpl in H5; try solve [inv H5].
    hnf in H5. red.
    rewrite Int.unsigned_repr in H5; auto.
    unfold Int64.ltu in H5.
    if_tac in H5; inv H5.
    rewrite Int64.unsigned_repr in H3; auto.
    specialize int_max_unsigned_int64_max_unsigned; omega. 

  + simpl update_tycon.
    apply semax_extensionality_Delta with (update_tycon Delta init).
    apply tycontext_eqv_sub.
    apply tycontext_eqv_symm.
    apply join_tycon_same.
    simpl typeof.
    eapply semax_post_flipped.
    - eapply semax_pre0; [ | apply (H2 i)].
      go_lowerx. repeat apply andp_right; try apply prop_right; auto.
      rename H4 into H4'; rename H into H4.
      rewrite Thi in H4. unfold_lift in H4. rewrite <- H6 in H4.
      destruct (eval_expr hi rho); simpl in H4; try solve [inv H4].
      hnf in H4. red.
      unfold Int64.ltu in H4.
      if_tac in H4; inv H4.
      rewrite Int.unsigned_repr in H; auto.
      rewrite Int64.unsigned_repr in H; auto.
      specialize int_max_unsigned_int64_max_unsigned; omega. 
    - intros.
      apply andp_left2.
      unfold normal_ret_assert, loop1_ret_assert; normalize.
      intro rho; unfold subst; simpl.
      apply exp_right with i.
      normalize.
* replace (fun a : environ =>
 EX  x : Z,
 PROPx (P x)
   (LOCALx (temp _i (Vint (Int.repr x)) :: Q x) (SEPx (R x))) a)
   with (EX  x : Z, PROPx (P x)
   (LOCALx (temp _i (Vint (Int.repr x)) :: Q x) (SEPx (R x))))
 by (extensionality; reflexivity).
  apply sequential.
  eapply semax_pre_simple; [ | apply semax_set].
  eapply derives_trans; [ | apply now_later].
  simpl typeof.
  unfold loop2_ret_assert.
  apply andp_right.
  + apply andp_left1.
    intro rho.
    unfold local, lift1.
    simpl.
    normalize.
    apply andp_right.
    unfold tc_expr;
    unfold typecheck_expr; fold typecheck_expr.
    repeat rewrite denote_tc_assert_andp.
    repeat apply andp_right; try apply @TT_right.
    rewrite TI. apply @TT_right.
    unfold tc_temp_id, typecheck_temp_id.
    rewrite TI.
    rewrite denote_tc_assert_andp;
    repeat apply andp_right; apply @TT_right.
  + unfold loop2_ret_assert.
    intro rho.
    rewrite exp_andp2.
    simpl.
    unfold subst.
    apply exp_left; intro i.
    apply exp_right with (i+1).
    simpl.
    repeat rewrite <- insert_local.
    simpl.
    specialize (CLOQ (i+1)).
    inv CLOQ.
    rename H4 into CLOQ1; rename H5 into CLOQ.
    apply andp_right.
    apply andp_left2; apply andp_left1.
    autorewrite with norm1 norm2; normalize.
    apply andp_left2. apply andp_left2.
    apply andp_right.
    apply andp_left1.
    unfold locald_denote; simpl.
    autorewrite with norm1 norm2; normalize.
    rewrite <- H. simpl.  normalize.
    normalize;
    autorewrite with norm1 norm2; normalize.
    apply andp_right; auto.
    apply prop_right.
    split; auto.
Qed.

Lemma semax_for_simple_bound_tulongHi_tuintLoop : 
 forall n Inv Espec {cs: compspecs} Delta Pre
           (P:  Z -> list Prop) (Q: Z -> list localdef) (R: Z -> list mpred)
           _i init hi body Post (*s1*) s2 s3
     (INV: Inv = EX i:Z, PROPx (P i)  (LOCALx (Q i) (SEPx (R i))))
     (RANGE: 0 <= n <= Int.max_unsigned)
     (TI: (temp_types (update_tycon Delta init)) ! _i = Some (tuint, true))
(*     (Thi: typeof hi = Tint I32 s1 noattr)*)
     (Thi: typeof hi = tulong)
     (CLOhi: closed_wrt_vars (eq _i) (eval_expr hi))
     (CLOQ: forall i, Forall (closed_wrt_vars (eq _i)) (map locald_denote (Q i))),
     @semax cs Espec Delta Pre init
      (normal_ret_assert 
        (EX i:Z, 
          local (`(eq (Vlong (Int64.repr n))) (eval_expr hi)) &&
          PROPx ((0 <= i <= n) :: P i)
          (LOCALx (temp _i (Vint (Int.repr i)) :: Q i)
           (SEPx (R i))))) ->
     (forall i, 
       PROPx ((0 <= i <= n) :: P i) 
       (LOCALx (tc_env (update_tycon Delta init) :: temp _i (Vint (Int.repr i)) :: Q i)
       (SEPx (R i))) |-- 
            (tc_expr (update_tycon Delta init) (Ebinop Olt (Etempvar _i tuint) hi (Tint I32 s3 noattr)))) ->
     (PROPx (P n)
                  (LOCALx (tc_env (update_tycon Delta init)
                                   :: temp _i (Vint (Int.repr n))
                                  :: (Q n)) (SEPx (R n)))
            |-- Post EK_normal None)    ->
     (forall i,
     @semax cs Espec (update_tycon Delta init)
        (PROPx ((0 <= i < n) :: P i)
         (LOCALx (temp _i (Vint (Int.repr i)) :: (Q i))
         (SEPx (R i))))
        body
        (normal_ret_assert (local (`(eq (Vlong (Int64.repr n))) (eval_expr hi)) &&
                             PROPx ((0 <= i+1 <= n) :: P (i+1)) 
                             (LOCALx (temp _i (Vint (Int.repr i)) :: Q (i+1))
                             (SEPx (R (i+1))))))) ->
     @semax cs Espec Delta Pre 
       (Sfor init
                (Ebinop Olt (Etempvar _i tuint) hi (Tint I32 s3 noattr))
                body 
                (Sset _i (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) (Tint I32 s2 noattr)) tuint))) Post.
Proof.
intros.
assert (RANGEn64: 0 <= n <= Int64.max_unsigned).
   solve [clear - RANGE; specialize int_max_unsigned_int64_max_unsigned; omega]. 
subst Inv.
eapply (semax_for_simple_tulongHi_tuintLoop 
  (EX i:Z, local (`(eq (Vlong (Int64.repr n))) (eval_expr hi)) && PROPx ((i<=n) :: P i)  (LOCALx (Q i) (SEPx (R i)))));
 try reflexivity; eauto.
+ intros. simpl. auto with closed.
+ eapply semax_post_flipped'; [ apply H | ].
  apply exp_derives; intro i.
  go_lowerx. normalize. apply andp_right; auto.
  apply prop_right; repeat split; auto; try omega.
+ intro i. eapply derives_trans; [ | solve [eauto]].
  instantiate (1:=i).
  go_lowerx. normalize. apply andp_right; auto.
  apply prop_right.
  split; [omega | ].
  split. split; auto. split; auto.
+ apply exp_left; intro i.
  eapply derives_trans; [ | solve [eauto]].
  go_lowerx; normalize.
  rewrite <- H4, op_Z_ulong_Vlong_repr in H3; trivial.
  assert (i=n) by omega.
  subst i.
  apply andp_right; auto.
  apply prop_right.
  split; auto.
+ intro.
  eapply semax_pre_post; [ | | solve [eauto]].
  instantiate (1:=i).
  apply andp_left2. go_lowerx; normalize.
  apply andp_right; auto.
  apply prop_right.
  split; auto. omega. split; auto. split; auto.
(*  rewrite <- H4 in H3; normalize in H3.*)
  rewrite <- H4 in H3; simpl in H3. rewrite Int64.unsigned_repr in H3; trivial. 
  intros.
  apply andp_left2.
  apply normal_ret_assert_derives'.
  go_lowerx; normalize.
  apply andp_right; auto.
  apply prop_right.
  split; auto. omega. split; auto. split; auto.
  omega. split; auto. omega.
Qed.

Definition Bl2VL (l: list byte) := map Vint (map Int.repr (map Byte.unsigned l)).

Lemma Zlength_Bl2VL l: Zlength (Bl2VL l) = Zlength l.
Proof. unfold Bl2VL. repeat rewrite Zlength_map. trivial.
Qed.

Fixpoint ZZ (zbytes: list byte) (n: nat): int * list byte :=
  match n with
   O => (Int.one, zbytes)
  | S k => match ZZ zbytes k with (u,zb) => 
             let v := (Int.unsigned u + (Byte.unsigned (Znth (Z.of_nat k+8) zb Byte.zero)))
             in (Int.shru (Int.repr v) (Int.repr 8), 
                 upd_Znth (Z.of_nat k+8) zb (Byte.repr (Z.modulo v 256))) end
          
  end.

Lemma ZZ_bound: forall n zbytes u U, ZZ zbytes n = (u,U) -> 0<= Int.unsigned u <256.
Proof. induction n; simpl; intros. inv H. unfold Int.one. rewrite Int.unsigned_repr; try omega. rewrite int_max_unsigned_eq; omega.
  remember (ZZ zbytes n). destruct p. symmetry in Heqp. inv H. apply IHn in Heqp. clear IHn.
  remember (Znth (Z.of_nat n + 8) l Byte.zero) as b. clear Heqb.
  specialize Byte_max_unsigned_Int_max_unsigned; intros B.
  assert (B1: Byte.max_unsigned = 255) by reflexivity.
  assert (B2: two_p 8 = 256) by reflexivity. 
  destruct (Byte.unsigned_range_2 b). 
  rewrite Int.shru_div_two_p. rewrite (Int.unsigned_repr 8). 2: rewrite int_max_unsigned_eq; omega.
  assert (B3: 0 <= Int.unsigned i + Byte.unsigned b <= Int.max_unsigned).
    split. omega. rewrite int_max_unsigned_eq; omega. 
  assert (0 <= (Int.unsigned i + Byte.unsigned b) / two_p 8 < 256).
    split. apply Z_div_pos. cbv; trivial. omega.
    apply Zdiv_lt_upper_bound. cbv; trivial. omega. 
  rewrite Int.unsigned_repr; rewrite Int.unsigned_repr; trivial. omega.
Qed.

Definition Data_as_QuadBytes
           (data : SixteenByte * SixteenByte * (SixteenByte * SixteenByte)): list QuadByte :=
match data with ((Nonce, C), K) =>
  match Nonce with (N1, N2, N3, N4) => 
  match C with (C1, C2, C3, C4) => 
  match K with ((K1, K2, K3, K4), (L1, L2, L3, L4)) =>
  [N1;N2;N3;N4;C1;C2;C3;C4;K1;K2;K3;K4;L1;L2;L3;L4]
  end end end
end.

Definition Data_as_reordered_QuadBytes
           (data : SixteenByte * SixteenByte * (SixteenByte * SixteenByte)): list QuadByte :=
match data with ((Nonce, C), K) =>
  match Nonce with (N1, N2, N3, N4) => 
  match C with (C1, C2, C3, C4) => 
  match K with ((K1, K2, K3, K4), (L1, L2, L3, L4)) =>
  [C1; K1; K2; K3; K4; C2; N1; N2; N3; N4; C3; L1; L2; L3; L4; C4]
  end end end
end.

Fixpoint flatten {A} (l: list (list A)): list A :=
  match l with [] => [] | (h::t) => h ++ flatten t end.

Definition Data_as_bytelist data:= flatten (map QuadByte2ByteList (Data_as_reordered_QuadBytes data)).

(*
Fixpoint ZZb (zbytes: list byte) (n: nat): byte * list byte :=
  match n with
   O => (Byte.one, zbytes)
  | S k => match ZZb zbytes k with (u,zb) => 
             let v := (Byte.unsigned u + (Byte.unsigned (Znth (Z.of_nat k+8) zb Byte.zero)))
             in (Byte.shru (Byte.repr v) (Byte.repr 8), 
                 upd_Znth (Z.of_nat k+8) zb (Byte.repr (v mod 256))) end
          
  end.

Lemma ZZb_ZZ: forall n zbytes, 
  match ZZb zbytes n with (x,y) => ZZ zbytes n = (Int.repr (Byte.unsigned x), y) end.
Proof.
induction n; simpl; intros. unfold Byte.one. rewrite Byte.unsigned_repr. reflexivity. cbv; intuition.
remember (ZZb zbytes n). destruct p. 
specialize (IHn zbytes). rewrite <- Heqp in IHn. rewrite IHn; clear IHn.
rewrite Int_unsigned_repr_byte.
 f_equal.
  unfold Int.shru. rewrite Int.unsigned_repr. rewrite Int.unsigned_repr. 
  unfold Byte.shru. rewrite (Byte.unsigned_repr 8).
  rewrite (Byte.unsigned_repr (Byte.unsigned i + Byte.unsigned (Znth (Z.of_nat n + 8) l Byte.zero))).
  rewrite Byte.unsigned_repr. trivial.
  3: cbv; intuition.
  3: cbv; intuition. Focus 2.
    
rewrite 

Definition ZZb (zbytes: list byte) (n: nat): byte * list byte :=
  match ZZ zbytes n with (u,zb) => (Byte.repr (Int.unsigned u), zb) end.

Lemma ROTATE N1 N2 N3 N4 zbytes: 
      SixteenByte2ValList (N1, N2, N3, N4) =
         map Vint (map Int.repr (map Byte.unsigned zbytes)) ->
      SixteenByte2ValList (N2, N3, N4, (Byte.zero, Byte.zero, Byte.zero, Byte.zero)) =
         map Vint (map Int.repr (map Byte.unsigned (snd (ZZ zbytes 8)))).
Proof. intros. 
  specialize (SixteenByte2ValList_Zlength (N1, N2, N3, N4)).
  rewrite H; repeat rewrite Zlength_map; intros. symmetry in H0.
  remember (ZZ zbytes 8) as Q. 
  destruct (listD16 _ H0) as
  [y0 [y1 [y2 [y3 [y4 [y5 [y6 [y7 [y8 [y9 [y10 [y11 [y12 [y13 [y14 [y15 Y]]]]]]]]]]]]]]]].
  subst zbytes. simpl in HeqQ. simpl. 
*)

Definition i_8_16_inv F x z c b m nonce k SV zbytes: environ -> mpred := 
EX i:_,
  (PROP  ()
   LOCAL  (temp _u (Vint (fst (ZZ zbytes (Z.to_nat (i-8)))));
     lvar _x (Tarray tuchar 64 noattr) x;
     lvar _z (Tarray tuchar 16 noattr) z; temp _c c; temp _m m;
     temp _b b; temp _n nonce; temp _k k; gvar _sigma SV)
   SEP  (F; data_at Tsh (Tarray tuchar 16 noattr) (Bl2VL (snd (ZZ zbytes (Z.to_nat (i-8))))) z)).

Lemma For_i_8_16_loop Espec F x z c m b nonce k SV zbytes:
@semax CompSpecs Espec 
  (initialized_list [_u; _i]
     (func_tycontext f_crypto_stream_salsa20_tweet_xor SalsaVarSpecs SalsaFunSpecs))
  (PROP  ()
   LOCAL  (temp _u (Vint (Int.repr 1)); lvar _x (Tarray tuchar 64 noattr) x;
   lvar _z (Tarray tuchar 16 noattr) z; temp _c c; temp _m m;
   temp _b b; temp _n nonce;
   temp _k k; gvar _sigma SV)
   SEP  (F; data_at Tsh (Tarray tuchar 16 noattr) (Bl2VL zbytes) z))
  (Sfor (Sset _i (Econst_int (Int.repr 8) tint))
     (Ebinop Olt (Etempvar _i tuint) (Econst_int (Int.repr 16) tint) tint)
     (Ssequence
        (Sset _temp
           (Ecast
              (Ederef
                 (Ebinop Oadd (Evar _z (tarray tuchar 16))
                    (Etempvar _i tuint) (tptr tuchar)) tuchar) tuchar))
        (Ssequence
           (Sset _u
              (Ebinop Oadd (Etempvar _u tuint)
                 (Ecast (Etempvar _temp tuchar) tuint) tuint))
           (Ssequence
              (Sassign
                 (Ederef
                    (Ebinop Oadd (Evar _z (tarray tuchar 16))
                       (Etempvar _i tuint) (tptr tuchar)) tuchar)
                 (Etempvar _u tuint))
              (Sset _u
                 (Ebinop Oshr (Etempvar _u tuint)
                    (Econst_int (Int.repr 8) tint) tuint)))))
     (Sset _i
        (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint) tuint)))
  (normal_ret_assert 
  ( PROP ()
    LOCAL (lvar _x (Tarray tuchar 64 noattr) x;
           lvar _z (Tarray tuchar 16 noattr) z; temp _c c; temp _m m;
           temp _b b; temp _n nonce; temp _k k; gvar _sigma SV)
    SEP (F; data_at Tsh (Tarray tuchar 16 noattr) (Bl2VL (snd (ZZ zbytes 8))) z))).
Proof.
forward_for_simple_bound 16 (i_8_16_inv F x z c b m nonce k SV zbytes).
{ entailer!. }
{ rename H into I. 
  remember (ZZ zbytes (Z.to_nat (i - 8))) as X. destruct X as [ui Zi]. 
  assert_PROP (Zlength (Bl2VL Zi) = 16) as L by entailer!.
  unfold Bl2VL in L; rewrite Zlength_map in L.
  destruct (Znth_mapVint (map Int.repr (map Byte.unsigned Zi)) i Vundef) as [vi Vi].
    omega.
  rewrite Znth_map with (d':= Int.zero) in Vi.
  2: omega.
  inv Vi. unfold Bl2VL.

  forward.
  { entailer!. rewrite Znth_map with (d':= Int.zero). 2: omega.
    simpl. 
    eapply zero_ext_range2. cbv; intuition. reflexivity. reflexivity.
  }
  simpl. rewrite Znth_map with (d':= Int.zero). 2: omega.
    simpl. rewrite Zlength_map in L.
    rewrite Znth_map with (d':=Z0); try omega.
    rewrite Zlength_map in L.
    rewrite Znth_map with (d':=Byte.zero); try omega. 
    rewrite zero_ext8_byte. 
  forward.
  forward.
  assert (Q: Z.to_nat (i + 1 - 8) = S (Z.to_nat (i-8))).
    rewrite <- Z2Nat.inj_succ. f_equal. omega. omega.
  forward.
  assert_PROP (isptr z) as PtrZ by entailer!.
  entailer!. rewrite Q; simpl; rewrite <- HeqX; simpl.
  f_equal. assert (W:Z.of_nat (Z.to_nat (i - 8)) + 8 = i).
     rewrite Z2Nat.id; omega.
     rewrite W. f_equal.
     unfold Int.add. rewrite Int_unsigned_repr_byte. trivial. 

  rewrite field_at_data_at. apply derives_refl'. f_equal.
  2: rewrite field_address_offset by auto with field_compatible; apply isptr_offset_val_zero; trivial.
  clear H4 H2 H1 H0 TC4 TC3 TC2 TC1 TC0 TC. unfold Bl2VL.
  rewrite Q; simpl; rewrite <- HeqX. 
  rewrite upd_Znth_map. f_equal. simpl.
  assert (W:Z.of_nat (Z.to_nat (i - 8)) + 8 = i). rewrite Z2Nat.id; omega.
  rewrite W. do 2 rewrite <- upd_Znth_map.
  rewrite Byte.unsigned_repr.
  Focus 2. assert (Byte.max_unsigned = 255) by reflexivity.
           destruct (Z_mod_lt (Int.unsigned ui + Byte.unsigned (Znth i Zi Byte.zero)) 256); omega.
  unfold Int.add. rewrite Int_unsigned_repr_byte.
  f_equal. unfold Int.zero_ext. f_equal. apply Int.equal_same_bits.
  intros j J. 
  rewrite Int.Zzero_ext_spec; trivial. rewrite (Byte.Ztestbit_mod_two_p 8); trivial.
  rewrite Int.unsigned_repr; trivial.
  symmetry in HeqX. apply ZZ_bound in HeqX. destruct (Byte.unsigned_range_2 (Znth i Zi Byte.zero)).
  assert (BB: Byte.max_unsigned = 255) by reflexivity. rewrite int_max_unsigned_eq.  omega.
}
Opaque ZZ.
entailer!.
Qed.

Definition message_at (mCont: list byte) (m:val): mpred :=
  match m with
    Vint i => !!(i=Int.zero) && emp
  | Vptr b z => data_at Tsh (tarray tuchar (Zlength mCont)) (Bl2VL mCont) m
  | _ => FF
  end.

Definition null_or_offset x q y :=
match x with 
  Vint i => i=Int.zero /\ y=nullval
| Vptr _ _ => y=offset_val (Int.repr q) x
| _ => False
end.

Definition byte_at x i mbytes :=
    match x with
     Vint _ => Byte.zero
   | _ => Znth i mbytes Byte.zero
    end.

Definition bytes_at x q i mbytes :=
match x with
  Vint _ => list_repeat (Z.to_nat i) (Byte.zero)
| _ => sublist q (q+i) mbytes
end.

Lemma bxorlist_snoc x q y b l mbytes xbytes
        (M:null_or_offset x q y )  
        (X: bxorlist (bytes_at x q (Zlength l) mbytes)
                     (sublist 0 (Zlength l) xbytes) = Some l):
        0<= q -> Zlength l < Zlength xbytes ->  q+ Zlength l < Zlength mbytes ->
        b = Byte.xor (byte_at x (Zlength l + q) mbytes)
                     (Znth (Zlength l) xbytes Byte.zero) -> 
  bxorlist (bytes_at x q (Zlength l  + 1) mbytes)
           (sublist 0 (Zlength l  + 1) xbytes) = Some (l ++ [b]).
Proof.
  specialize (Zlength_nonneg l). intros. unfold bytes_at. 
  rewrite (Z.add_assoc q), (sublist_hi_plus xbytes), (sublist_hi_plus mbytes). 
  destruct x; try contradiction.
      - destruct M as [M1 M2]. subst i y. simpl. simpl in X.
        rewrite Z2Nat.inj_add, <- list_repeat_app.
        apply bxorlist_app. assumption.
        rewrite pure_lemmas.sublist_singleton with (d:=Byte.zero). simpl. subst b. reflexivity.
        omega. omega. omega.
      - simpl in M. subst y. (*rewrite M in *;*) simpl in X; simpl.
        rewrite pure_lemmas.sublist_singleton with (d:=Byte.zero).
        apply bxorlist_app. assumption.
        rewrite pure_lemmas.sublist_singleton with (d:=Byte.zero). subst b. rewrite Z.add_comm. reflexivity.
        omega. omega.
      - omega.
      - omega.
      - omega.
      - omega.
Qed.

Lemma loop1 Espec F x z c mInit b nonce k m xbytes mbytes SV cLen 
      q (M: null_or_offset mInit q m)
      (Q: 0 <= q <= (Zlength mbytes) - 64) (CL: 64 <= cLen):
@semax CompSpecs Espec 
  (initialized_list [_i]
     (func_tycontext f_crypto_stream_salsa20_tweet_xor SalsaVarSpecs SalsaFunSpecs))
  (PROP  ()
   LOCAL  (lvar _x (Tarray tuchar 64 noattr) x;
   lvar _z (Tarray tuchar 16 noattr) z; temp _c c; temp _m m;
   temp _b b; temp _n nonce;
   temp _k k; gvar _sigma SV)
   SEP  (F;
   data_at Tsh (tarray tuchar 64)
     (map Vint (map Int.repr (map Byte.unsigned xbytes))) x;
   data_at_ Tsh (Tarray tuchar cLen noattr) c;
   message_at mbytes mInit))
(Sfor (Sset _i (Econst_int (Int.repr 0) tint))
        (Ebinop Olt (Etempvar _i tuint) (Econst_int (Int.repr 64) tint) tint)
        (Ssequence
           (Ssequence
              (Sifthenelse
                 (Ebinop One (Etempvar _m (tptr tuchar))
                    (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
                 (Sset 188%positive
                    (Ecast
                       (Ederef
                          (Ebinop Oadd (Etempvar _m (tptr tuchar))
                             (Etempvar _i tuint) (tptr tuchar)) tuchar) tint))
                 (Sset 188%positive
                    (Ecast (Econst_int (Int.repr 0) tint) tint)))
              (Sset _loop2left (Ecast (Etempvar 188%positive tint) tuchar)))
           (Ssequence
              (Sset _loop2right
                 (Ecast
                    (Ederef
                       (Ebinop Oadd (Evar _x (tarray tuchar 64))
                          (Etempvar _i tuint) (tptr tuchar)) tuchar) tuchar))
              (Sassign
                 (Ederef
                    (Ebinop Oadd (Etempvar _c (tptr tuchar))
                       (Etempvar _i tuint) (tptr tuchar)) tuchar)
                 (Ebinop Oxor (Etempvar _loop2left tuchar)
                    (Etempvar _loop2right tuchar) tint))))
        (Sset _i
           (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
              tuint)))
(normal_ret_assert 
  ( PROP  ()
    LOCAL  (temp _i (Vint (Int.repr 64)); lvar _x (Tarray tuchar 64 noattr) x;
       lvar _z (Tarray tuchar 16 noattr) z; temp _c c; temp _m m; temp _b b;
       temp _n nonce; temp _k k; gvar _sigma SV)
    SEP  (F;
          data_at Tsh (tarray tuchar 64)
             (map Vint (map Int.repr (map Byte.unsigned xbytes))) x;
          message_at mbytes mInit;
         EX  l : list byte,
          !!(bxorlist (bytes_at mInit q 64 mbytes) (sublist 0 64 xbytes) = Some l) &&
          data_at Tsh (Tarray tuchar cLen noattr)
            (Bl2VL l ++ list_repeat (Z.to_nat (cLen - 64)) Vundef) c))).
Proof. intros.
Intros. 
forward_for_simple_bound 64 (EX i:Z, 
  (PROP  ()
   LOCAL  (lvar _x (Tarray tuchar 64 noattr) x;
   lvar _z (Tarray tuchar 16 noattr) z; temp _c c; temp _m m;
   temp _b b; temp _n nonce;
   temp _k k; gvar _sigma SV)
   SEP (F;
     data_at Tsh (tarray tuchar 64)
       (map Vint (map Int.repr (map Byte.unsigned xbytes))) x;
     message_at mbytes mInit;
     EX l:_,!!(bxorlist (bytes_at mInit q i mbytes) 
                        (sublist 0 i xbytes)
               = Some l)
         && data_at Tsh (Tarray tuchar cLen noattr)
                        (Bl2VL l ++ list_repeat (Z.to_nat (cLen - i)) Vundef) c))).
{ entailer!. rewrite Zminus_0_r. autorewrite with sublist.
  Exists (@nil byte). 
  unfold Bl2VL; simpl.
  entailer!.
  destruct mInit; simpl in M; try contradiction.
  destruct M; subst; simpl; trivial.
  subst; simpl. autorewrite with sublist. trivial. }
rename H into I.
  Intros l. rename H into XOR.
  assert_PROP (isptr c) as C by entailer!.
  assert_PROP (Zlength xbytes = 64) as XL.
  { entailer!. repeat rewrite Zlength_map in H4. trivial. } 
  freeze [0;1;3] FR1.
  forward_if
  (PROP  ()
   LOCAL  (temp _i (Vint (Int.repr i)); lvar _x (Tarray tuchar 64 noattr) x;
      lvar _z (Tarray tuchar 16 noattr) z; temp _c c; temp _m m;
      temp _b b; temp _n nonce; temp _k k; gvar _sigma SV;
      temp 188%positive (Vint (Int.repr (Byte.unsigned (byte_at mInit (i+q) mbytes)))))
   SEP  (FRZL FR1; message_at mbytes mInit)).
  { apply denote_tc_comparable_split.
    + clear H XOR. destruct mInit; simpl in M; try contradiction.
      - destruct M. subst m. apply valid_pointer_null.
      - subst m. thaw FR1. apply sepcon_valid_pointer2.
        unfold message_at. 
        eapply derives_trans. apply data_at_memory_block.
        eapply derives_trans. apply memory_block_valid_pointer.
        3: apply derives_refl.
        simpl. rewrite Z.max_r. omega. apply Zlength_nonneg.
        apply top_share_nonidentity.
    + apply valid_pointer_null. }
  { unfold Bl2VL in *.
    destruct mInit; try contradiction. destruct M; contradiction.
    clear H.
    unfold message_at. rewrite M in *. simpl in *.
    unfold tarray.
    assert_PROP (field_compatible (Tarray tuchar (Zlength mbytes) noattr) [] (Vptr b0 i0)) by entailer!.
    erewrite (split2_data_at_Tarray_tuchar _ _ q). 2: omega. 2: unfold Bl2VL; repeat rewrite Zlength_map; trivial. 
    normalize. unfold field_address0. simpl.
    destruct (field_compatible0_dec (Tarray tuchar (Zlength mbytes) noattr)
           [ArraySubsc q] (Vptr b0 i0)).
    Focus 2. elim n; clear n. apply field_compatible0_cons. simpl. split; trivial. omega.
    assert (X: 0 + 1 * q = q) by omega. rewrite X; clear X. 
    destruct (Znth_mapVint (map Int.repr (map Byte.unsigned mbytes)) (i+q) Vundef) as [mi Mi]. 
      repeat rewrite Zlength_map; omega. 
    forward. 
    { entailer!. rewrite Znth_sublist. unfold Bl2VL. rewrite Mi. simpl. trivial. omega. omega. }
    rewrite Znth_sublist. unfold Bl2VL. rewrite Mi.
    entailer!. 
      rewrite Znth_map with (d':=Int.zero) in Mi. inversion Mi.
      rewrite Znth_map with (d':=Z0). 
      rewrite Znth_map with (d':=Byte.zero); trivial. omega.
      rewrite Zlength_map; omega.
      repeat rewrite Zlength_map; omega. 
 
      erewrite (split2_data_at_Tarray_tuchar _ (Zlength mbytes) q).
      2: omega. 2: unfold Bl2VL; repeat rewrite Zlength_map; trivial. 
      unfold field_address0. simpl. autorewrite with sublist in *. 
         if_tac; try contradiction.
      rewrite Z.mul_1_l. cancel.
      omega. omega.
  }
  { rewrite H in *; simpl in *. 
    destruct mInit; simpl in M; try contradiction.
    destruct M as [M _]. 2: discriminate.
    forward. entailer!.
  } 
  forward. drop_LOCAL 10%nat. (*variable 188*) 
  destruct (Znth_mapVint (map Int.repr (map Byte.unsigned xbytes)) i Vundef) as  [xi Xi].
    repeat rewrite Zlength_map. omega.
  thaw FR1. freeze [0;2;3] FR2.
  forward; rewrite Xi.
  { entailer!.
    eapply zero_ext_range2; try reflexivity. cbv; intuition.
  } 
  simpl.
  thaw FR2. freeze [0;2;3] FR3.
  forward.
  { entailer!.
    clear H4 TC TC1 TC2 TC3 TC4 TC5.
    specialize (Zlength_combinelist _ _ _ _ XOR); intros LL.
    autorewrite with sublist in LL.
    rewrite upd_Znth_app2.  
    Focus 2. rewrite Zlength_Bl2VL. autorewrite with sublist. omega.
    rewrite field_at_data_at, Zlength_Bl2VL, LL, Zminus_diag, upd_Znth0, sublist_list_repeat; try omega.
    2: autorewrite with sublist; omega.
    simpl. thaw FR3.
    rewrite Znth_map with (d':=Int.zero) in Xi. inv Xi. 2: repeat rewrite Zlength_map; omega.
    rewrite Znth_map with (d':=Z0). 2: rewrite Zlength_map; omega.
    rewrite Znth_map with (d':=Byte.zero). 2: omega. 
    remember (Byte.xor (byte_at mInit (Zlength l+q) mbytes) 
                       (Znth (Zlength l) xbytes Byte.zero)) as mybyte.
    Exists (l++ [mybyte]). cancel.
    apply andp_right.
    + apply prop_right. 
      eapply (bxorlist_snoc mInit q _id3 mybyte l); trivial; omega.
    + autorewrite with sublist.
      rewrite field_address_offset by auto with field_compatible.
      simpl. rewrite isptr_offset_val_zero; trivial.
      apply derives_refl'. f_equal. unfold Bl2VL. subst mybyte. clear.
      repeat rewrite map_app. rewrite <- app_assoc. f_equal. simpl.
      f_equal.
      repeat rewrite zero_ext_inrange; try rewrite xor_byte_int; try rewrite Int.unsigned_repr; trivial;
        try apply Byte.unsigned_range_2;
        try apply byte_unsigned_range_3.
      assert (X:cLen - Zlength l - 1 = cLen - (Zlength l + 1)) by omega.
      rewrite X; trivial.
  }
apply derives_refl.
Qed.

Parameter SIGMA: SixteenByte.
Definition Sigma_vector : val -> mpred :=
  data_at Tsh (tarray tuchar 16) (SixteenByte2ValList SIGMA).

Definition loop2Inv F x z c mInit m b nonce k SV q xbytes mbytes cLen: environ -> mpred:=
EX i:Z, 
  (PROP  ()
   LOCAL  (lvar _x (Tarray tuchar 64 noattr) x;
   lvar _z (Tarray tuchar 16 noattr) z; temp _c c; temp _m m;
   temp _b b; temp _n nonce;
   temp _k k; gvar _sigma SV)
   SEP (F;
     data_at Tsh (tarray tuchar 64)
       (map Vint (map Int.repr (map Byte.unsigned xbytes))) x;
     message_at mbytes mInit;
     EX l:_,!!(bxorlist (bytes_at mInit q i mbytes) 
                        (sublist 0 i xbytes)
               = Some l)
         && data_at Tsh (Tarray tuchar cLen noattr)
                        (Bl2VL l ++ list_repeat (Z.to_nat (cLen - i)) Vundef) c)).

Lemma loop2 Espec F x z c mInit m b nonce k xbytes mbytes SV
      q (M: null_or_offset mInit q m) (Q: 0 <= q) (QB: q+Int64.unsigned b = Zlength mbytes) (*(CL: 64 > cLen) *) (*should be b <= cLen or so?*)
      (B: Int64.unsigned b < 64):
@semax CompSpecs Espec

  (initialized_list [_i]
     (func_tycontext f_crypto_stream_salsa20_tweet_xor SalsaVarSpecs SalsaFunSpecs))

  (PROP  ()
   LOCAL  (lvar _x (Tarray tuchar 64 noattr) x;
   lvar _z (Tarray tuchar 16 noattr) z; temp _c c; temp _m m;
   temp _b (Vlong b); temp _n nonce;
   temp _k k; gvar _sigma SV)
   SEP  (F; data_at Tsh (tarray tuchar 64)
              (map Vint (map Int.repr (map Byte.unsigned xbytes))) x;
         data_at_ Tsh (Tarray tuchar (Int64.unsigned b) noattr) c;
         message_at mbytes mInit))

  (Sfor (Sset _i (Econst_int (Int.repr 0) tint))
     (Ebinop Olt (Etempvar _i tuint) (Etempvar _b tulong) tint)
     (Ssequence
        (Ssequence
           (Sifthenelse
              (Ebinop One (Etempvar _m (tptr tuchar))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
              (Sset 189%positive
                 (Ecast
                    (Ederef
                       (Ebinop Oadd (Etempvar _m (tptr tuchar))
                          (Etempvar _i tuint) (tptr tuchar)) tuchar) tint))
              (Sset 189%positive (Ecast (Econst_int (Int.repr 0) tint) tint)))
           (Sset _loop3left (Ecast (Etempvar 189%positive tint) tuchar)))
        (Ssequence
           (Sset _loop3right
              (Ecast
                 (Ederef
                    (Ebinop Oadd (Evar _x (tarray tuchar 64))
                       (Etempvar _i tuint) (tptr tuchar)) tuchar) tuchar))
           (Sassign
              (Ederef
                 (Ebinop Oadd (Etempvar _c (tptr tuchar)) (Etempvar _i tuint)
                    (tptr tuchar)) tuchar)
              (Ebinop Oxor (Etempvar _loop3left tuchar)
                 (Etempvar _loop3right tuchar) tint))))
     (Sset _i
        (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint) tuint)))

(normal_ret_assert 
  ( PROP  ()
    LOCAL  ((*temp _i (Vlong b); *) lvar _x (Tarray tuchar 64 noattr) x;
       lvar _z (Tarray tuchar 16 noattr) z; temp _c c; temp _m m; temp _b (Vlong b);
       temp _n nonce; temp _k k; gvar _sigma SV)
    SEP  (F;
          data_at Tsh (tarray tuchar 64)
             (map Vint (map Int.repr (map Byte.unsigned xbytes))) x;
          message_at mbytes mInit;
         EX  l : list byte,
          !!(bxorlist (bytes_at mInit q (Int64.unsigned b) mbytes) (sublist 0 (Int64.unsigned b) xbytes) = Some l) &&
          data_at Tsh (Tarray tuchar (Int64.unsigned b) noattr) (Bl2VL l) c))).
Proof. intros.
destruct (Int64.unsigned_range_2 b) as [bLo bHi].

eapply semax_post.
Focus 2.
{ eapply (semax_for_simple_bound_tulongHi_tuintLoop (Int64.unsigned b) 
    (loop2Inv F x z c mInit m (Vlong b) nonce k SV q xbytes mbytes (Int64.unsigned b))).
  + reflexivity.
  + rewrite int_max_unsigned_eq; omega. 
  + reflexivity.
  + reflexivity. 
  + auto 50 with closed.
  + intro; unfold map at 1; auto 50 with closed.
  + cbv beta; simpl update_tycon.
    forward.
    Exists 0. rewrite Int64.repr_unsigned. entailer!.
    autorewrite with sublist. Exists (@nil byte).
    unfold Bl2VL; simpl. entailer!.
    destruct mInit; simpl in M; try contradiction.
    destruct M; subst. simpl. trivial.
    simpl. autorewrite with sublist. reflexivity.
  + intro; cbv beta; simpl update_tycon; try solve [entailer!].
  + try apply semax_for_resolve_postcondition.
  + intro; cbv beta; simpl update_tycon; abbreviate_semax;
     try (apply semax_extract_PROP; intro).
    rename H into I.
    Intros l. rename H into XOR.
  assert_PROP (isptr c) as C by entailer!.
  assert_PROP (Zlength xbytes = 64) as XL.
  { entailer!. repeat rewrite Zlength_map in H4. trivial. } 
  freeze [0;1;3] FR1.
  forward_if
  (PROP  ()
   LOCAL  (temp _i (Vint (Int.repr i)); lvar _x (Tarray tuchar 64 noattr) x;
      lvar _z (Tarray tuchar 16 noattr) z; temp _c c; temp _m m;
      temp _b (Vlong b); temp _n nonce; temp _k k; gvar _sigma SV;
      temp 189%positive (Vint (Int.repr (Byte.unsigned (byte_at mInit (i+q) mbytes)))))
   SEP  (FRZL FR1; message_at mbytes mInit)).
  { apply denote_tc_comparable_split.
    + clear H XOR. destruct mInit; simpl in M; try contradiction.
      - destruct M. subst m. apply valid_pointer_null.
      - subst m. thaw FR1. apply sepcon_valid_pointer2.
        unfold message_at. 
        eapply derives_trans. apply data_at_memory_block.
        eapply derives_trans. apply memory_block_valid_pointer.
        3: apply derives_refl.
        simpl. rewrite Z.max_r. omega. apply Zlength_nonneg.
        apply top_share_nonidentity.
    + apply valid_pointer_null. }
  { unfold Bl2VL in *.
    destruct mInit; try contradiction; simpl in M. destruct M; contradiction.
    clear H.
    unfold message_at. rewrite M in *. simpl in *.
    unfold tarray.
    assert_PROP (field_compatible (Tarray tuchar (Zlength mbytes) noattr) [] (Vptr b0 i0)) by entailer!.
    erewrite (split2_data_at_Tarray_tuchar _ _ q). 2: omega. 2: unfold Bl2VL; repeat rewrite Zlength_map; trivial. 
    normalize. unfold field_address0. simpl.
    destruct (field_compatible0_dec (Tarray tuchar (Zlength mbytes) noattr)
           [ArraySubsc q] (Vptr b0 i0)).
    Focus 2. elim n; clear n. apply field_compatible0_cons. simpl. split; trivial. omega.
    assert (X: 0 + 1 * q = q) by omega. rewrite X; clear X. 
    destruct (Znth_mapVint (map Int.repr (map Byte.unsigned mbytes)) (i+q) Vundef) as [mi Mi]. 
      repeat rewrite Zlength_map; omega. 
    forward. 
    { entailer!. rewrite Znth_sublist. unfold Bl2VL. rewrite Mi. simpl. trivial. omega. omega. }
    rewrite Znth_sublist. unfold Bl2VL. rewrite Mi.
    entailer!. 
      rewrite Znth_map with (d':=Int.zero) in Mi. inversion Mi.
      rewrite Znth_map with (d':=Z0). 
      rewrite Znth_map with (d':=Byte.zero); trivial. omega.
      rewrite Zlength_map; omega.
      repeat rewrite Zlength_map; omega. 
 
      erewrite (split2_data_at_Tarray_tuchar _ (Zlength mbytes) q).
      2: omega. 2: unfold Bl2VL; repeat rewrite Zlength_map; trivial. 
      unfold field_address0. simpl. autorewrite with sublist in *. 
         if_tac; try contradiction.
      rewrite Z.mul_1_l. cancel.
      omega. omega.
  }
  { rewrite H in *; simpl in *. 
    destruct mInit; simpl in M; try contradiction.
    destruct M as [M _]. 2: discriminate.
    forward. entailer!.
  } 
  forward. drop_LOCAL 10%nat. (*variable 189*) 
  destruct (Znth_mapVint (map Int.repr (map Byte.unsigned xbytes)) i Vundef) as  [xi Xi].
    repeat rewrite Zlength_map. omega.
  thaw FR1. freeze [0;2;3] FR2.
  forward; rewrite Xi.
  { entailer!.
    eapply zero_ext_range2; try reflexivity. cbv; intuition.
  } 
  simpl.
  thaw FR2. freeze [0;2;3] FR3. (* rewrite zero_ext8_byte.
  rewrite Znth_map with (d':= Int.zero) in Xi. 2: repeat rewrite Zlength_map; omega.
  rewrite Znth_map with (d':= Z0) in Xi. 2: rewrite Zlength_map; omega.
  rewrite Znth_map with (d':= Byte.zero) in Xi. 2: omega.
  inversion Xi; clear Xi. subst xi. rewrite zero_ext8_byte.
  remember  (Bl2VL l ++ list_repeat (Z.to_nat (Int64.unsigned b - Zlength l)) Vundef) as ll.
  simpl. 
  apply isptrD in C. destruct C as [cb [coff C]]. rewrite C in *.
*)
eapply semax_post.
Focus 2. my_store_tac. apply prop_right. split; simpl; trivial. 
  (*Qinxiang: forward again runs out of heap here - just commenting out the solve_legal_nested_field_in_entailment 
    in store_tac solves the problem*)
(*  forward.*)
  intros. apply andp_left2. instantiate (1:= POSTCONDITION).
  unfold overridePost, POSTCONDITION, abbreviate. entailer!.
  if_tac; entailer!. rewrite normal_ret_assert_elim.
  entailer!. rewrite Int64.repr_unsigned. trivial.
    specialize (Zlength_combinelist _ _ _ _ XOR); intros LL.
    autorewrite with sublist in LL.
    rewrite upd_Znth_app2.  
    Focus 2. rewrite Zlength_Bl2VL. autorewrite with sublist. omega.
    rewrite field_at_data_at, Zlength_Bl2VL, LL, Zminus_diag, upd_Znth0, sublist_list_repeat; try omega.
    2: autorewrite with sublist; omega.
    simpl. thaw FR3. 
    rewrite Znth_map with (d':=Int.zero) in Xi. inv Xi. 2: repeat rewrite Zlength_map; omega.
    rewrite Znth_map with (d':=Z0). 2: rewrite Zlength_map; omega.
    rewrite Znth_map with (d':=Byte.zero). 2: omega. 
    remember (Byte.xor (byte_at mInit (Zlength l+q) mbytes) 
                       (Znth (Zlength l) xbytes Byte.zero)) as mybyte.
    Exists (l++ [mybyte]). cancel.
    apply andp_right.
    - apply prop_right. 
      eapply (bxorlist_snoc mInit q (eval_id _m rho) mybyte l); trivial; omega.
    - autorewrite with sublist.
      rewrite field_address_offset by auto with field_compatible.
      simpl. rewrite isptr_offset_val_zero; trivial.
      apply derives_refl'. f_equal. unfold Bl2VL. subst mybyte. clear.
      repeat rewrite map_app. rewrite <- app_assoc. f_equal. simpl.
      f_equal.
      repeat rewrite zero_ext_inrange; try rewrite xor_byte_int; try rewrite Int.unsigned_repr; trivial;
        try apply Byte.unsigned_range_2;
        try apply byte_unsigned_range_3.
      assert (X:Int64.unsigned b - Zlength l - 1 = Int64.unsigned b - (Zlength l + 1)) by omega.
      rewrite X; trivial.
  }
Unfocus.
intros. apply andp_left2. rewrite Zminus_diag, list_repeat_0.
apply assert_lemmas.normal_ret_assert_derives'. entailer!. Intros l. rewrite app_nil_r. Exists l.
 entailer!. 
Qed.


(*TODO: refine non-zero-case of this spec, relating COUT to mCont and K and Nonce*)
Definition crypto_stream_xor_postsep b Nonce K mCont cLen nonce c k m :=
  (if Int64.eq b Int64.zero 
   then data_at_ Tsh (Tarray tuchar cLen noattr) c
   else (EX COUT:_, data_at Tsh (Tarray tuchar cLen noattr) COUT c))
                    * SByte Nonce nonce * ThirtyTwoByte K k
                    * message_at mCont m (*data_at Tsh (tarray tuchar mLen) mCont m*).

(*Precondition length mCont = Int64.unsigned b comes from textual spec in
  https://download.libsodium.org/doc/advanced/salsa20.html
  TODO: support the following part of the tetxual spec:
      m and c can point to the same address (in-place encryption/decryption). 
     If they don't, the regions should not overlap.*)
Definition crypto_stream_salsa20_xor_spec :=
  DECLARE _crypto_stream_salsa20_tweet_xor
   WITH c : val, k:val, m:val, nonce:val, b:int64,
        Nonce : SixteenByte, K: SixteenByte * SixteenByte,
        mCont: list byte, SV:val
   PRE [ _c OF tptr tuchar, _m OF tptr tuchar, _b OF tulong,
         _n OF tptr tuchar, _k OF tptr tuchar]
      PROP (Zlength mCont = Int64.unsigned b)
      LOCAL (temp _c c; temp _m m; temp _b (Vlong b);
             temp _n nonce; temp _k k; gvar _sigma SV)
      SEP ( SByte Nonce nonce;
            data_at_ Tsh (Tarray tuchar (Int64.unsigned b) noattr) c;
            ThirtyTwoByte K k;
            Sigma_vector SV;
            message_at mCont m
            (*data_at Tsh (tarray tuchar (Zlength mCont)) (Bl2VL mCont) m*))
  POST [ tint ] 
       PROP ()
       LOCAL (temp ret_temp (Vint (Int.repr 0)))
       SEP (Sigma_vector SV; 
            crypto_stream_xor_postsep b Nonce K mCont (Int64.unsigned b) nonce c k m). 
            
(*
Definition joinMXC i (mCont xCont: list int) (cCont: list val):=
   bind (xorlist (firstn i mCont) (firstn i xCont)) (fun l => Some (map Vint l ++ skipn i cCont)).
*)

Fixpoint ZCont (r: nat) (zcont: list byte): list byte := 
  match r with
     O => zcont
   | S n => let zb := ZCont n zcont in 
            let zz := ZZ zb (8:nat) in snd zz
  end.

Lemma ZCont0 bytes: ZCont O bytes = bytes. reflexivity. Qed.
Lemma ZContS bytes n: ZCont (S n) bytes = snd (ZZ (ZCont n bytes) 8). reflexivity. Qed.
Opaque ZCont.

Lemma crypto_stream_salsa20_xor_ok: semax_body SalsaVarSpecs SalsaFunSpecs
      f_crypto_stream_salsa20_tweet_xor
      crypto_stream_salsa20_xor_spec.
Proof. 
start_function.
name c' _c.
name m' _m.
name b' _b.
name n' _n.
name k' _k.
abbreviate_semax.
rename lvar0 into z.
rename lvar1 into x.
rename H into MLEN.
assert_PROP (isptr z) by entailer!. rename H into isptrZ.
forward_if
  (PROP  (b <> Int64.zero)
   LOCAL  (lvar _x (tarray tuchar 64) x; lvar _z (tarray tuchar 16) z;
   temp _c c; temp _m m; temp _b (Vlong b); temp _n nonce; temp _k k; gvar _sigma SV)
   SEP  (data_at_ Tsh (tarray tuchar 16) z;
   data_at_ Tsh (tarray tuchar 64) x; SByte Nonce nonce;
   data_at_ Tsh (Tarray tuchar (Int64.unsigned b) noattr) c; ThirtyTwoByte K k;
   Sigma_vector SV; message_at mCont m
   (*data_at Tsh (tarray tuchar (Zlength mCont)) (Bl2VL mCont) m*))).
{ unfold typed_true, strict_bool_val in H. simpl in H. 
  unfold eval_unop in H. simpl in H.
  specialize (Int64.eq_spec b Int64.zero). intros.
  destruct (Int64.eq b Int64.zero); simpl in *. 2: inv H.
  clear H.
Check 
Ltac mkConciseDelta V G F Delta :=
  let vv := constr:(filter (is_init_temp Delta) (map fst (fn_temps F))) in
    let inits := (eval simpl in vv) in
    change Delta with (initialized_list inits (func_tycontext F V G)). (*;
    refold_temp_names F;
  clear Delta.*)
(*
mkConciseDelta SalsaVarSpecs SalsaFunSpecs
      f_crypto_stream_salsa20_tweet_xor Delta. *)
  forward. Exists x z. entailer!. 
  unfold crypto_stream_xor_postsep. 
  rewrite Int64.eq_true. cancel. }
{ unfold typed_false, strict_bool_val in H. simpl in H.
  unfold eval_unop in H. simpl in H.
  specialize (Int64.eq_spec b Int64.zero). intros.
  destruct (Int64.eq b Int64.zero); simpl in *. inv H.
  clear H.  
  forward. Time entailer!. }
Intros. rename H into B.
freeze [1;2;3;4;5;6] FR1.
forward_for_simple_bound 16 (EX i:Z, 
  (PROP  ()
   LOCAL  (lvar _x (tarray tuchar 64) x; lvar _z (tarray tuchar 16) z;
   temp _c c; temp _m m; temp _b (Vlong b); temp _n nonce; temp _k k; gvar _sigma SV)
   SEP  (FRZL FR1; EX l:_, !!(Zlength l + i = 16) && data_at Tsh (tarray tuchar 16) 
          ((list_repeat (Z.to_nat i) (Vint Int.zero)) ++ l) z))).
{ Exists (list_repeat 16 Vundef). entailer!. }
{ rename H into I. Intros l. rename H into LI16.
  forward. Exists (sublist 1 (Zlength l) l). entailer!.
    rewrite Zlength_sublist; omega.
  rewrite field_at_data_at. rewrite field_address_offset by auto with field_compatible. 
  simpl. rewrite isptr_offset_val_zero; trivial.
  apply derives_refl'. f_equal. 
  rewrite Z2Nat.inj_add, <- list_repeat_app, <- app_assoc; try omega. 
  rewrite upd_Znth_app2.
  rewrite Zlength_list_repeat, Zminus_diag, upd_Znth0. reflexivity. omega.
  repeat rewrite Zlength_list_repeat; omega. 
}
Intros l. destruct l.
2: specialize (Zlength_nonneg l); intros;
         rewrite Zlength_cons', Z.add_comm, Z.add_assoc in H; omega.
clear H. rewrite app_nil_r.
thaw FR1.
freeze [0;2;3;4;5] FR2.
unfold SByte.
forward_for_simple_bound 8 (EX i:Z, 
  (PROP  ()
   LOCAL  (lvar _x (Tarray tuchar 64 noattr) x;
   lvar _z (Tarray tuchar 16 noattr) z; temp _c c; temp _m m;
   temp _b (Vlong b); temp _n nonce; temp _k k; gvar _sigma SV)
   SEP 
   (FRZL FR2; data_at Tsh (Tarray tuchar 16 noattr)
        (sublist 0 i (SixteenByte2ValList Nonce) ++
         (list_repeat (Z.to_nat (16-i)) (Vint Int.zero))) z;
   data_at Tsh (Tarray tuchar 16 noattr) (SixteenByte2ValList Nonce) nonce))).
{ entailer!. }
{ rename H into I.
  assert (ZWS: Int.zwordsize = 32) by reflexivity.
  destruct (SixteenByte2ValList_bytes Nonce) as [NBytes [NBytesL NB]]; rewrite NB.
  assert (NBytesZL: Zlength NBytes = 16). apply Zlength_length; simpl; omega.
  destruct (Znth_mapVint (map Int.repr (map Byte.unsigned NBytes)) i Vundef) as [v V]. 
    repeat rewrite Zlength_map. rewrite NBytesZL. omega. 
  assert (v = Int.repr (Byte.unsigned (Znth i NBytes Byte.zero))).
    rewrite Znth_map' with (d':=Int.zero) in V. inv V. 
    2: repeat rewrite Zlength_map; rewrite NBytesZL; simpl; omega.
    rewrite Znth_map' with (d':=Z0).
    2: rewrite Zlength_map, NBytesZL; simpl; omega.
    rewrite Znth_map' with (d':=Byte.zero). reflexivity.
    rewrite NBytesZL; simpl; omega.
  subst v.
  destruct (Byte.unsigned_range_2 (Znth i NBytes Byte.zero)) as [VBmin VBmax]. 
  specialize Byte_max_unsigned_Int_max_unsigned; intros ByteIntMaxUnsigned.
  simpl.
  forward; rewrite V.
  { entailer!.
    rewrite zero_ext_inrange. 
      rewrite Int.unsigned_repr; trivial; omega.
      rewrite Int.unsigned_repr; trivial; omega.
  }
  simpl; rewrite zero_ext_inrange. 
  2: rewrite Int.unsigned_repr; trivial; omega.
  forward.
  rewrite NB.
  entailer!.
  rewrite field_at_data_at. rewrite field_address_offset by auto with field_compatible. 
  simpl. rewrite isptr_offset_val_zero; trivial.
  apply derives_refl'. f_equal.
  rewrite upd_Znth_app2; try autorewrite with sublist. 2: omega.
  rewrite upd_Znth0, <- (@sublist_rejoin val 0 i (i+1)), <- app_assoc. f_equal.
  rewrite <- Znth_cons_sublist with (d:=Vundef).
  f_equal. rewrite Znth_map' with (d':=Int.zero).
     rewrite Znth_map' with (d':=Z0).
     rewrite Znth_map' with (d':=Byte.zero); trivial.
     omega. rewrite Zlength_map; omega. repeat rewrite Zlength_map; omega.
     autorewrite with sublist. rewrite  Z.sub_add_distr; trivial.
     autorewrite with sublist in *. omega.
     omega. 
     autorewrite with sublist in *. omega.
}
drop_LOCAL 0%nat. (*remove temp i*)
(*freeze [2] FULLNONCE.*)
(*
(*Verification of loop while (b >=64) ...*)
Parameter merge : list byte -> SixteenByte * SixteenByte -> list val.
(*Definition WHILE (r:nat) mC K cC :=
    firstn (r * 64)%nat cC = merge (firstn (r * 64)%nat mC) K.
  (*TODO: add that all asigned-to locations in c are bytes*)*)
Parameter WHILE : nat -> list byte -> SixteenByte * SixteenByte -> list val -> Prop.*)
          
rename c into cInit. rename m into mInit. rename b into bInit.
Parameter CCont: (* rounds:*) nat -> list val.
Axiom CCont0: CCont O = nil.
(*Parameter ZCont: (*zcont:*) SixteenByte ->  (* rounds:*) nat -> SixteenByte.
Axioms ZCont0: forall zcont, ZCont zcont O = zcont.
*)
(*Parameter MCont: (*mCont :*) list byte -> (* rounds:*) nat -> list byte.
Axioms MCont0: forall mcont, MCont mcont O = mcont.*)

Definition Inv cInit mInit bInit k nonce x z Nonce K SV mcont zcont:=
(EX rounds:nat, EX m:_, EX d:_,
 let r64 := (Z.of_nat rounds * 64)%Z in
 let c := offset_val (Int.repr r64) cInit in
(* let m := offset_val (Int.repr r64) mInit in*)
 (*let m := match mInit with
            Vint i => nullval
          | _ => offset_val (Int.repr r64) mInit
          end in*)
 let b := Int64.sub bInit (Int64.repr r64) in
  (PROP  ((*WHILE rounds mCont K cCont /\ *)
          (*Z.of_nat rounds * 64 <= Zlength mcont /\*)
          (*length cCont = (rounds * 64)%nat*)
          (*Int64.ltu (Int64.repr (Z.of_nat rounds * 64)) bInit = true*)
          0 <= r64 <= Int64.unsigned bInit /\ null_or_offset mInit r64 m
          /\ SixteenByte2ValList d = Bl2VL (ZCont rounds zcont))
   LOCAL  (lvar _x (Tarray tuchar 64 noattr) x;
           lvar _z (Tarray tuchar 16 noattr) z; temp _c c; temp _m m;
           temp _b (Vlong b); temp _n nonce; temp _k k; gvar _sigma SV)
   SEP 
   (data_at Tsh (Tarray tuchar 16 noattr)
        (*(SixteenByte2ValList  (ZCont zcont rounds)) z*)
        (Bl2VL (ZCont rounds zcont)) z;
   data_at_ Tsh (Tarray tuchar 64 noattr) x; Sigma_vector SV;
   data_at Tsh (Tarray tuchar 16 noattr) (SixteenByte2ValList Nonce) nonce;
   ThirtyTwoByte K k; 

   data_at Tsh (Tarray tuchar  (Z.of_nat rounds * 64) noattr) (CCont rounds) cInit;
   data_at_ Tsh (Tarray tuchar (Int64.unsigned bInit - Z.of_nat rounds * 64) noattr) c;
   message_at mcont mInit
   (*data_at Tsh (Tarray tuchar (Zlength mcont - Z.of_nat rounds * 64) noattr)
               (sublist (Z.of_nat rounds * 64)%Z (Zlength mcont) (Bl2VL mcont)) m;
   data_at_ Tsh (Tarray tuchar (Z.of_nat rounds * 64) noattr) mInit*)))).

  remember ((Byte.zero, Byte.zero, Byte.zero, Byte.zero):QuadByte) as ZeroQuadByte.
  destruct Nonce as [[[N0 N1] N2] N3].
  assert (sublist 0 8 (SixteenByte2ValList (N0, N1, N2, N3)) ++
       list_repeat (Z.to_nat (16 - 8)) (Vint Int.zero)
     = (SixteenByte2ValList (((N0, N1), ZeroQuadByte), ZeroQuadByte))).
  { do 2 rewrite SixteenByte2ValList_char. 
    rewrite app_assoc, sublist_app1; try omega. 
        2: rewrite Zlength_app; do 2 rewrite Zlength_correct, QuadByteValList_length; simpl; omega.
    rewrite sublist_same; try omega. 
        2: rewrite Zlength_app; do 2 rewrite Zlength_correct, QuadByteValList_length; simpl; omega.
    subst ZeroQuadByte. simpl. rewrite Byte.unsigned_zero. rewrite <- app_assoc. reflexivity. }
  rewrite H; clear H.
  assert (Int64.max_unsigned = 18446744073709551615) by reflexivity. rename H into I64MAX.
  (*destruct (SixteenByte2ValList_bytes (N0, N1, N2, N3)) as [nbytes [Lnbytes NBytes]].
  rewrite NBytes.*) 
  destruct (SixteenByte2ValList_bytes (N0, N1, ZeroQuadByte, ZeroQuadByte)) as [zbytes [Lzbytes ZBytes]].
  rewrite ZBytes.
forward_while (Inv cInit mInit bInit k nonce x z (N0, N1,N2,N3) K SV mCont zbytes).
{ (*precondition*)
  Exists O mInit. Exists (N0, N1, ZeroQuadByte, ZeroQuadByte).
  rewrite ZCont0, (*MCont0,*) CCont0. 
  destruct (Int64.unsigned_range bInit). 
  specialize (Zlength_nonneg mCont); intros. unfold Bl2VL.
  thaw FR2.
  entailer!.
  rewrite Int64.sub_zero_l; split; trivial.
  destruct m'; inv TC2; simpl. split; reflexivity. rewrite Int.add_zero; trivial.
  rewrite Zminus_0_r. unfold tarray.
   autorewrite with sublist. cancel.
(*   rewrite Tarray_0_emp_iff_; auto with field_compatible.*)
   rewrite Tarray_0_emp_iff; auto with field_compatible.
(*   cancel.*)
}
{ entailer!. }
{ remember (Z.of_nat rounds * 64)%Z as r64.
  apply Int64_ltu_false in HRE; rewrite Int64.unsigned_repr in HRE. 2: omega.
  destruct (zle (r64 + 64) (Int64.unsigned bInit)).
  Focus 2. exfalso. assert (X: 64 > Int64.unsigned bInit - r64) by omega. clear g.
           destruct (Int64.unsigned_range_2 bInit) as [X1 X2].
           unfold Int64.sub in HRE. rewrite (Int64.unsigned_repr r64) in HRE. 2: omega.
           rewrite Int64.unsigned_repr in HRE; omega.
  destruct H as [R64old [M D]]. rename l into R64next.
   
  forward_call (SV, k, z, x, (d, SIGMA, K)). 
  { unfold CoreInSEP, SByte, Sigma_vector, tarray. rewrite D; cancel. }
Intros snuff. rename H into Snuff.

destruct (QuadChunks2ValList_bytes (map littleendian_invert snuff)) as [sr_bytes [SRBL SNR]].
assert (Zlength sr_bytes = 64).
  rewrite map_length, (Snuffle20_length _ _ Snuff) in SRBL.
  rewrite Zlength_correct, SRBL. reflexivity.
  apply prepare_data_length.
rename H into SRL.
freeze [0;2;3] FR3.
remember (offset_val (Int.repr r64) cInit) as c.

assert(INT64SUB: Int64.sub bInit (Int64.repr (r64 + 64)) =
           Int64.sub (Int64.sub bInit (Int64.repr r64)) (Int64.repr 64)).
{ clear - R64next R64old HRE Heqr64 I64MAX.
  destruct (Int64.unsigned_range_2 bInit).
  unfold Int64.sub.
  repeat rewrite Int64.unsigned_repr; try omega. f_equal; omega.
} 

assert_PROP (isptr c) as C by entailer!.
rewrite SNR.
forward_seq. (*
mkConciseDelta SalsaVarSpecs SalsaFunSpecs
      f_crypto_stream_salsa20_tweet_xor Delta.
eapply semax_extensionality_Delta.*)
  apply (loop1 Espec (FRZL FR3) x z c mInit (Vlong (Int64.sub bInit (Int64.repr r64))) nonce k m sr_bytes mCont).
    eassumption. (* subst m. destruct mInit; simpl in MI; try contradiction. split; trivial. reflexivity.*)
    clear - SRL R64next R64old HRE Heqr64 MLEN. rewrite MLEN. omega. omega.

(*continuation after the FOR(i,64) loop*)
drop_LOCAL 0%nat.
Intros xorlist. rename H into XOR.
forward.
thaw FR3. unfold CoreInSEP. repeat flatten_sepcon_in_SEP.
freeze [1;2;3;4;5;6;7;8] FR4.
unfold SByte. (*
destruct (SixteenByte2ValList_bytes (ZCont (N0, N1, ZeroQuadByte, ZeroQuadByte) rounds)) as [zbytes [Lzbytes Hzbytes]].
rewrite Hzbytes.*)
(*mkConciseDelta SalsaVarSpecs SalsaFunSpecs
      f_crypto_stream_salsa20_tweet_xor Delta.*) 
forward_seq. rewrite D.
  apply (For_i_8_16_loop Espec (FRZL FR4) x z c m 
           (Vlong (Int64.sub bInit (Int64.repr r64))) nonce k SV (ZCont rounds zbytes)).
freeze [0;1] FR5.
forward.
forward.
rewrite Heqc. simpl.
forward_if (EX m:_,
  (PROP  (null_or_offset mInit (r64+64) m)
   LOCAL 
   (temp _c
      (force_val
         (sem_add_pi tuchar (offset_val (Int.repr r64) cInit)
            (Vint (Int.repr 64))));
   temp _b
     (Vlong
        (Int64.sub (Int64.sub bInit (Int64.repr r64))
           (Int64.repr (Int.signed (Int.repr 64)))));
   lvar _x (Tarray tuchar 64 noattr) x; lvar _z (Tarray tuchar 16 noattr) z;
   temp _m m; temp _n nonce; temp _k k; gvar _sigma SV)  SEP  (FRZL FR5))).
{  clear H v. apply denote_tc_comparable_split.
   destruct mInit; simpl in M; try contradiction.
   destruct M as [II M]; rewrite M in *.
     apply valid_pointer_null.
   rewrite M in *.
     thaw FR5; thaw FR4. apply sepcon_valid_pointer1. apply sepcon_valid_pointer2.
        apply sepcon_valid_pointer2.  apply sepcon_valid_pointer2.  apply sepcon_valid_pointer2.
         apply sepcon_valid_pointer2.  apply sepcon_valid_pointer1. entailer!.
        unfold message_at. eapply derives_trans. apply data_at_memory_block.
        eapply derives_trans. apply memory_block_valid_pointer. simpl.
        3: apply derives_refl'. 3: reflexivity.
        rewrite Z.max_r. omega. apply Zlength_nonneg.
        apply top_share_nonidentity.
     apply valid_pointer_null.
}
{ forward. Exists (force_val (sem_add_pi tuchar m (Vint (Int.repr 64)))). entailer!.
  destruct mInit; simpl in M; try contradiction.
  destruct M as [II M]; rewrite M in *. contradiction. 
  rewrite M in *.  simpl. rewrite Int.add_assoc, add_repr. trivial. }
{ forward. Exists m. entailer!. destruct mInit; simpl in M; try contradiction.
  simpl. apply M. inv M. }
intros.
apply andp_left2. unfold overridePost. if_tac. 2: trivial.
destruct cInit; simpl in Heqc; rewrite Heqc in C; try contradiction.
subst ek.
unfold POSTCONDITION, abbreviate. entailer!. rewrite Int.add_assoc in H0.

assert (DD: exists dd, SixteenByte2ValList dd = Bl2VL (ZCont (S rounds) zbytes)). admit. (*TODO*)
destruct DD as [dd DD].

  Exists (S rounds, eval_id _m rho, dd).
  entailer!. rewrite  Nat2Z.inj_succ, <- Zmult_succ_l_reverse, <- H0, <- Heqr64, <- H1.
  rewrite Int.signed_repr, INT64SUB; trivial.
  intuition. 
  unfold Int.min_signed, Int.max_signed; simpl; omega.
  thaw FR5; thaw FR4. unfold SByte, Sigma_vector. subst c nonce k; cancel.

  assert (Zlength xorlist = 64).
     unfold bxorlist in XOR; destruct (combinelist_Zlength _ _ _ _ _ XOR).
     autorewrite with sublist in H5. rewrite H4. unfold bytes_at. destruct mInit; autorewrite with sublist; trivial.
  assert (Zlength (Bl2VL xorlist) = 64). rewrite Zlength_Bl2VL; omega.

  erewrite (split2_data_at_Tarray_tuchar _ (Int64.unsigned bInit - r64) (Zlength (Bl2VL xorlist))).
  2: omega. 2: rewrite Zlength_app; autorewrite with sublist; omega.
  autorewrite with sublist. rewrite H5.
  destruct rounds; simpl in *. subst r64; simpl in *.
    rewrite CCont0. rewrite Tarray_0_emp_iff.
    assert ().
  destruct (beq_nat rounds O); simpl.
  unfold field_address0. simpl. autorewrite with sublist in *. 
  if_tac.
  assert (Int.add i (Int.repr (Z.pos (Pos.of_succ_nat rounds * 64))) = 
          Int.add (Int.add i (Int.repr r64)) (Int.repr 64)). 
    rewrite Int.add_assoc. f_equal. rewrite add_repr. f_equal. 
    subst r64. rewrite <- Pos.succ_of_nat, Pos.mul_succ_l, Pos2Z.inj_add, 
       <- initial_world.Zpos_Posofnat, Pos2Z.inj_mul.  omega.
    red in H. red in H7. simpl in H7.
    omega. Pos.of_nat_succ. unfold Pos.of_succ_nat. rewrite (Zpos_P_of_succ_nat rounds). omega.  2: admit. (*TODO*)  elim H7; clear H7.  try contradiction.
      rewrite Z.mul_1_l. cancel.



admit. (*data_at Tsh (Tarray tuchar r64 noattr) (CCont rounds) (Vptr b i) *
data_at Tsh (Tarray tuchar (Int64.unsigned bInit - r64) noattr)
  (Bl2VL xorlist ++
   list_repeat (Z.to_nat (Int64.unsigned bInit - r64 - 64)) Vundef)
  (Vptr b (Int.add i (Int.repr r64))) *
data_at Tsh (Tarray tuchar 16 noattr) (Bl2VL (snd (ZZ zbytes 8))) z
|-- data_at Tsh (Tarray tuchar 16 noattr)
      (SixteenByte2ValList
         (ZCont (N0, N1, ZeroQuadByte, ZeroQuadByte) (S rounds))) z *
    data_at Tsh (Tarray tuchar (r64 + 64) noattr) (CCont (S rounds))
      (Vptr b i) *
    data_at_ Tsh (Tarray tuchar (Int64.unsigned bInit - (r64 + 64)) noattr)
      (Vptr b (Int.add i (Int.repr (r64 + 64))))*)

}

(*continuation if (b) {...} *)
apply negb_false_iff in HRE.
apply Int64.ltu_inv in HRE.
rewrite Int64.unsigned_repr in HRE. 2: omega.
remember (Z.of_nat rounds * 64)%Z as r64.
  destruct (zle (r64 + 64) (Int64.unsigned bInit)).
  exfalso. assert (X: 64 <= Int64.unsigned bInit - r64) by omega. clear l.
           destruct (Int64.unsigned_range_2 bInit) as [X1 X2].
           unfold Int64.sub in HRE. rewrite (Int64.unsigned_repr r64) in HRE. 2: omega.
           rewrite Int64.unsigned_repr in HRE; omega.
  destruct H as [R64a M]. rename g into R64b. 
  assert (RR: Int64.unsigned (Int64.sub bInit (Int64.repr r64)) = Int64.unsigned bInit - r64).
  { destruct (Int64.unsigned_range_2 bInit).
    unfold Int64.sub.
    repeat rewrite Int64.unsigned_repr; try omega. }
Parameter IfPost: environ -> mpred.
(*freeze [0;2;3;4;5;8] FR3.*)
forward_if IfPost.
{ rename H into BR.
  forward_call (SV, k, z, x, 
                 (ZCont (((N0, N1), ZeroQuadByte), ZeroQuadByte) rounds, SIGMA, K)). 
  { unfold CoreInSEP, SByte, Sigma_vector, tarray. cancel. }
  Intros snuff. rename H into Snuff.
  destruct (QuadChunks2ValList_bytes (map littleendian_invert snuff)) as [sr_bytes [SRBL SNR]].
  assert (Zlength sr_bytes = 64).
    rewrite map_length, (Snuffle20_length _ _ Snuff) in SRBL.
    rewrite Zlength_correct, SRBL. reflexivity.
    apply prepare_data_length.
  rename H into SRL.
  freeze [0;2;3;6] FR1.
  remember (offset_val (Int.repr r64) cInit) as c.
  assert (BB: Int64.unsigned (Int64.sub bInit (Int64.repr r64)) < Int.max_unsigned). 
     solve [rewrite int_max_unsigned_eq; omega].
(*mkConciseDelta SalsaVarSpecs SalsaFunSpecs
      f_crypto_stream_salsa20_tweet_xor Delta.*)
(*  eapply semax_extensionality_Delta.*)
  rewrite SNR, <- RR.
  eapply semax_post.
  2: eapply (loop2 Espec (FRZL FR1) x z c mInit); try eassumption. 2: omega. 2: omega. 2: omega.
  intros. apply andp_left2. unfold POSTCONDITION, abbreviate. 
  rewrite normal_ret_assert_eq. entailer!. simpl. entailer!.
  unfold typed_true in BR. inversion BR; clear BR. rewrite RR in *. eapply negb_true_iff in H14. 
  unfold Int64.eq in H14. rewrite RR in H14. unfold Int64.zero in H14.
  rewrite Int64.unsigned_repr in H14. 2: omega.
  if_tac in H14. inv H14. clear H14.
 (*yields first half of definition of IfPost: Int64.unsigned bInit - r64 <> 0
______________________________________(1/2)
FRZL FR1 *
data_at Tsh (tarray tuchar 64)
  (map Vint (map Int.repr (map Byte.unsigned sr_bytes))) x *
message_at mCont mInit *
data_at Tsh (Tarray tuchar (Int64.unsigned bInit - r64) noattr) (Bl2VL l)
  (eval_id _c rho) |-- IfPost rho*)
   admit.
}
{ forward.
  unfold typed_false in H. inversion H; clear H. rewrite RR in *. eapply negb_false_iff in H1. 
  unfold Int64.eq in H1. rewrite RR in H1. unfold Int64.zero in H1.
  rewrite Int64.unsigned_repr in H1. 2: omega.
  if_tac in H1. 2: inv H1. clear H1. 
  assert (XX: Int64.unsigned bInit = r64) by omega.
  rewrite XX in *; clear XX RR H.
  entailer!. admit. (*Second half rewrite Zminus_diag, Tarray_0_emp_iff_. 
  Focus 2. clear - H13. red; red in H13.  simpl in *. unfold tarray; eassumption. simpl. rewrite field_address_offset by auto with field_compatible.  autorewrite with compatible. clear H14.
*)
}

admit. (*Once we have definition of IfPost, this yeilds definition of POSTCONDITION*)
Time Qed. (*121 secs*)