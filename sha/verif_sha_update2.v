Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Local Open Scope nat.
Local Open Scope logic.

Definition update_inner_if_then :=
  (Ssequence
      (Scall None
           (Evar _memcpy
              (Tfunction
                 (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                 (tptr tvoid) cc_default))
           [Ebinop Oadd (Etempvar _p (tptr tuchar)) (Etempvar _n tuint)
              (tptr tuchar); Etempvar _data (tptr tuchar);
           Etempvar _fragment tuint])
     (Ssequence
        (Scall None
           (Evar _sha256_block_data_order
              (Tfunction
                 (Tcons (tptr t_struct_SHA256state_st)
                    (Tcons (tptr tvoid) Tnil)) tvoid cc_default))
           [Etempvar _c (tptr t_struct_SHA256state_st);
           Etempvar _p (tptr tuchar)])
        (Ssequence
           (Sset _data
              (Ebinop Oadd (Etempvar _data (tptr tuchar))
                 (Etempvar _fragment tuint) (tptr tuchar)))
           (Ssequence
              (Sset _len
                 (Ebinop Osub (Etempvar _len tuint)
                    (Etempvar _fragment tuint) tuint))
                 (Scall None
                    (Evar _memset
                       (Tfunction
                          (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil)))
                          (tptr tvoid) cc_default))
                    [Etempvar _p (tptr tuchar); Econst_int (Int.repr 0) tint;
                    Ebinop Omul (Econst_int (Int.repr 16) tint)
                      (Econst_int (Int.repr 4) tint) tint]))))).

Definition  update_inner_if_else :=
                (Ssequence
                    (Scall None
                      (Evar _memcpy (Tfunction
                                      (Tcons (tptr tvoid)
                                        (Tcons (tptr tvoid)
                                          (Tcons tuint Tnil))) (tptr tvoid) cc_default))
                      ((Ebinop Oadd (Etempvar _p (tptr tuchar))
                         (Etempvar _n tuint) (tptr tuchar)) ::
                       (Etempvar _data (tptr tuchar)) ::
                       (Etempvar _len tuint) :: nil))
                  (Ssequence
                    (Sassign
                      (Efield
                        (Ederef (Etempvar _c (tptr t_struct_SHA256state_st))
                          t_struct_SHA256state_st) _num tuint)
                      (Ebinop Oadd (Etempvar _n tuint)
                        (Ecast (Etempvar _len tuint) tuint) tuint))
                    (Sreturn None))).

Definition update_inner_if :=
        Sifthenelse (Ebinop Oge (Etempvar _len tuint)
                             (Etempvar _fragment tuint) tint)
         update_inner_if_then
         update_inner_if_else.

Definition inv_at_inner_if sh hashed len c d dd data kv :=
 (PROP ()
   (LOCAL 
      (temp _fragment (Vint (Int.repr (64- Zlength dd)));
       temp _p (field_address t_struct_SHA256state_st [StructField _data] c);
       temp _n (Vint (Int.repr (Zlength dd)));
       temp _c c; temp _data d;
       temp _len (Vint (Int.repr (Z.of_nat len)));
       gvar  _K256 kv)
   SEP  (`(data_at Tsh t_struct_SHA256state_st
                 (map Vint (hash_blocks init_registers hashed),
                  (Vint (lo_part (bitlength hashed dd + (Z.of_nat len)*8)),
                   (Vint (hi_part (bitlength hashed dd + (Z.of_nat len)*8)),
                    (map Vint (map Int.repr dd),
                     Vint (Int.repr (Zlength dd))))))
               c);
   `(K_vector kv);
   `(data_block sh data d)))).

Definition sha_update_inv sh hashed len c d (dd: list Z) (data: list Z) kv (done: bool) :=
   (EX blocks:list int,
   PROP  (len >= length blocks*4 - length dd /\
              (LBLOCKz | Zlength blocks) /\ 
              intlist_to_Zlist blocks = dd ++ firstn (length blocks * 4 - length dd) data /\
             if done then len-(length blocks*4 - length dd) < CBLOCK else True)
   LOCAL  (temp _p (field_address t_struct_SHA256state_st [StructField _data]  c); temp _c c; 
                temp _data (offset_val (Int.repr (Z.of_nat (length blocks*4-length dd))) d);
                temp _len (Vint (Int.repr (Z.of_nat (len- (length blocks*4 - length dd)))));
                gvar  _K256 kv)
   SEP  (`(K_vector kv);
           `(data_at Tsh t_struct_SHA256state_st
                 (map Vint (hash_blocks init_registers (hashed++blocks)),
                  (Vint (lo_part (bitlength hashed dd + (Z.of_nat len)*8)),
                   (Vint (hi_part (bitlength hashed dd + (Z.of_nat len)*8)),
                    (nil, Vundef))))
                c);
   `(data_block sh data d))).

Definition Delta_update_inner_if : tycontext.
simplify_Delta_from
  (initialized _fragment
     (initialized _p
        (initialized _n
           (initialized _data (func_tycontext f_SHA256_Update Vprog Gtot))))).
Defined.

Require Import JMeq.

Definition splice_into_list (lo hi n : Z) (source target : list val) : list val :=
   firstn (Z.to_nat lo) (target ++ list_repeat (Z.to_nat (lo - Zlength target)) Vundef)
   ++ firstn (Z.to_nat (hi-lo)) (source ++ list_repeat (Z.to_nat (hi-lo)) Vundef)
   ++ firstn (Z.to_nat (n-hi)) (skipn (Z.to_nat hi) (target ++ list_repeat (Z.to_nat (n- Zlength target)) Vundef)).

Lemma splice_into_list_simplify0:
  forall n src dst, 
    Zlength src = n ->
    Zlength dst = n ->
    splice_into_list 0 n n src dst = src.
Proof.
 intros.
 unfold splice_into_list.
 rewrite Z.sub_0_r. change (Z.of_nat 0) with 0%nat.
 simpl firstn. unfold app at 1.
 rewrite firstn_app1.
 rewrite Z.sub_diag. change (Z.to_nat 0) with 0. simpl firstn. 
 rewrite firstn_same. rewrite <- app_nil_end; auto.
 rewrite <- H. rewrite Zlength_correct. rewrite Nat2Z.id; auto.
 rewrite <- H. rewrite Zlength_correct. rewrite Nat2Z.id; auto.
Qed.

Lemma splice_into_list_simplify1:
  forall lo hi src tgt,
    lo = Zlength tgt ->
    (hi-lo = Zlength src)%Z ->
    splice_into_list lo hi hi src tgt = tgt++src.
Proof.
intros; subst; unfold splice_into_list.
rewrite H0.
rewrite Z.sub_diag.
change (Z.to_nat 0) with 0.
unfold list_repeat at 1.
repeat rewrite ZtoNat_Zlength.
rewrite <- app_nil_end.
rewrite firstn_same by omega.
f_equal.
rewrite firstn_app1 by omega.
rewrite firstn_same by omega.
pose proof (Zlength_nonneg src).
pose proof (Zlength_nonneg tgt).
pose proof (skipn_length_short (Z.to_nat hi) tgt).
spec H2.
apply Nat2Z.inj_le.
rewrite <- Zlength_correct.
rewrite Z2Nat.id by omega.
omega.
destruct (skipn (Z.to_nat hi) tgt); inv H2.
rewrite Z.sub_diag.
change (Z.to_nat 0) with 0.
simpl. rewrite <- app_nil_end; auto.
Qed.

Lemma splice_into_list_simplify2:
  forall lo hi src tgt,
    lo = Zlength tgt ->
    (lo <= hi)%Z ->
    (hi-lo <= Zlength src)%Z ->
    splice_into_list lo hi hi src tgt = tgt++ firstn (Z.to_nat (hi-lo)) src.
Proof.
intros; subst; unfold splice_into_list.
repeat rewrite Z.sub_diag.
change (Z.to_nat 0) with 0.
unfold list_repeat at 1.
repeat rewrite ZtoNat_Zlength.
rewrite <- app_nil_end.
rewrite firstn_same by omega.
f_equal.
pose proof (Zlength_nonneg src).
pose proof (Zlength_nonneg tgt).
rewrite skipn_short.
rewrite <- app_nil_end.
rewrite firstn_app1; auto.
apply Nat2Z.inj_le.
rewrite <- Zlength_correct.
rewrite Z2Nat.id by omega.
auto.
rewrite app_length.
rewrite length_list_repeat.
rewrite <- (Nat2Z.id (length tgt)).
rewrite <- Zlength_correct. 
rewrite <- Z2Nat.inj_add by omega.
unfold ge.
rewrite <- Z2Nat.inj_le; try omega.
Qed.

Lemma JMeq_skipn:
  forall ta tb n (la: list ta) (lb: list tb),
     ta=tb ->
     JMeq la lb ->
     JMeq (skipn n la) (skipn n lb).
Proof.
intros. subst tb. apply JMeq_eq in H0. subst lb. auto.
Qed.

Lemma JMeq_firstn:
  forall ta tb n (la: list ta) (lb: list tb),
    ta=tb -> JMeq la lb -> JMeq (firstn n la) (firstn n lb).
Proof.
intros. subst tb. apply JMeq_eq in H0. subst lb. auto.
Qed.

Lemma JMeq_length:
  forall ta tb (la: list ta) (lb: list tb),
     ta=tb -> JMeq la lb -> length la = length lb.
Proof.
intros. subst tb.  apply JMeq_eq in H0. subst lb. auto.
Qed.

 Definition fsig_of_funspec (fs: funspec)  :=  
  match fs with mk_funspec fsig _ _ _ => fsig end.

Lemma firstn_splice_into_list:
  forall lo hi n al bl, 
    (0 <= lo <= Zlength bl)%Z ->
    firstn (Z.to_nat lo) (splice_into_list lo hi n al bl) = firstn (Z.to_nat lo) bl.
Proof.
 intros.
 assert (Z.to_nat lo <= length bl).
 destruct H;  apply Z2Nat.inj_le in H0; try omega.
 rewrite Zlength_correct in H0.
 rewrite Nat2Z.id in H0; auto.
 unfold splice_into_list.
 rewrite firstn_app1.
 pattern (Z.to_nat lo) at 2;  replace (Z.to_nat lo) with (Z.to_nat lo + 0) by omega.
 rewrite firstn_firstn.
 rewrite firstn_app1; auto.
 rewrite firstn_app1; auto.
 rewrite firstn_length, min_l; auto.
Qed. 


Lemma length_splice_into_list:
  forall lo hi n al bl, 
    (0 <= lo <= hi)%Z -> (hi <= n)%Z ->
    Zlength (splice_into_list lo hi n al bl) = n.
Proof.
intros.
unfold splice_into_list.
rewrite Zlength_correct.
repeat rewrite app_length.
rewrite firstn_length, min_l.
rewrite firstn_length, min_l.
rewrite firstn_length, min_l.
rewrite <- Z2Nat.inj_add; try omega.
rewrite <- Z2Nat.inj_add; try omega.
rewrite Z2Nat.id; try omega.
rewrite skipn_length.
destruct (zlt n (Zlength bl)).
rewrite (Z2Nat_nonpos_0 (n - Zlength bl)) by omega.
unfold list_repeat; simpl; rewrite <- app_nil_end.
rewrite <- (Nat2Z.id (length bl)).
rewrite <- Zlength_correct.
rewrite <- Z2Nat.inj_sub by omega.
   apply Z2Nat.inj_le; omega.
rewrite app_length.
rewrite length_list_repeat.
rewrite Z2Nat.inj_sub by omega.
rewrite <- (Nat2Z.id (length bl)).
rewrite <- Zlength_correct.
rewrite <- Z2Nat.inj_sub by omega.
rewrite <- Z2Nat.inj_add; try omega.
rewrite <- Z2Nat.inj_sub by omega.
   apply Z2Nat.inj_le; omega.
apply Zlength_nonneg.
rewrite app_length.
rewrite length_list_repeat.
omega.
rewrite app_length.
rewrite length_list_repeat.
rewrite <- (Nat2Z.id (length bl)).
rewrite <- Zlength_correct.
destruct (zlt lo (Zlength bl)).
rewrite (Z2Nat_nonpos_0 (_ - _)) by omega.
rewrite NPeano.Nat.add_0_r.
   apply Z2Nat.inj_le; omega.
rewrite <- Z2Nat.inj_add; try omega.
   apply Z2Nat.inj_le; omega.
apply Zlength_nonneg.
Qed.

Lemma call_memcpy_tuchar:
  forall (shp : share) (tp: type) (pathp: list gfield) (lop: Z) (vp': list val) (p: val)
           (shq: share) (tq: type) (pathq: list gfield) (loq: Z) (contents: list int) (q: val)
           (len : Z)
           (R': list (environ -> mpred))
           (np nq : Z)
           (vp vp'': reptype (nested_field_type2 tp pathp))
           (vq : reptype (nested_field_type2 tq pathq))
           (e_p e_q e_n : expr)
           Espec Delta P Q R,
      typeof e_p = tptr tuchar ->
      typeof e_q = tptr tuchar ->
      typeof e_n = tuint ->
      (var_types Delta) ! _memcpy = None ->
     (glob_specs Delta) ! _memcpy = Some (snd memcpy_spec) ->
     (glob_types Delta) ! _memcpy = Some (type_of_funspec (snd memcpy_spec)) ->
     writable_share shp ->
     nested_field_type2 tp pathp = tarray tuchar np ->
     nested_field_type2 tq pathq = tarray tuchar nq ->
     (0 <= lop)%Z -> (0 <= len <= Int.max_unsigned)%Z ->
     (lop <= Zlength vp' <= np)%Z ->
     (lop + len <= np)%Z ->
     (0 <= loq)%Z ->  (loq + len <=  Zlength contents <= nq)%Z ->
     JMeq vq (map Vint contents) ->
     JMeq vp vp' ->
     JMeq vp'' (splice_into_list lop (lop+len) np (skipn (Z.to_nat loq) (map Vint contents)) vp') ->
     PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
         PROP () (LOCALx
                (tc_exprlist Delta [tptr tvoid; tptr tvoid; tuint] [e_p; e_q; e_n] ::
                 `(eq (field_address tp (ArraySubsc lop :: pathp) p)) (eval_expr e_p) ::
                 `(eq (field_address tq (ArraySubsc loq :: pathq) q)) (eval_expr e_q) ::
                 `(eq (Vint (Int.repr len))) (eval_expr e_n) ::
                 Q)
         (SEPx (`(field_at shp tp pathp vp p) :: 
                   `(field_at shq tq pathq vq q) :: R'))) ->
   @semax Espec Delta 
    (PROPx P (LOCALx Q (SEPx R)))
    (Scall None
             (Evar _memcpy 
               (Tfunction
                (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                  (tptr tvoid) cc_default))
              [e_p; e_q; e_n])
    (normal_ret_assert (PROPx P (LOCALx Q 
     (SEPx (`(field_at shp tp pathp vp'' p) :: 
               `(field_at shq tq pathq vq q) :: R'))))).
Proof.
intros until R.
intros TCp TCq TCn Hvar Hspec Hglob ? ? ? Hlop Hlen Hvp' Hnp Hloq Hnq; intros.
assert_PROP (fold_right and True P); [ entailer | ].
eapply semax_pre; [ eassumption | ].
apply semax_post' with
   (PROPx nil   (LOCALx Q
           (SEPx
              (`(field_at shp tp pathp vp'' p)
               :: `(field_at shq tq pathq vq q) :: R'))));
 [ entailer | ].
clear H5 H6 P R.
assert (He: exists (vpe: reptype (nested_field_type2 tp pathp)),
               JMeq vpe (vp' ++ list_repeat (Z.to_nat (np - Zlength vp')) Vundef)).
 rewrite H0.
 econstructor. apply eq_JMeq. reflexivity.
destruct He as [vpe He].
rewrite (field_at_data_equal shp tp pathp vp vpe).
Focus 2. {
eapply (data_equal_JMeq (tarray tuchar np)); auto.
symmetry; apply H3.
symmetry; apply He.
apply data_equal_list_repeat_default.
} Unfocus.
assert (reptype (tarray tuchar np) = list val) by reflexivity.
rewrite <- H0 in H5.
assert (H99: reptype (nested_field_type2 tp (ArraySubsc 0 :: pathp)) = val).
 clear - H0. unfold nested_field_type2 in *; simpl in *.
  destruct (nested_field_rec tp pathp); inv H0. destruct p. subst.
 reflexivity.
assert (exists vpx : list (reptype (nested_field_type2 tp (ArraySubsc 0 :: pathp))),
                    JMeq vpe vpx).
rewrite H99. rewrite <- H5. exists vpe; auto.
destruct H6 as [vpx Hvpx].
rewrite (array_seg_reroot_lemma shp tp pathp tuchar np
              noattr lop (lop+len) (firstn (Z.to_nat lop) vpx)
                  (firstn (Z.to_nat len) (skipn (Z.to_nat lop) vpx))
                  (skipn (Z.to_nat lop + Z.to_nat len) vpx)
                  (firstn (Z.to_nat len) (skipn (Z.to_nat lop)
                              (vp'  ++ list_repeat (Z.to_nat (np - Zlength vp')) Vundef)))
                  ); auto; try omega.
2: apply JMeq_firstn; auto ; apply JMeq_skipn; auto.
2:  apply JMeq_trans with (y:= vpe); auto.
Focus 2. {
 apply JMeq_trans with (y:= vpx); auto.
 rewrite <- skipn_skipn.
 rewrite firstn_skipn. rewrite firstn_skipn. auto.
} Unfocus.
Focus 2.  {
rewrite Zlength_correct. rewrite firstn_length. rewrite min_l.
rewrite Z2Nat.id by omega; auto.
apply le_trans with (length vp').
rewrite <- (Nat2Z.id (length vp')).
apply Z2Nat.inj_le; try omega. rewrite <- Zlength_correct; omega.
clear - Hvpx He H99.
replace (length vpx) with (length (vp' ++ list_repeat (Z.to_nat (np - Zlength vp')) Vundef)).
rewrite app_length; omega.
apply JMeq_length; auto.
apply JMeq_trans with (y:=vpe); auto.
} Unfocus.
Focus 2. {
rewrite Zlength_correct.
rewrite firstn_length. rewrite min_l. rewrite Z2Nat.id by omega. omega.
rewrite skipn_length.
replace (length vpx) with (Z.to_nat (Zlength (vp' ++ list_repeat (Z.to_nat (np - Zlength vp')) Vundef))).
rewrite <- Z2Nat.inj_sub by omega.
apply Z2Nat.inj_le; try omega.
rewrite Zlength_app.
rewrite (Zlength_correct (list_repeat _ _)). omega.
rewrite Zlength_app. 
rewrite (Zlength_correct (list_repeat _ _)).
rewrite length_list_repeat.
destruct (zlt (lop+len) (Zlength vp') ).
omega.
rewrite Z2Nat.id; try omega.
rewrite Zlength_correct. rewrite Nat2Z.id.
apply JMeq_length; auto.
apply JMeq_trans with (y:=vpe); auto.
} Unfocus.
assert (H98: reptype (nested_field_type2 tq (ArraySubsc 0 :: pathq)) = val).
 clear - H1. unfold nested_field_type2 in *; simpl in *.
  destruct (nested_field_rec tq pathq); inv H1. destruct p. subst.
 reflexivity.
assert (exists vqx : list (reptype (nested_field_type2 tq (ArraySubsc 0 :: pathq))),
                    JMeq vq vqx).
 rewrite H98. exists (map Vint contents); auto.
destruct H6 as [vqx Hvqx].
assert (JMeq vqx (map Vint contents)) by (etransitivity; try eassumption; auto).
rewrite (array_seg_reroot_lemma shq tq pathq tuchar nq
              noattr loq (loq+len) (firstn (Z.to_nat loq) vqx)
                  (firstn (Z.to_nat len) (skipn (Z.to_nat loq) vqx))
                  (skipn (Z.to_nat loq + Z.to_nat len) vqx)
                  (firstn (Z.to_nat len) (skipn (Z.to_nat loq) (map Vint contents)))
                  ); auto; try omega.
2: apply JMeq_firstn; auto; apply JMeq_skipn; auto.
2: eapply JMeq_trans; [ | symmetry; eassumption];
  rewrite <- skipn_skipn, firstn_skipn, firstn_skipn; reflexivity.
Focus 2.  {
rewrite Zlength_correct. rewrite firstn_length. rewrite min_l.
rewrite Z2Nat.id by omega; auto.
replace (length vqx) with (length (map Vint contents)).
rewrite <- (Nat2Z.id (length (map Vint contents))).
apply Z2Nat.inj_le; try omega. rewrite map_length, <- Zlength_correct; omega.
apply JMeq_length; auto.
} Unfocus.
Focus 2. {
rewrite Zlength_correct.
rewrite firstn_length. rewrite min_l. rewrite Z2Nat.id by omega. omega.
rewrite skipn_length.
replace (length vqx) with (Z.to_nat (Zlength (map Vint contents))).
rewrite <- Z2Nat.inj_sub by omega.
rewrite Zlength_map.
apply Z2Nat.inj_le; omega. 
rewrite Zlength_correct. rewrite Nat2Z.id.
apply JMeq_length; auto.
} Unfocus.

normalize.
rewrite sepcon_assoc.
rewrite <- sepcon_comm.
rewrite flatten_sepcon_in_SEP.
rewrite flatten_sepcon_in_SEP.
pose (witness := ((shq,shp),
                              field_address tp (ArraySubsc lop :: pathp) p,
                              field_address tq (ArraySubsc loq :: pathq) q,
                              len,  (firstn (Z.to_nat len)
                 (skipn (Z.to_nat loq) contents)))).
pose (Frame := 
         `(array_at shp tp pathp (lop + len) np
              (skipn (Z.to_nat lop + Z.to_nat len) vpx) p)
          :: `(array_at shp tp pathp 0 lop (firstn (Z.to_nat lop) vpx) p)
             :: `(array_at shq tq pathq 0 loq (firstn (Z.to_nat loq) vqx) q) *
                `(array_at shq tq pathq (loq + len) nq
                    (skipn (Z.to_nat loq + Z.to_nat len) vqx) q) :: R').
eapply semax_post_flipped'.
*
 eapply (semax_call_id0_alt _ _ _ _ _ _ _ _ _ _ _ witness Frame);
  try eassumption; try reflexivity.
 3: instantiate (1:= fst (fsig_of_funspec (snd memcpy_spec))); reflexivity.
 2: assumption.
 rewrite Hspec.
 f_equal. simpl @snd. simpl @fst.  f_equal. f_equal.
 reflexivity.
 reflexivity.
 unfold Frame; go_lowerx.
 replace (lop+len-lop)%Z with len by omega.
 replace (loq+len-loq)%Z with len by omega.
 super_unfold_lift.
 simpl.
 rewrite prop_true_andp by auto.
 rewrite prop_true_andp by auto.
 rewrite prop_true_andp.
 Focus 2. {
 unfold temp, make_args'.
 unfold_lift. simpl.
 unfold eval_id. simpl. rewrite <- H10, <- H11, <- H12.
 rewrite TCp, TCq, TCn.
 simpl.
 split.
 unfold field_address.
 if_tac; [ |  reflexivity].
 destruct H14 as [? _]; destruct p; try contradiction; reflexivity.
 split.
 unfold field_address.
 if_tac; [ |  reflexivity].
 destruct H14 as [? _]; destruct q; try contradiction; reflexivity.
 split; auto.
 } Unfocus.
 rewrite map_firstn, <- skipn_map.
 cancel.
 apply derives_trans with (data_at_ shp (tarray tuchar len) (field_address tp (ArraySubsc lop :: pathp) p)).
 cancel.
 rewrite data_at__memory_block; try reflexivity.
 normalize.
 rewrite sizeof_tarray_tuchar by omega.
 auto.
 rewrite sizeof_tarray_tuchar by omega.
 change (Int.modulus) with (Int.max_unsigned + 1)%Z.
 omega.
*
 go_lowerx.
 normalize.
 replace (loq+len-loq)%Z with len by omega.
 rewrite map_firstn, <- skipn_map.
 cancel.
clear witness Frame.
 hnf in H13. normalize in H13.
 subst x. clear H10 H11 H12 H9 H8 H7 rho.
assert (exists (vpy : list (reptype (nested_field_type2 tp (ArraySubsc 0 :: pathp)))),
                  JMeq vpy vp'').
 rewrite H99. eauto.
destruct H7 as [vpy H8].
rewrite (array_seg_reroot_lemma shp tp pathp tuchar np
              noattr lop (lop+len) (firstn (Z.to_nat lop) vpy)
                  (firstn (Z.to_nat len) (skipn (Z.to_nat lop) vpy))
                  (skipn (Z.to_nat lop + Z.to_nat len) vpy)
                  (firstn (Z.to_nat len) (skipn (Z.to_nat loq) (map Vint contents)))
                  ); auto; try omega.
+ replace (lop+len-lop)%Z with len by omega.
    replace (firstn (Z.to_nat lop) vpx) with (firstn (Z.to_nat lop) vpy).
    replace (skipn (Z.to_nat lop + Z.to_nat len) vpx) 
     with (skipn (Z.to_nat lop + Z.to_nat len) vpy).
    cancel.
    rewrite <- Z2Nat.inj_add; try omega.
    clear - H8 H4 He Hvpx H99 Hlop Hvp' Hnp Hlen.
    apply JMeq_eq.
    apply JMeq_trans 
      with (y:= skipn (Z.to_nat (lop + len)) (splice_into_list lop (lop + len) np
          (skipn (Z.to_nat loq) (map Vint contents)) vp')).
   apply JMeq_skipn; auto. eapply JMeq_trans; try eassumption.
    apply JMeq_trans 
      with (y:= skipn (Z.to_nat (lop + len)) (vp' ++ list_repeat (Z.to_nat (np - Zlength vp')) Vundef)).
   apply eq_JMeq.
   forget (skipn (Z.to_nat loq) (map Vint contents)) as bl.
   { clear - Hlop Hlen Hvp' Hnp.
     assert (Z.to_nat lop <= length vp').
       rewrite <- (Nat2Z.id (length vp')), <- Zlength_correct.
       apply Z2Nat.inj_le; omega.
     assert (Z.to_nat len =
                   length (firstn (Z.to_nat len) (bl ++ list_repeat (Z.to_nat len) Vundef))).
       rewrite firstn_length, min_l; auto .
       rewrite app_length, length_list_repeat. omega.
     unfold splice_into_list.
     rewrite firstn_app1 by auto.
     replace (lop+len-lop)%Z with len by omega.
     rewrite Z2Nat.inj_add by omega.
     repeat rewrite <- skipn_skipn.
     rewrite skipn_app1 by (rewrite firstn_length, min_l; omega).
     rewrite (skipn_short (Z.to_nat lop))  by (rewrite firstn_length, min_l; omega).
     simpl app.
     rewrite (skipn_app1 _ (Z.to_nat lop) vp') by auto.
     rewrite skipn_app1 by omega.
     rewrite skipn_short by omega.
     simpl.
     rewrite firstn_same; auto.
     rewrite skipn_length.
     rewrite app_length, length_list_repeat.
     rewrite skipn_length.
     rewrite <- (Nat2Z.id (length vp')), <- Zlength_correct.
     rewrite <- Z2Nat.inj_sub by omega.
     rewrite <- Z2Nat.inj_add by omega.
     rewrite <- Z2Nat.inj_sub by omega.
     apply Z2Nat.inj_le; omega.
   }
   apply JMeq_skipn; auto.
   apply JMeq_trans with (y := vpe); auto.
 assert (0 <= lop <= Zlength vp')%Z by omega.
   apply JMeq_eq.
 apply JMeq_trans with (y:= firstn (Z.to_nat lop)  (splice_into_list lop (lop + len) np
          (skipn (Z.to_nat loq) (map Vint contents)) vp')).
 apply JMeq_firstn; auto. eapply JMeq_trans; try eassumption.
 apply JMeq_trans with (y := firstn (Z.to_nat lop) (vp' ++ list_repeat (Z.to_nat (np - Zlength vp')) Vundef)).
  apply eq_JMeq.
 rewrite firstn_splice_into_list; auto.
 rewrite firstn_app1; auto.
 rewrite <- (Nat2Z.id (length vp')). rewrite <- Zlength_correct.
   apply Z2Nat.inj_le; omega.
 apply JMeq_firstn; auto.
 apply JMeq_trans with (y := vpe); auto.  
+  
   apply JMeq_trans with (y:=   firstn (Z.to_nat len) (skipn (Z.to_nat lop) (splice_into_list lop (lop + len) np
          (skipn (Z.to_nat loq) (map Vint contents)) vp'))).
  apply JMeq_firstn; auto. apply JMeq_skipn; auto. eapply JMeq_trans; eassumption.
  apply eq_JMeq.
assert (Z.to_nat len <= length (skipn (Z.to_nat loq) (map Vint contents))). {
 rewrite skipn_length. rewrite map_length. 
 destruct Hnq as [Hn ?].  clear - Hn Hloq Hlen.
 rewrite <- (Nat2Z.id (length contents)).
  rewrite <- Z2Nat.inj_sub; try omega.
 rewrite <- Zlength_correct. apply Z2Nat.inj_le; omega.
}
 unfold splice_into_list.
 rewrite skipn_app2.
 rewrite firstn_length, min_l. rewrite minus_diag. rewrite skipn_0.
 replace (lop+len-lop)%Z with len by omega.
 rewrite firstn_app1.
 rewrite firstn_app1 by auto.
 pattern (Z.to_nat len) at 2;  replace (Z.to_nat len) with (Z.to_nat len + 0) by omega.
 rewrite firstn_firstn.
 auto.
 rewrite firstn_app1 by auto.
 rewrite firstn_length, min_l; try omega.
 rewrite app_length.
 rewrite length_list_repeat.
 rewrite <- (Nat2Z.id (length vp')). rewrite <- Zlength_correct.
 destruct (zlt lop (Zlength vp')).
 apply Z2Nat.inj_lt in l; try omega.
  rewrite <- Z2Nat.inj_add; try omega.
 apply Z2Nat.inj_le; try omega.
 rewrite firstn_app1.
 rewrite firstn_length. rewrite min_l; try omega.
 rewrite <- (Nat2Z.id (length vp')). rewrite <- Zlength_correct.
 apply Z2Nat.inj_le; try omega.
 rewrite <- (Nat2Z.id (length vp')). rewrite <- Zlength_correct.
 apply Z2Nat.inj_le; try omega.
+
 rewrite <- skipn_skipn.
 rewrite firstn_skipn. rewrite firstn_skipn. auto.
+
 rewrite Zlength_correct, firstn_length, min_l.
 apply Z2Nat.id. omega.
 transitivity (length   (splice_into_list lop (lop + len) np
          (skipn (Z.to_nat loq) (map Vint contents)) vp')).
 rewrite <- (Nat2Z.id (length _)). rewrite <- Zlength_correct. 
 rewrite length_splice_into_list; try omega.
 apply Z2Nat.inj_le; try omega.
 apply NPeano.Nat.eq_le_incl.
 apply JMeq_length; auto.
 apply JMeq_trans with (y:=vp''); auto.
+
 rewrite Zlength_correct. rewrite firstn_length, min_l. rewrite Z2Nat.id by omega. omega.
 rewrite skipn_length.
 replace (length vpy) with (length (splice_into_list lop (lop + len) np
          (skipn (Z.to_nat loq) (map Vint contents)) vp'))
  by (apply JMeq_length; auto; apply JMeq_trans with (y:=vp''); auto).
 rewrite <- (Nat2Z.id (length _)). rewrite <- Zlength_correct. 
 rewrite length_splice_into_list; try omega.
 rewrite <- Z2Nat.inj_sub by omega.
 apply Z2Nat.inj_le; omega.
Qed.

Lemma data_block_data_field:
 forall sh dd dd' c, 
  Forall isbyteZ dd ->
  (Zlength dd = CBLOCKz)%Z ->
  JMeq (map Vint (map Int.repr dd)) dd' ->
  data_block sh dd (field_address t_struct_SHA256state_st [StructField _data] c) =
  field_at sh t_struct_SHA256state_st [StructField _data] dd' c.
Proof.
intros.
unfold data_block.
erewrite field_at_data_at by reflexivity.
repeat rewrite prop_true_andp by auto.
apply equal_f.
apply data_at_type_changable; auto.
rewrite H0; reflexivity.
Qed.

Lemma call_memset_tuchar:
  forall (shp : share) (tp: type) (pathp: list gfield) (lop: Z) (vp': list val) (p: val)
           (c: int) (len : Z)
           (R': list (environ -> mpred))
           (np : Z)
           (vp vp'': reptype (nested_field_type2 tp pathp))
           (e_p e_c e_n : expr)
           Espec Delta P Q R,
     writable_share shp ->
     (0 <= len <= Int.max_signed)%Z ->
     nested_field_type2 tp pathp = tarray tuchar np ->
     JMeq vp vp' ->
     JMeq vp'' (splice_into_list lop (lop+len) np (list_repeat (Z.to_nat len) (Vint c)) vp') ->
     PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
         PROP () LOCAL (`(eq (offset_val (Int.repr lop) 
                                      (offset_val (Int.repr (nested_field_offset2 tp pathp)) p))) (eval_expr e_p);
                  `(eq (Vint c)) (eval_expr e_c);
                  `(eq (Vint (Int.repr len))) (eval_expr e_n))
         (SEPx (`(field_at shp tp pathp vp p) :: R')) ->
   @semax Espec Delta 
    (PROPx P (LOCALx Q (SEPx R)))
    (Scall None
             (Evar _memset 
               (Tfunction
                (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil)))
                  (tptr tvoid) cc_default))
              [e_p; e_c; e_n])
    (normal_ret_assert (PROPx P (LOCALx Q 
     (SEPx (`(field_at shp tp pathp vp'' p) :: R'))))).
Admitted.

Lemma field_at_cancel_undef_example:
  forall  d c, 
  field_at Tsh t_struct_SHA256state_st [StructField _data] d c |--
  field_at Tsh t_struct_SHA256state_st [StructField _data] (list_repeat 64 Vundef) c.
Proof.
  intros.
  apply field_at_stronger.
  apply stronger_array_ext.
  intros.
  unfold Znth.
  if_tac; [omega |].
  rewrite nth_list_repeat.
  intros sh p.
  apply data_at_data_at_.
Qed.

Lemma update_inner_if_then_proof:
 forall (Espec : OracleKind) (hashed : list int)
          (dd data : list Z) (c d: val) (sh: share) (len: nat) kv
   (H : (Z.of_nat len <= Zlength data)%Z)
   (H3 : (Zlength dd < CBLOCKz)%Z)
   (H3' : Forall isbyteZ dd)
   (H4 : (LBLOCKz | Zlength hashed))
   (Hlen : (Z.of_nat len <= Int.max_unsigned)%Z)
   (c' : name _c) (data_ : name _data) (len' : name _len) 
   (data' : name _data) (p : name _p) (n : name _n)
   (fragment_ : name _fragment),
  let k := (64 - Zlength dd)%Z in
  forall (H0: (0 < k <= 64)%Z)
       (H1: (64 < Int.max_unsigned)%Z)
       (DBYTES: Forall isbyteZ data),
semax Delta_update_inner_if
  (PROP  ()
   LOCAL 
   (`(typed_true tint)
      (eval_expr
         (Ebinop Oge (Etempvar _len tuint) (Etempvar _fragment tuint) tint));
    temp _fragment (Vint (Int.repr k));
    temp _p (field_address t_struct_SHA256state_st [StructField _data] c);
    temp _n (Vint (Int.repr (Zlength dd)));
    temp _c c; temp _data d; temp _len (Vint (Int.repr (Z.of_nat len)));
    gvar  _K256 kv)
   SEP 
   (`(data_at Tsh t_struct_SHA256state_st
                 (map Vint (hash_blocks init_registers hashed),
                  (Vint (lo_part (bitlength hashed dd + (Z.of_nat len)*8)),
                   (Vint (hi_part (bitlength hashed dd + (Z.of_nat len)*8)),
                    (map Vint (map Int.repr dd),
                     Vint (Int.repr (Zlength dd))))))
               c);
   `(K_vector kv);
   `(data_at sh (tarray tuchar (Zlength data)) (map Vint (map Int.repr data)) d)))
  update_inner_if_then
  (overridePost (sha_update_inv sh hashed len c d dd data kv false)
     (function_body_ret_assert tvoid
        (EX  a' : s256abs,
         PROP  (update_abs (firstn len data) (S256abs hashed dd) a')
         LOCAL ()
         SEP  (`(K_vector kv); `(sha256state_ a' c); `(data_block sh data d))))).
Proof.
 intros.
 simplify_Delta; abbreviate_semax.
  unfold update_inner_if_then.
  apply (remember_value (eval_id _fragment)); intro fragment.
assert_PROP (fragment = Vint (Int.repr k)).
  entailer!.
drop_LOCAL 0. subst fragment.
assert_PROP ((Z.of_nat len >= k)%Z). {
  entailer!.
  rewrite negb_true_iff in H5. 
  apply ltu_repr_false in H5; [ | repable_signed | omega].
  auto.
}
drop_LOCAL 0.
match goal with |- semax ?D (PROP() (LOCALx ?Q (SEPx _))) _ _ =>
 apply semax_seq'
 with (PROP() (LOCALx Q 
        (SEP (`(data_at Tsh t_struct_SHA256state_st 
                 (map Vint (hash_blocks init_registers hashed),
                  (Vint (lo_part (bitlength hashed dd + (Z.of_nat len)*8)),
                   (Vint (hi_part (bitlength hashed dd + (Z.of_nat len)*8)),
                    (map Vint (map Int.repr dd) ++
                      firstn (Z.to_nat k) (map Vint (map Int.repr data)),
                     Vint (Int.repr (Zlength dd))))))
               c);
      `(K_vector kv);
      `(data_at sh (tarray tuchar (Zlength data)) (map Vint (map Int.repr data)) d)))))
end;
 [ eapply semax_post_flipped' | ].
*
  assert_PROP (field_address (tarray tuchar (Zlength data)) [ArraySubsc 0] d = d). {
    entailer.
    rewrite (data_at_field_at sh  (tarray tuchar (Zlength data))).
    rewrite (field_at_compatible' sh).
    entailer!.
    unfold field_address; rewrite if_true.
    unfold nested_field_offset2; simpl. normalize.
  eapply field_compatible_cons_Tarray; try reflexivity; auto.
 omega.
  }
 rename H5 into Hd.
  evar (Frame: list (LiftEnviron mpred)).
  eapply(call_memcpy_tuchar
   (*dst*) Tsh t_struct_SHA256state_st [StructField _data] (Zlength dd) (map Vint (map Int.repr dd)) c
   (*src*) sh (tarray tuchar (Zlength data)) [ ] 0 (map Int.repr data)  d
   (*len*) k
        Frame);
  try reflexivity; auto; try omega.
  apply Zlength_nonneg. repeat rewrite Zlength_map. unfold k in *; omega.
  unfold k; omega.
  rewrite Zlength_map. omega.
  unfold_data_at 1%nat.
  entailer!.
  rewrite field_address_clarify; auto.
  normalize.
  erewrite nested_field_offset2_Tarray; try reflexivity. 
  rewrite sizeof_tuchar, Z.mul_1_l.
  unfold field_address in *.
  if_tac in TC; try contradiction. normalize.
  apply isptr_is_pointer_or_null.
  apply field_address_isptr; auto.
  eapply field_compatible_cons_Tarray; try reflexivity; auto.
  unfold k in *; omega.
*
  rewrite skipn_0.
  rewrite (data_at_field_at sh).
  replace (Zlength dd + k - Zlength dd)%Z with k by (clear; omega).
  unfold_data_at 1%nat.
  entailer!.
  replace (Zlength dd + k)%Z with 64%Z by (unfold k; omega).
  rewrite splice_into_list_simplify2; try (repeat rewrite Zlength_map; omega).
  fold k. apply derives_refl.
  unfold k in H0; omega.
  repeat rewrite Zlength_map.
  clear - H2 H0 H.
  unfold k in *; clear k. omega.
*
  abbreviate_semax.
  repeat rewrite firstn_map. repeat rewrite <- map_app.
  unfold_data_at 1%nat.
  rewrite <- (data_block_data_field _ (dd ++ firstn (Z.to_nat k) data));
 [
 | rewrite Forall_app; split; auto; apply Forall_firstn; auto
 | rewrite Zlength_app, (Zlength_correct (firstn _ _)),
   firstn_length, min_l;
   [ rewrite Z2Nat.id by omega; unfold k; change CBLOCKz with 64%Z; omega
   | apply Nat2Z.inj_le;
     rewrite Z2Nat.id; [rewrite <- Zlength_correct; omega | omega ]]
 | reflexivity
 ].
normalize.
 forward_call (* sha256_block_data_order (c,p); *)
   (hashed, Zlist_to_intlist (dd++(firstn (Z.to_nat k) data)), c,
     (field_address t_struct_SHA256state_st [StructField _data] c),
      Tsh, kv). {
 entailer.
 unfold k in *|-.
 assert (length (dd ++ firstn (Z.to_nat k) data) = 64). {
  unfold k.
  rewrite app_length.
  rewrite firstn_length, min_l.
  apply Nat2Z.inj. rewrite Nat2Z.inj_add.
  rewrite Z2Nat.id.
  change (Z.of_nat 64) with 64%Z.
  rewrite <- Zlength_correct; omega.
  omega.
  apply Nat2Z.inj_le.  rewrite Z2Nat.id.  rewrite <- Zlength_correct; omega.
  omega.
 }
 assert (length (Zlist_to_intlist (dd ++ firstn (Z.to_nat k) data)) = LBLOCK). {
  apply length_Zlist_to_intlist. assumption.
 }
 apply andp_right; [apply prop_right |].
 rewrite Zlength_correct, H10. reflexivity.
rewrite Zlist_to_intlist_to_Zlist;
  [ 
  | rewrite H9; exists LBLOCK; reflexivity
  | rewrite Forall_app; split; auto; apply Forall_firstn; auto].
 cancel.
}
 after_call.
 
 rewrite Zlist_to_intlist_to_Zlist;
 [
 | rewrite app_length, firstn_length;
   rewrite min_l 
    by (apply Nat2Z.inj_le; rewrite Z2Nat.id by omega; 
     rewrite <- Zlength_correct; omega);
   exists LBLOCK; unfold k;
   apply Nat2Z.inj; transitivity 64%Z; [ | reflexivity];
   rewrite Nat2Z.inj_add; rewrite Z2Nat.id by (fold k; omega);
   rewrite <- Zlength_correct; omega
 |  rewrite Forall_app; split; auto; apply Forall_firstn; auto
].
 erewrite data_block_data_field;
   auto; 
 [
 | rewrite Forall_app; split; auto; apply Forall_firstn; auto
 | rewrite Zlength_app, (Zlength_correct (firstn _ _)),
   firstn_length, min_l;
   [ rewrite Z2Nat.id by omega; unfold k; change CBLOCKz with 64%Z; omega
   | apply Nat2Z.inj_le;
     rewrite Z2Nat.id; [rewrite <- Zlength_correct; omega | omega ]]
 ].
forward. (* data  += fragment; *)
forward. (* len -= fragment; *)
  normalize_postcondition.
eapply semax_post_flipped3.
evar (Frame: list (LiftEnviron mpred)).
  eapply(call_memset_tuchar
   (*dst*) Tsh t_struct_SHA256state_st [StructField _data] 0 
                (map Vint (map Int.repr (dd ++ firstn (Z.to_nat k) data))) c
   (*src*) Int.zero
   (*len*) 64
        Frame);
   [ auto | repable_signed | reflexivity | reflexivity | reflexivity | ].
entailer!.
 rewrite field_address_clarify by auto.
 auto.

 rewrite overridePost_normal'.
 unfold sha_update_inv.
 apply exp_right with (Zlist_to_intlist (dd ++ firstn (Z.to_nat k) data)).
assert (LL: length (dd ++ firstn (Z.to_nat k) data) = CBLOCK). {
 rewrite app_length. rewrite firstn_length. rewrite min_l.
 unfold k in *; 
 apply Nat2Z.inj. rewrite Nat2Z.inj_add.
 rewrite Z2Nat.id by omega.
 rewrite <- Zlength_correct. change (Z.of_nat (CBLOCK)) with 64%Z.
 omega.
 apply Nat2Z.inj_le;  rewrite Z2Nat.id by omega; rewrite <- Zlength_correct; omega.
}
assert (length (Zlist_to_intlist (dd ++ firstn (Z.to_nat k) data)) = LBLOCK). {
 apply length_Zlist_to_intlist. change (4*LBLOCK)%nat with CBLOCK.
 apply LL.
}
 assert (KK: k = Z.of_nat (LBLOCK * 4 - length dd)). {
 unfold k.
 rewrite Nat2Z.inj_sub. rewrite Zlength_correct; reflexivity.
 unfold k in H0. clear - H0.
 apply Nat2Z.inj_le.
 change (Z.of_nat (LBLOCK*4)) with 64%Z.
 rewrite <- Zlength_correct.
 omega.
}

 rewrite (Zlength_correct (Zlist_to_intlist _)).
 rewrite H5.
 rewrite Zlist_to_intlist_to_Zlist;
 [
 | rewrite app_length, firstn_length;
   rewrite min_l 
    by (apply Nat2Z.inj_le; rewrite Z2Nat.id by omega; rewrite <- Zlength_correct; omega);
   exists LBLOCK; unfold k;
   apply Nat2Z.inj; transitivity 64%Z; [ | reflexivity];
   rewrite Nat2Z.inj_add; rewrite Z2Nat.id by (fold k; omega);
   rewrite <- Zlength_correct; omega
 |  rewrite Forall_app; split; auto; apply Forall_firstn; auto
].

 simpl update_tycon; rewrite insert_local.
 rewrite splice_into_list_simplify0;
 [ 
 | rewrite Zlength_correct, length_list_repeat; reflexivity
 | rewrite Zlength_correct, map_length, map_length, LL; reflexivity].
unfold_data_at 2%nat.
change (Z.to_nat 64) with CBLOCK.
entailer!.
 +
  apply Nat2Z.inj_ge.
  rewrite Nat2Z.inj_sub.
  change (Z.of_nat (LBLOCK*4)) with 64%Z.
  rewrite <- Zlength_correct; omega.
  clear - H3. apply Nat2Z.inj_le. rewrite <- Zlength_correct.
  change (Z.of_nat (LBLOCK*4)%nat) with CBLOCKz; clear - H3; omega.
 + 
  f_equal. f_equal. rewrite Z2Nat.inj_sub by omega.
  rewrite Zlength_correct, Nat2Z.id.
  reflexivity.
 +
 rewrite <- KK. auto.
 +
 rewrite KK.
 rewrite Nat2Z.inj_sub; auto.
 apply Nat2Z.inj_le.
 rewrite Nat2Z.inj_sub.
 rewrite <- Zlength_correct.
 change (Z.of_nat (LBLOCK * 4)) with 64%Z.
 omega.
 apply Nat2Z.inj_le.
 rewrite <- Zlength_correct.
 change (Z.of_nat (LBLOCK * 4)) with 64%Z.
 omega.
 +
 unfold data_block; normalize.
Qed.
