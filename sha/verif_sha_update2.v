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

Definition inv_at_inner_if sh hashed len c d dd data kv bitlen :=
 (PROP ()
   (LOCAL 
      (temp _fragment (Vint (Int.repr (64- Zlength dd)));
       temp _p (offset_val (Int.repr 40) c);
       temp _n (Vint (Int.repr (Zlength dd)));
       temp _c c; temp _data d;
       temp _len (Vint (Int.repr (Z.of_nat len)));
       var  _K256 (tarray tuint CBLOCKz) kv)
   SEP  (`(data_at Tsh t_struct_SHA256state_st
                 (map Vint (hash_blocks init_registers hashed),
                  (Vint (lo_part (bitlen + (Z.of_nat len)*8)),
                   (Vint (hi_part (bitlen + (Z.of_nat len)*8)),
                    (map Vint (map Int.repr dd),
                     Vint (Int.repr (Zlength dd))))))
               c);
   `(K_vector kv);
   `(data_block sh data d)))).

Definition sha_update_inv sh hashed len c d (frag: list Z) (data: list Z) kv bitlen (done: bool) :=
   (EX blocks:list int,
   PROP  (len >= length blocks*4 - length frag /\
              (LBLOCKz | Zlength blocks) /\ 
              intlist_to_Zlist blocks = frag ++ firstn (length blocks * 4 - length frag) data /\
             if done then len-(length blocks*4 - length frag) < CBLOCK else True)
   LOCAL  (temp _p (offset_val (Int.repr 40) c); temp _c c; 
                temp _data (offset_val (Int.repr (Z.of_nat (length blocks*4-length frag))) d);
                temp _len (Vint (Int.repr (Z.of_nat (len- (length blocks*4 - length frag)))));
                var  _K256 (tarray tuint CBLOCKz) kv)
   SEP  (`(K_vector kv);
           `(data_at Tsh t_struct_SHA256state_st
                 (map Vint (hash_blocks init_registers (hashed++blocks)),
                  (Vint (lo_part (bitlen + (Z.of_nat len)*8)),
                   (Vint (hi_part (bitlen + (Z.of_nat len)*8)),
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

Definition splice_into_list (lo hi: Z) (source target : list val) : list val :=
   firstn (Z.to_nat lo) (target ++ list_repeat (Z.to_nat (lo - Zlength target)) Vundef)
   ++ firstn (Z.to_nat (hi-lo)) (source ++ list_repeat (Z.to_nat (hi-lo)) Vundef)
   ++ skipn (Z.to_nat hi) target.

Lemma splice_into_list_simplify0:
  forall n src dst, 
    Zlength src = n ->
    Zlength dst = n ->
    splice_into_list 0 n src dst = src.
Proof.
 intros.
 unfold splice_into_list.
 rewrite Z.sub_0_r. change (Z.of_nat 0) with 0%nat.
 simpl firstn. unfold app at 1.
 rewrite firstn_app1.
 rewrite firstn_same.
 rewrite skipn_short.
 rewrite <- app_nil_end; auto.
 rewrite <- H0. rewrite Zlength_correct. rewrite Nat2Z.id; auto.
 rewrite <- H. rewrite Zlength_correct. rewrite Nat2Z.id; auto.
 rewrite <- H. rewrite Zlength_correct. rewrite Nat2Z.id; auto.
Qed.

Lemma splice_into_list_simplify1:
  forall lo hi src tgt,
    lo = Zlength tgt ->
    (hi-lo = Zlength src)%Z ->
    splice_into_list lo hi src tgt = tgt++src.
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
rewrite <- app_nil_end.
auto.
Qed.

Lemma splice_into_list_simplify2:
  forall lo hi src tgt,
    lo = Zlength tgt ->
    (lo <= hi)%Z ->
    (hi-lo <= Zlength src)%Z ->
    splice_into_list lo hi src tgt = tgt++ firstn (Z.to_nat (hi-lo)) src.
Proof.
intros; subst; unfold splice_into_list.
rewrite Z.sub_diag.
change (Z.to_nat 0) with 0.
unfold list_repeat at 1.
repeat rewrite ZtoNat_Zlength.
rewrite <- app_nil_end.
rewrite firstn_same by omega.
f_equal.
pose proof (Zlength_nonneg src).
pose proof (Zlength_nonneg tgt).
rewrite skipn_short
 by (apply Nat2Z.inj_le;
      rewrite <- Zlength_correct;
      rewrite Z2Nat.id by omega; omega).
rewrite <- app_nil_end.
rewrite firstn_app1; auto.
apply Nat2Z.inj_le.
rewrite <- Zlength_correct.
rewrite Z2Nat.id by omega.
auto.
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
     writable_share shp ->
     nested_field_type2 tp pathp = tarray tuchar np ->
     nested_field_type2 tq pathq = tarray tuchar nq ->
     JMeq vq (map Vint contents) ->
     JMeq vp vp' ->
     JMeq vp'' (splice_into_list lop (lop+len) (skipn (Z.to_nat loq) (map Vint contents)) vp') ->
     PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
         PROP () LOCAL (`(eq (offset_val (Int.repr lop) 
                                      (offset_val (Int.repr (nested_field_offset2 tp pathp)) p))) (eval_expr e_p);
                  `(eq (offset_val (Int.repr loq) q)) (eval_expr e_q);
                  `(eq (Vint (Int.repr len))) (eval_expr e_n))
         (SEPx (`(field_at shp tp pathp vp p) :: 
                   `(field_at shq tq pathq vq q) :: R')) ->
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
Admitted.


Lemma data_block_data_field:
 forall sh dd dd' c, 
  Forall isbyteZ dd ->
  (Zlength dd = CBLOCKz)%Z ->
  size_compatible t_struct_SHA256state_st c ->
  align_compatible t_struct_SHA256state_st c ->
  JMeq (map Vint (map Int.repr dd)) dd' ->
  data_block sh dd (offset_val (Int.repr 40) c) =
  field_at sh t_struct_SHA256state_st [StructField _data] dd' c.
Proof.
intros.
unfold data_block.
erewrite field_at_data_at by reflexivity.
repeat rewrite prop_true_andp by auto.
rewrite prop_true_andp by (split; simpl; auto).
unfold at_offset', at_offset; simpl.
apply equal_f.
apply data_at_type_changable; auto.
rewrite H0; reflexivity.
Qed.


Lemma data_field_data_block:
 forall sh dd dd' c, 
  Forall isbyteZ dd ->
  (Zlength dd = CBLOCKz)%Z ->
  JMeq (map Vint (map Int.repr dd)) dd' ->
  field_at sh t_struct_SHA256state_st [StructField _data] dd' c =
  !! (size_compatible t_struct_SHA256state_st c) &&
  !! (align_compatible t_struct_SHA256state_st c)
  && data_block sh dd (offset_val (Int.repr (nested_field_offset2 t_struct_SHA256state_st [StructField _data])) c).
Proof.
intros.
unfold data_block.
erewrite field_at_data_at by reflexivity.
rewrite at_offset'_eq.
rewrite (prop_true_andp _ _ H).
repeat rewrite andp_assoc.
f_equal.
f_equal.
rewrite (prop_true_andp (legal_nested_field _ _)) by solve_legal_nested_field.
apply equal_f.
apply data_at_type_changable; auto.
rewrite H0; reflexivity.
rewrite <- data_at_offset_zero.
auto.
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
     JMeq vp'' (splice_into_list lop (lop+len) (list_repeat (Z.to_nat len) (Vint c)) vp') ->
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
  apply field_at_stronger; [reflexivity |].
  change (nested_field_type2 t_struct_SHA256state_st [StructField _data]) with (tarray tuchar 64).
  apply stronger_array_ext; [reflexivity |].
  intros.
  unfold Znth.
  if_tac; [omega |].
  rewrite nth_list_repeat.
  intros sh p.
  apply data_at_data_at_.
  reflexivity.
Qed.

Lemma update_inner_if_then_proof:
 forall (Espec : OracleKind) (hashed : list int)
          (dd data : list Z) (c d: val) (sh: share) (len: nat) kv
          (bitlen: Z) 
   (H : (Z.of_nat len <= Zlength data)%Z)
   (H7 : ((Zlength hashed * 4 + Zlength dd) * 8)%Z = bitlen)
   (H3 : (Zlength dd < CBLOCKz)%Z)
   (H3' : Forall isbyteZ dd)
   (H4 : (LBLOCKz | Zlength hashed))
   (Hlen : (Z.of_nat len <= Int.max_unsigned)%Z)
   (c' : name _c) (data_ : name _data) (len' : name _len) 
   (data' : name _data) (p : name _p) (n : name _n)
   (fragment_ : name _fragment),
  let j := (40 + Zlength dd)%Z in
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
    temp _p (offset_val (Int.repr 40) c);
    temp _n (Vint (Int.repr (Zlength dd)));
    temp _c c; temp _data d; temp _len (Vint (Int.repr (Z.of_nat len)));
    var  _K256 (tarray tuint CBLOCKz) kv)
   SEP 
   (`(data_at Tsh t_struct_SHA256state_st
                 (map Vint (hash_blocks init_registers hashed),
                  (Vint (lo_part (bitlen + (Z.of_nat len)*8)),
                   (Vint (hi_part (bitlen + (Z.of_nat len)*8)),
                    (map Vint (map Int.repr dd),
                     Vint (Int.repr (Zlength dd))))))
               c);
   `(K_vector kv);
   `(data_at sh (tarray tuchar (Zlength data)) (map Vint (map Int.repr data)) d)))
  update_inner_if_then
  (overridePost (sha_update_inv sh hashed len c d dd data kv bitlen false)
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
                  (Vint (lo_part (bitlen + (Z.of_nat len)*8)),
                   (Vint (hi_part (bitlen + (Z.of_nat len)*8)),
                    (map Vint (map Int.repr dd) ++
                      firstn (Z.to_nat k) (map Vint (map Int.repr data)),
                     Vint (Int.repr (Zlength dd))))))
               c);
      `(K_vector kv);
      `(data_at sh (tarray tuchar (Zlength data)) (map Vint (map Int.repr data)) d)))))
end.
eapply semax_post_flipped'.

evar (Frame: list (LiftEnviron mpred)).
  eapply(call_memcpy_tuchar
   (*dst*) Tsh t_struct_SHA256state_st [StructField _data] (Zlength dd) (map Vint (map Int.repr dd)) c
   (*src*) sh (tarray tuchar (Zlength data)) [ ] 0 (map Int.repr data)  d
   (*len*) k
        Frame);
   [ auto | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | ].
unfold_data_at 1%nat.
entailer!.
rewrite skipn_0.
rewrite (data_at_field_at sh).
rewrite splice_into_list_simplify2
  by (repeat rewrite Zlength_map; omega).
replace (Zlength dd + k - Zlength dd)%Z with k by omega.
unfold_data_at 1%nat.
entailer!.
abbreviate_semax.
repeat rewrite firstn_map. repeat rewrite <- map_app.
unfold_data_at 1%nat.

rewrite (data_field_data_block _ (dd ++ firstn (Z.to_nat k) data));
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
   (hashed, Zlist_to_intlist (dd++(firstn (Z.to_nat k) data)), c, (offset_val (Int.repr 40) c), Tsh, kv). {
 entailer.
 unfold j,k in *|-.
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
 rewrite Zlength_correct, H12. reflexivity.
 repeat rewrite firstn_map. repeat rewrite <- map_app.
rewrite Zlist_to_intlist_to_Zlist;
  [ 
  | rewrite H11; exists LBLOCK; reflexivity
  | rewrite Forall_app; split; auto; apply Forall_firstn; auto].
 cancel.
}
 after_call.
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
 rewrite H8.
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
 *
  apply Nat2Z.inj_ge.
  rewrite Nat2Z.inj_sub.
  change (Z.of_nat (LBLOCK*4)) with 64%Z.
  rewrite <- Zlength_correct; omega.
  clear - H3. apply Nat2Z.inj_le. rewrite <- Zlength_correct.
  change (Z.of_nat (LBLOCK*4)%nat) with CBLOCKz; clear - H3; omega.
 * 
  f_equal. f_equal. rewrite Z2Nat.inj_sub by omega.
  rewrite Zlength_correct, Nat2Z.id.
  reflexivity.
*
 rewrite <- KK. auto.
*
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
 *
 repeat apply sepcon_derives.
 unfold data_block.
 normalize.
Qed.
