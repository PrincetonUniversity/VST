Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.call_memcpy.
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
       temp _data d; temp _c c;
       temp _len (Vint (Int.repr len));
       gvar  _K256 kv)
   SEP  (data_at Tsh t_struct_SHA256state_st
                 (map Vint (hash_blocks init_registers hashed),
                  (Vint (lo_part (bitlength hashed dd + len*8)),
                   (Vint (hi_part (bitlength hashed dd + len*8)),
                    (map Vint (map Int.repr dd) ++ list_repeat (Z.to_nat (CBLOCKz-Zlength dd)) Vundef,
                     Vint (Int.repr (Zlength dd))))))
               c;
     K_vector kv;
     data_block sh data d))).

Definition sha_update_inv sh hashed len c d (dd: list Z) (data: list Z) kv (done: bool)
    : environ -> mpred :=
   (*EX blocks:list int,*)  (* this line doesn't work; bug in Coq 8.4pl3 thru 8.4pl6?  *)
   @exp (environ->mpred) _ _  (fun blocks:list int =>
   PROP  ((len >= Zlength blocks*4 - Zlength dd)%Z;
              (LBLOCKz | Zlength blocks);
              intlist_to_Zlist blocks = dd ++ sublist 0  (Zlength blocks * 4 - Zlength dd) data;
             if done then (len-(Zlength blocks*4 - Zlength dd) < CBLOCKz)%Z else True)
   LOCAL  (temp _p (field_address t_struct_SHA256state_st [StructField _data]  c);
                temp _data
                (field_address0 (tarray tuchar (Zlength data))
                          [ArraySubsc (Zlength blocks * 4 - Zlength dd)] d);
                temp _c c;
                temp _len (Vint (Int.repr (len- (Zlength blocks*4 - Zlength dd))));
                gvar  _K256 kv)
   SEP  (K_vector kv;
           @data_at CompSpecs Tsh t_struct_SHA256state_st
                 ((map Vint (hash_blocks init_registers (hashed++blocks)),
                  (Vint (lo_part (bitlength hashed dd + len*8)),
                   (Vint (hi_part (bitlength hashed dd + len*8)),
                    (list_repeat (Z.to_nat CBLOCKz) Vundef, Vundef)))) : reptype t_struct_SHA256state_st)
               c;
            data_block sh data d)).

Definition Delta_update_inner_if : tycontext :=
  (initialized _fragment
     (initialized _p
        (initialized _n
           (initialized _data (func_tycontext f_SHA256_Update Vprog Gtot))))).

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

Lemma update_inner_if_update_abs:
  forall (hashed : list int) (dd data : list Z) (len : Z)
  (H3 : Zlength dd < CBLOCKz)
  (H3' : Forall isbyteZ dd)
  (H4 : (LBLOCKz | Zlength hashed))
  (DBYTES : Forall isbyteZ data)
  (H2 : len < 64 - Zlength dd)
  (H7 : value_fits (tarray tuchar 64)
       (map Vint (map Int.repr dd) ++
        sublist 0 len (map Vint (map Int.repr data)) ++
        list_repeat (Z.to_nat (CBLOCKz - Zlength dd - len)) Vundef)),
update_abs (sublist 0 len data) (S256abs hashed dd)
  (S256abs hashed (dd ++ sublist 0 len data)).
Proof.
  intros.
    assert (Zlength (dd ++ sublist 0 len data) < CBLOCKz).
         clear - H2 H7. simplify_value_fits in H7. destruct H7 as [? _].
   rewrite !sublist_map in H.
   autorewrite with sublist in H. rewrite Zlength_app.
   pose proof CBLOCKz_eq. rewrite Zlength_list_repeat in H.
   rewrite Z.max_r in H by omega. omega.
    rewrite (app_nil_end hashed) at 2.
    rewrite update_abs_eq.
    exists nil. rewrite <- !app_nil_end.
    rewrite !S256abs_hashed; auto.
    rewrite !S256abs_data; auto.
    apply Forall_app; split; auto.
    unfold S256abs.
    apply Forall_app; split; auto.
    apply isbyte_intlist_to_Zlist.
    rewrite <- !app_nil_end.
    unfold S256abs.
    apply Forall_app; split; auto.
    apply isbyte_intlist_to_Zlist.
    apply Forall_app; split; auto.
Qed.

Lemma update_inner_if_sha256_state_:
  forall (hashed : list int) (dd data : list Z) (c d : val) (sh : share) (len : Z)
  (H : 0 <= len <= Zlength data)
  (H3' : Forall isbyteZ dd)
  (H4 : (LBLOCKz | Zlength hashed))
  (H0 : 0 < 64 - Zlength dd <= 64)
  (DBYTES : Forall isbyteZ data)
  (H2 : len < 64 - Zlength dd),
field_at Tsh t_struct_SHA256state_st [StructField _data]
  (map Vint (map Int.repr dd) ++
   sublist 0 len (map Vint (map Int.repr data)) ++
   list_repeat (Z.to_nat (CBLOCKz - Zlength dd - len)) Vundef) c *
field_at sh (tarray tuchar (Zlength data)) []
  (map Vint (map Int.repr data)) d *
field_at Tsh t_struct_SHA256state_st [StructField _h]
  (map Vint (hash_blocks init_registers hashed)) c *
field_at Tsh t_struct_SHA256state_st [StructField _Nl]
  (Vint (lo_part (bitlength hashed dd + len * 8))) c *
field_at Tsh t_struct_SHA256state_st [StructField _Nh]
  (Vint (hi_part (bitlength hashed dd + len * 8))) c *
field_at Tsh t_struct_SHA256state_st [StructField _num]
  (Vint (Int.repr (Zlength dd + len))) c
|-- sha256state_ (S256abs hashed (dd ++ sublist 0 len data)) c *
    data_at sh (tarray tuchar (Zlength data))
      (map Vint (map Int.repr data)) d.
Proof.
intros.
  unfold sha256state_.
  Exists (map Vint (hash_blocks init_registers hashed),
                  (Vint (lo_part (bitlength hashed dd + len*8)),
                   (Vint (hi_part (bitlength hashed dd + len*8)),
                    (map Vint (map Int.repr (dd ++ sublist 0 len data))
                       ++list_repeat (Z.to_nat (64 - Zlength dd - len)) Vundef,
                     Vint (Int.repr (Zlength dd + len)))))).
  unfold_data_at 1%nat.
  rewrite prop_true_andp.
  cancel. rewrite !map_app, <- ?sublist_map, <- app_assoc. cancel.
  assert (Zlength (dd ++ sublist 0 len data) < CBLOCKz).
  autorewrite with sublist. pose proof CBLOCKz_eq; omega.
  hnf; unfold s256_Nh, s256_Nl, s256_data, s256_num; simpl.
  rewrite bitlength_eq.
  replace (s256a_len (S256abs hashed dd) + len * 8)
     with (s256a_len (S256abs hashed (dd ++ sublist 0 len data))).
  unfold s256a_regs.
  rewrite S256abs_hashed; auto.
  rewrite S256abs_data; auto.
  split3; auto.
  split3.
  rewrite sublist_app1. rewrite !sublist_map.
  autorewrite with sublist. auto.
  autorewrite with sublist. omega.
  autorewrite with sublist. omega.
  unfold S256abs.
  rewrite !Forall_app. split3; auto.
  apply isbyte_intlist_to_Zlist.
  autorewrite with sublist. auto.
  rewrite <- !bitlength_eq.
  unfold bitlength.
  autorewrite with sublist.
  rewrite !Z.mul_add_distr_r, !Z.add_assoc. auto.
Qed.

Lemma update_inner_if_proof:
 forall (Espec: OracleKind) (hashed: list int) (dd data: list Z)
            (c d: val) (sh: share) (len: Z) kv
 (H: (0 <= len <= Zlength data)%Z)
 (Hsh: readable_share sh)
 (LEN64: (bitlength hashed dd  + len * 8 < two_p 64)%Z)
 (H3 : (Zlength dd < CBLOCKz)%Z)
 (H3' : Forall isbyteZ dd)
 (H4 : (LBLOCKz | Zlength hashed))
 (Hlen : (len <= Int.max_unsigned)%Z),
semax Delta_update_inner_if
  (inv_at_inner_if sh hashed len c d dd data kv)
  update_inner_if
  (overridePost (sha_update_inv sh hashed len c d dd data kv false)
     (function_body_ret_assert tvoid
        (EX  a' : s256abs,
         PROP  (update_abs (sublist 0 len data) (S256abs hashed dd) a')
         LOCAL ()
         SEP  (K_vector kv;
                 sha256state_ a' c; data_block sh data d)))).
Proof.
intros.
name c' _c.
name data_ _data_.
name len' _len.
name data' _data.
name p _p.
name n _n.
name fragment_ _fragment.
unfold sha_update_inv, inv_at_inner_if, update_inner_if.
abbreviate_semax.
 set (k := 64-Zlength dd).
assert (0 < k <= 64) by Omega1.
pose proof I.
unfold data_block; simpl. normalize.
rename H2 into DBYTES.
forward_if.
+
 destruct H as [_ H].
 clear H1; assert (H1: 64 < Int.max_unsigned) by Omega1.
 unfold k.
 clear - H H1 H3 H3' H4 Hlen Hsh H0 H2 DBYTES.
 unfold update_inner_if_then.
 eapply semax_seq'.
  *
   assert_PROP (field_address (tarray tuchar (Zlength data)) [ArraySubsc 0] d = d). {
     entailer!.
     rewrite field_address_offset by auto with field_compatible.
     normalize.
   }
  rename H5 into Hd.
  evar (Frame: list mpred).
  eapply(call_memcpy_tuchar
   (*dst*) Tsh t_struct_SHA256state_st [StructField _data] (Zlength dd)
              (map Vint (map Int.repr dd)
                       ++list_repeat (Z.to_nat k) Vundef)
               c
   (*src*) sh (tarray tuchar (Zlength data)) [ ] 0 (map Int.repr data)  d
   (*len*) k
        Frame);
  try reflexivity; auto; try omega.
  apply Zlength_nonneg.
  subst k; omega.
  unfold_data_at 1%nat.
  entailer!.
  rewrite field_address_offset by auto.
  rewrite !field_address0_offset by (subst k; auto with field_compatible).
  simpl.
  normalize.
  *
  replace (Zlength dd + k)%Z with 64%Z by Omega1.
  subst k.
  unfold splice_into_list; autorewrite with sublist.
 set (k := 64-Zlength dd) in *.
  abbreviate_semax.
  repeat rewrite sublist_map. repeat rewrite <- map_app.
  rewrite <- (data_block_data_field _ (dd ++ sublist 0 k data));
   [
   | rewrite Forall_app; split; auto; apply Forall_sublist; auto
   | rewrite Zlength_app; rewrite Zlength_sublist; MyOmega
   | apply JMeq_refl
   ].
 assert (Zlength (dd ++ sublist 0 k data) = 64%Z)
   by (rewrite Zlength_app, Zlength_sublist; MyOmega).
 assert (Zlength (Zlist_to_intlist (dd ++ sublist 0 k data)) = LBLOCKz)
    by (apply Zlength_Zlist_to_intlist; assumption).
 forward_call (* sha256_block_data_order (c,p); *)
   (hashed, Zlist_to_intlist (dd++(sublist 0 k data)), c,
     (field_address t_struct_SHA256state_st [StructField _data] c),
      Tsh, kv).
 rewrite Zlist_to_intlist_to_Zlist;
   [ | rewrite H5; exists LBLOCKz; reflexivity
     | rewrite Forall_app; split; auto; apply Forall_firstn; auto
   ];   entailer!.
 forward. (* data  += fragment; *)
 forward. (* len -= fragment; *)
 normalize_postcondition.
 eapply semax_post_flipped3.
 evar (Frame: list mpred).
 eapply(call_memset_tuchar
   (*dst*) Tsh t_struct_SHA256state_st [StructField _data] 0
                (map Vint (map Int.repr (dd ++ sublist 0 k data))) c
   (*src*) Int.zero
   (*len*) 64
        Frame); try reflexivity; auto.
  rewrite <- (data_block_data_field _ (dd ++ sublist 0 k data));
   [
   | rewrite Forall_app; split; auto; apply Forall_sublist; auto
   | rewrite Zlength_app; rewrite Zlength_sublist; MyOmega
   | apply JMeq_refl
   ].
  rewrite Zlist_to_intlist_to_Zlist;
   [ | exists LBLOCKz; rewrite H5; reflexivity
     | rewrite Forall_app; split; auto; apply Forall_firstn; auto
   ].
  entailer!.
  rewrite field_address_offset by auto with field_compatible.
  rewrite field_address0_offset by auto with field_compatible.
  reflexivity.
  simpl update_tycon.
  Exists (Zlist_to_intlist (dd ++ sublist 0 k data)).
  erewrite Zlength_Zlist_to_intlist
     by (instantiate (1:=LBLOCKz); assumption).
  rewrite splice_into_list_simplify0;
   [
   | rewrite Zlength_correct, length_list_repeat; reflexivity
   | rewrite !Zlength_map; auto
   ].
  rewrite Zlist_to_intlist_to_Zlist;
    [ | exists LBLOCKz; rewrite H5; reflexivity
     | rewrite Forall_app; split; auto; apply Forall_firstn; auto
    ].
  change 64%Z with CBLOCKz.
  simpl (temp _data _).
  entailer!.
  rewrite field_address0_offset
    by (pose proof LBLOCKz_eq; subst k; auto with field_compatible).
  f_equal. f_equal. unfold k. simpl. Omega1.
  unfold data_block. rewrite prop_true_andp by auto.
  unfold_data_at 1%nat.
  cancel.
+ (* else clause: len < fragment *)
  weak_normalize_postcondition.
  unfold k.
  clear H1; assert (H1: 64 < Int.max_unsigned) by computable.
  clear - H Hsh LEN64 H3 H3' H4 Hlen H0 H1 H2 DBYTES.
  unfold update_inner_if_else;
  simplify_Delta; abbreviate_semax.
  assert_PROP (field_address0 (tarray tuchar (Zlength data)) [ArraySubsc 0] d = d)
     as Hd. {
     entailer!.
     rewrite field_address0_offset by auto with field_compatible.
     normalize.
   }
  eapply semax_seq'.
  evar (Frame: list mpred).
  eapply(call_memcpy_tuchar
   (*dst*) Tsh t_struct_SHA256state_st [StructField _data] (Zlength dd)
                     (map Vint (map Int.repr dd) ++
         list_repeat (Z.to_nat (CBLOCKz - Zlength dd)) Vundef) c
   (*src*) sh (tarray tuchar (Zlength data)) [ ] 0 (map Int.repr data)  d
   (*len*) (len)
        Frame);
    try reflexivity; auto; try omega.
  apply Zlength_nonneg.
  repeat rewrite Zlength_map; unfold k in *; omega.
  entailer!.
  rewrite field_address_offset by auto with field_compatible.
  rewrite field_address0_offset by
   (subst k; auto with field_compatible).
  rewrite offset_offset_val; simpl. rewrite Z.mul_1_l; auto.
  unfold_data_at 1%nat. cancel.
  abbreviate_semax.
  autorewrite with sublist.
  unfold splice_into_list.
  assert (H5: (0 <= Zlength dd < 64)%Z) by (Omega1).
  assert (H6: (k = 64 - Zlength dd)%Z) by (unfold k; auto).
  autorewrite with sublist.
  change 64%Z with CBLOCKz.
  replace (CBLOCKz - (Zlength dd + (CBLOCKz - Zlength dd)))%Z
    with 0%Z by (clear; omega).
  change (list_repeat (Z.to_nat 0) Vundef) with (@nil val).
  rewrite <- app_nil_end.
  autorewrite with sublist.
  rewrite sublist_list_repeat by Omega1.
  clear H5 H6.
  forward. (* c->num = n+(unsigned int)len; *)
  forward. (* return; *)
  Exists (S256abs hashed (dd ++ sublist 0 len data)).
  repeat rewrite TT_andp.
  unfold data_block.
  rewrite (prop_true_andp (Forall _ data)) by auto.
  subst k.
  rewrite (prop_true_andp (_ /\ _));
     [ | split; [apply update_inner_if_update_abs; auto | auto ]].
 rewrite (sepcon_comm (K_vector kv)).
 apply sepcon_derives; [ | auto].
 apply update_inner_if_sha256_state_; auto.
Qed.
