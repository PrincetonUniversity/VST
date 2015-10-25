Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import JMeq.
Require Import sha.call_memcpy.

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
       temp _data d; temp _c c; 
       temp _len (Vint (Int.repr len));
       gvar  _K256 kv)
   SEP  (`(data_at Tsh t_struct_SHA256state_st
                 (map Vint (hash_blocks init_registers hashed),
                  (Vint (lo_part (bitlength hashed dd + len*8)),
                   (Vint (hi_part (bitlength hashed dd + len*8)),
                    (map Vint (map Int.repr dd) ++ list_repeat (Z.to_nat (CBLOCKz-Zlength dd)) Vundef,
                     Vint (Int.repr (Zlength dd))))))
               c);
   `(K_vector kv);
   `(data_block sh data d)))).

Definition  S_struct (hashed: list int) (len:Z) (dd: list Z) (num: val) :=
    data_at Tsh t_struct_SHA256state_st
                 (map Vint (hash_blocks init_registers hashed),
                  (Vint (lo_part len),
                   (Vint (hi_part len),
                    (map Vint (map Int.repr dd),
                     num)))).

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
   SEP  (`(K_vector kv);
           `(@data_at CompSpecs Tsh t_struct_SHA256state_st
                 ((map Vint (hash_blocks init_registers (hashed++blocks)),
                  (Vint (lo_part (bitlength hashed dd + len*8)),
                   (Vint (hi_part (bitlength hashed dd + len*8)),
                    (list_repeat (Z.to_nat CBLOCKz) Vundef, Vundef)))) : reptype t_struct_SHA256state_st)
               c);
   `(data_block sh data d))).

Definition Delta_update_inner_if : tycontext.
simplify_Delta_from
  (initialized _fragment
     (initialized _p
        (initialized _n
           (initialized _data (func_tycontext f_SHA256_Update Vprog Gtot))))).
Defined.

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

Lemma field_at_cancel_undef_example:
  forall  (d': list val) d c, 
  Zlength d' = 64%Z ->
  JMeq d' d ->
  field_at Tsh t_struct_SHA256state_st [StructField _data] d c |--
  field_at Tsh t_struct_SHA256state_st [StructField _data] (list_repeat (Z.to_nat 64) Vundef) c.
Proof.
  intros.
  apply field_at_stronger.
  apply stronger_array_ext.
  change (list val) in d. apply JMeq_eq in H0. subst.
  erewrite !unfold_reptype_elim by reflexivity.
  rewrite Zlength_list_repeat, Z.max_r by omega.
  auto.
  intros.
  erewrite !unfold_reptype_elim by reflexivity.
 rewrite Znth_list_repeat_inrange by omega.
  intros sh p.
  apply data_at_data_at_.
Qed.

Lemma update_inner_if_then_proof:
 forall (Espec : OracleKind) (hashed : list int)
          (dd data : list Z) (c d: val) (sh: share) (len: Z) kv
   (H : (len <= Zlength data)%Z)
   (H3 : (Zlength dd < CBLOCKz)%Z)
   (H3' : Forall isbyteZ dd)
   (H4 : (LBLOCKz | Zlength hashed))
   (Hlen : (len <= Int.max_unsigned)%Z)
   (Hsh: readable_share sh)
   (c' : name _c) (data_ : name _data) (len' : name _len) 
   (data' : name _data) (p : name _p) (n : name _n)
   (fragment_ : name _fragment),
  let k := (64 - Zlength dd)%Z in
  forall (H0: (0 < k <= 64)%Z)
       (H1: (64 < Int.max_unsigned)%Z)
       (H2: (len >= k)%Z)
       (DBYTES: Forall isbyteZ data),
semax Delta_update_inner_if
  (PROP  ()
   LOCAL 
   (temp _fragment (Vint (Int.repr k));
    temp _p (field_address t_struct_SHA256state_st [StructField _data] c);
    temp _n (Vint (Int.repr (Zlength dd)));
    temp _data d; temp _c c; temp _len (Vint (Int.repr (len)));
    gvar  _K256 kv)
   SEP 
   (`(data_at Tsh t_struct_SHA256state_st
                 (map Vint (hash_blocks init_registers hashed),
                  (Vint (lo_part (bitlength hashed dd + len*8)),
                   (Vint (hi_part (bitlength hashed dd + len*8)),
                    (map Vint (map Int.repr dd)
                       ++list_repeat (Z.to_nat k) Vundef,
                     Vint (Int.repr (Zlength dd))))))
               c);
   `(K_vector kv);
   `(data_at sh (tarray tuchar (Zlength data)) (map Vint (map Int.repr data)) d)))
  update_inner_if_then
  (normal_ret_assert (sha_update_inv sh hashed len c d dd data kv false)).
Proof.
 intros.
  unfold update_inner_if_then.
  abbreviate_semax.
match goal with |- semax _ (PROP() (LOCALx ?Q (SEPx _))) _ _ =>
 apply semax_seq'
 with (PROP() (LOCALx Q 
        (SEP (`(data_at Tsh t_struct_SHA256state_st 
                ( (map Vint (hash_blocks init_registers hashed),
                  (Vint (lo_part (bitlength hashed dd + len*8)),
                   (Vint (hi_part (bitlength hashed dd + len*8)),
                    (map Vint (map Int.repr dd) ++
                      sublist 0 k (map Vint (map Int.repr data)),
                     Vint (Int.repr (Zlength dd))))))
                   : @reptype CompSpecs t_struct_SHA256state_st)
               c);
      `(K_vector kv);
      `(data_at sh (tarray tuchar (Zlength data)) (map Vint (map Int.repr data)) d)))))
end.
eapply semax_post_flipped'.
*
  assert_PROP (field_address (tarray tuchar (Zlength data)) [ArraySubsc 0] d = d). {
    entailer!.
    unfold field_address; rewrite if_true; normalize.
    eapply field_compatible_cons_Tarray; try reflexivity; auto; omega.
  }
 rename H5 into Hd.
  evar (Frame: list (LiftEnviron mpred)).
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
  unfold data_at. unfold_field_at 1%nat.
  entailer!.
  unfold field_address0, field_address.
  rewrite !if_true; auto.
  rewrite nested_field_offset2_ind at 1.
+
  destruct c; try (destruct H13 as [H13 _]; contradiction H13).
  destruct d; try (destruct H17 as [H17 _]; contradiction H17).
  unfold offset_val.
  set (t := nested_field_type2 t_struct_SHA256state_st [StructField _data]).
  compute in t. subst t.
  set (a := nested_field_offset2 t_struct_SHA256state_st [StructField _data]).
  unfold gfield_offset.
   unfold sem_add_pi. unfold force_val.
  split; f_equal.
  rewrite Int.add_assoc. f_equal. rewrite add_repr.
  f_equal. simpl sizeof. omega.
 simpl. apply Int.add_zero.
+
 split3; auto.
 clear; compute; intuition.
 apply Zlength_nonneg.
 MyOmega.
+
 eapply field_compatible0_cons_Tarray.
 reflexivity. auto. omega.
+
 eapply field_compatible0_cons_Tarray.
 reflexivity. auto. subst k; omega.
*
  unfold data_at.   unfold_field_at 7%nat.
  entailer!.
  replace (Zlength dd + k)%Z with 64%Z by Omega1.
  subst k.
  unfold splice_into_list; autorewrite with sublist.
  auto.
*
change (PTree.tree funspec)  with (PTree.t funspec) in Delta_specs.
simplify_Delta.
  abbreviate_semax.
  repeat rewrite sublist_map. repeat rewrite <- map_app.
  unfold data_at.   unfold_field_at 1%nat.
  rewrite <- (data_block_data_field _ (dd ++ sublist 0 k data));
 [
 | rewrite Forall_app; split; auto; apply Forall_sublist; auto
 | rewrite Zlength_app; rewrite Zlength_sublist; MyOmega
 | reflexivity
 ].
 assert (Zlength (dd ++ sublist 0 k data) = 64%Z)
  by (rewrite Zlength_app, Zlength_sublist; MyOmega).
 assert (Zlength (Zlist_to_intlist (dd ++ sublist 0 k data)) = LBLOCKz)
   by (apply Zlength_Zlist_to_intlist; assumption).
 forward_call (* sha256_block_data_order (c,p); *)
   (hashed, Zlist_to_intlist (dd++(sublist 0 k data)), c,
     (field_address t_struct_SHA256state_st [StructField _data] c),
      Tsh, kv). {
 rewrite Zlist_to_intlist_to_Zlist;
 [ | rewrite H5; exists LBLOCKz; reflexivity
   | rewrite Forall_app; split; auto; apply Forall_firstn; auto
 ].
 entailer!.
}
simpl map. (* SHOULD NOT BE NECESSARY *)
forward. (* data  += fragment; *)
forward. (* len -= fragment; *)
  normalize_postcondition.
eapply semax_post_flipped3.
evar (Frame: list (LiftEnviron mpred)).
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
 | reflexivity
 ].
 rewrite Zlist_to_intlist_to_Zlist;
 [ | exists LBLOCKz; rewrite H5; reflexivity
   | rewrite Forall_app; split; auto; apply Forall_firstn; auto
 ].
 entailer!.
 unfold field_address, field_address0; rewrite !if_true; auto.
 eapply field_compatible0_cons_Tarray; [reflexivity | auto | Omega1 ].
 Exists (Zlist_to_intlist (dd ++ sublist 0 k data)).

 erewrite Zlength_Zlist_to_intlist
  by (instantiate (1:=LBLOCKz); assumption).
 simpl update_tycon; rewrite insert_local.
 rewrite splice_into_list_simplify0;
 [ 
 | rewrite Zlength_correct, length_list_repeat; reflexivity
 | rewrite !Zlength_map; auto
].
unfold data_at. unfold_field_at 7%nat.
 rewrite Zlist_to_intlist_to_Zlist;
 [ | exists LBLOCKz; rewrite H5; reflexivity
   | rewrite Forall_app; split; auto; apply Forall_firstn; auto
 ].
change 64%Z with CBLOCKz.
entailer!.
unfold field_address0.
rewrite if_true.
f_equal. f_equal.
unfold k.
change (LBLOCKz * 4)%Z with 64%Z.
rewrite nested_field_offset2_ind.
simpl. clear; omega.
split; auto. constructor. constructor. Omega1. Omega1.
eapply field_compatible0_cons_Tarray; try reflexivity; auto; Omega1.
unfold data_block. normalize.
Qed.
