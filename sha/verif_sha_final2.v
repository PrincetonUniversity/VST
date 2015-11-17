Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.call_memcpy.
Local Open Scope Z.
Local Open Scope logic.

Definition Delta_final_if1 :=
 (initialized _n  (initialized _p
     (func_tycontext f_SHA256_Final Vprog Gtot))).

Definition Body_final_if1 := 
  (Ssequence
              (Scall None
                (Evar _memset (Tfunction
                                (Tcons (tptr tvoid)
                                  (Tcons tint (Tcons tuint Tnil)))
                                (tptr tvoid) cc_default))
                ((Ebinop Oadd (Etempvar _p (tptr tuchar)) (Etempvar _n tuint)
                   (tptr tuchar)) :: (Econst_int (Int.repr 0) tint) ::
                 (Ebinop Osub
                   (Ebinop Omul (Econst_int (Int.repr 16) tint)
                     (Econst_int (Int.repr 4) tint) tint) (Etempvar _n tuint)
                   tuint) :: nil))
              (Ssequence
                (Sset _n (Econst_int (Int.repr 0) tint))
                (Scall None
                  (Evar _sha256_block_data_order (Tfunction
                                                   (Tcons
                                                     (tptr t_struct_SHA256state_st)
                                                     (Tcons (tptr tvoid)
                                                       Tnil)) tvoid cc_default))
                  ((Etempvar _c (tptr t_struct_SHA256state_st)) ::
                   (Etempvar _p (tptr tuchar)) :: nil)))).

Definition invariant_after_if1 hashed (dd: list Z) c md shmd kv:= 
   @exp (environ -> mpred) _ _ (fun hashed': list int =>
   @exp (environ -> mpred) _ _ (fun dd': list Z =>
   @exp (environ -> mpred) _ _ (fun pad: Z =>
   PROP  (Forall isbyteZ dd';
              pad=0%Z \/ dd'=nil;
              (length dd' + 8 <= CBLOCK)%nat;
              (0 <= pad < 8)%Z;
              (LBLOCKz | Zlength hashed')%Z;
              intlist_to_Zlist hashed' ++ dd' =
              intlist_to_Zlist hashed ++  dd 
                  ++ [128%Z] ++ list_repeat (Z.to_nat pad) 0)
   LOCAL 
   (temp _n (Vint (Int.repr (Zlength dd')));
    temp _p (field_address t_struct_SHA256state_st [StructField _data] c);
    temp _md md; temp _c c;
    gvar _K256 kv)
   SEP  (data_at Tsh t_struct_SHA256state_st 
           (map Vint (hash_blocks init_registers hashed'),
            (Vint (lo_part (bitlength hashed dd)),
             (Vint (hi_part (bitlength hashed dd)),
              (map Vint (map Int.repr dd') 
                 ++ list_repeat (Z.to_nat (CBLOCKz - Zlength dd')) Vundef,
               Vundef))))
           c;
           K_vector kv;
           memory_block shmd 32 md)))).

Lemma ifbody_final_if1:
  forall (Espec : OracleKind) (hashed : list int) (md c : val) (shmd : share)
  (dd : list Z) (kv: val)
 (H4: (LBLOCKz  | Zlength hashed))
 (H3: Zlength dd < CBLOCKz)
 (H0 : Zlength dd + 1 > 16 * 4 - 8)
 (DDbytes: Forall isbyteZ dd),
  semax Delta_final_if1
  (PROP  ()
   LOCAL 
   (temp _n (Vint (Int.repr (Zlength dd + 1)));
    temp _p (field_address t_struct_SHA256state_st [StructField _data] c);
    temp _md md; temp _c c;
    gvar _K256 kv)
   SEP 
   (data_at Tsh t_struct_SHA256state_st
       (map Vint (hash_blocks init_registers hashed),
        (Vint (lo_part (bitlength hashed dd)), 
         (Vint (hi_part (bitlength hashed dd)),
          (map Vint (map Int.repr dd) ++ [Vint (Int.repr 128)] ++
            list_repeat (Z.to_nat (64 - (Zlength dd + 1))) Vundef,
           Vint (Int.repr (Zlength dd))))))
      c;
      K_vector kv;
      memory_block shmd 32 md))
  Body_final_if1
  (normal_ret_assert (invariant_after_if1 hashed dd c md shmd kv)).
Proof.
assert (H:=True).
name md_ _md.
name c_ _c.
name p _p.
name n _n.
name cNl _cNl.
name cNh _cNh.
intros.
abbreviate_semax.
assert (Hddlen: (0 <= Zlength dd < CBLOCKz)%Z) by Omega1.
set (ddlen := Zlength dd) in *.
set (fill_len := (64 - (ddlen + 1))).
 unfold Delta_final_if1; simplify_Delta; unfold Body_final_if1; abbreviate_semax.
change CBLOCKz with 64 in Hddlen.
unfold_data_at 1%nat. 
eapply semax_seq'.
evar (Frame: list mpred).
evar (V: list val).
  eapply (call_memset_tuchar Tsh
   (*dst*) t_struct_SHA256state_st [StructField _data] (ddlen+1)
                V c
   (*src*) Int.zero
   (*len*) (CBLOCKz - (ddlen+1))
        Frame); try reflexivity; try omega; auto.
 split; try omega. change CBLOCKz with 64; repable_signed.
 change CBLOCKz with 64; omega.
 subst V.
 entailer!. {
 clear - Hddlen H11.
 rewrite field_address0_offset by auto with field_compatible.
 rewrite field_address_offset by auto with field_compatible.
 simpl. normalize. 
}
 abbreviate_semax.
replace (ddlen + 1 + (CBLOCKz - (ddlen + 1))) with CBLOCKz by (clear; omega).
change 64 with CBLOCKz.
pose (ddz := ((map Int.repr dd ++ [Int.repr 128]) ++ list_repeat (Z.to_nat (CBLOCKz-(ddlen+1))) Int.zero)).

replace (splice_into_list (ddlen + 1) CBLOCKz CBLOCKz
           (list_repeat (Z.to_nat (CBLOCKz - (ddlen + 1))) (Vint Int.zero))
           (map Vint (map Int.repr dd) ++
            Vint (Int.repr 128) :: list_repeat (Z.to_nat fill_len) Vundef))
  with  (map Vint ddz).
Focus 2. {
 clear - Hddlen. subst ddz fill_len ddlen. rewrite !map_app.
 change (cons (Vint (Int.repr 128))) with (app [Vint (Int.repr 128)]).
 rewrite map_list_repeat.
 rewrite <- ?app_ass.
 unfold splice_into_list.
 change CBLOCKz with 64 in *.
 autorewrite with sublist. reflexivity.
} Unfocus.
pose (ddzw := Zlist_to_intlist (map Int.unsigned ddz)).
assert (H0': Zlength ddz = CBLOCKz). {
  clear - Hddlen H3. subst ddz ddlen. 
  autorewrite with sublist. clear; omega.
}
assert (H1': Zlength ddzw = LBLOCKz). {
  unfold ddzw.
  apply Zlength_Zlist_to_intlist. rewrite Zlength_map. apply H0'.
}
assert (HU: map Int.unsigned ddz = intlist_to_Zlist ddzw). {
  unfold ddzw; rewrite Zlist_to_intlist_to_Zlist; auto.
  rewrite Zlength_map, H0'; exists LBLOCKz; reflexivity.
  unfold ddz; repeat rewrite map_app; repeat rewrite Forall_app; repeat split; auto.
  apply Forall_isbyteZ_unsigned_repr; auto.
  repeat constructor. computable.
  apply Forall_map, Forall_list_repeat. simpl.
  rewrite Int.unsigned_zero. split; clear; omega.
}
clear H0'.
clearbody ddzw.
forward.  (* n=0; *)
erewrite field_at_data_at with (gfs := [StructField _data]) by reflexivity.
rewrite semax_seq_skip.
forward_call (* sha256_block_data_order (c,p); *)
  (hashed, ddzw, c,
    field_address t_struct_SHA256state_st [StructField _data] c,
    Tsh, kv).
{
  simpl.
  repeat rewrite sepcon_assoc; apply sepcon_derives; [ | cancel].
  unfold data_block.
  rewrite prop_true_andp by apply isbyte_intlist_to_Zlist.
  autorewrite with sublist.
  rewrite H1', <- HU. change (LBLOCKz*4)%Z with 64.
  rewrite map_map with (g := Int.repr).
  replace (fun x => Int.repr (Int.unsigned x)) with (@id int) by 
    (extensionality xx; rewrite Int.repr_unsigned; auto).
  rewrite map_id.
  apply derives_refl.
}
 set (pad := (CBLOCKz - (ddlen+1))%Z) in *.
 Exists (hashed ++ ddzw) (@nil Z) pad.
 entailer!.
*
split; [ Omega1 |].
split. 
 + rewrite initial_world.Zlength_app.
  apply Z.divide_add_r; auto. rewrite H1'.
  apply Z.divide_refl.
 + 
  rewrite intlist_to_Zlist_app.
  autorewrite with sublist.
  f_equal.
  rewrite <- HU.
  unfold ddz.
  repeat rewrite map_app.
  repeat rewrite app_ass.
 f_equal.
 clear - DDbytes; induction dd; simpl; auto.
 inv DDbytes; f_equal; auto.
 apply Int.unsigned_repr; unfold isbyteZ in H1; repable_signed.
 rewrite map_list_repeat. reflexivity.
*
 rewrite Zlength_nil, Z.sub_0_r.
 unfold_data_at 1%nat.
 unfold data_block. simpl.
 Intros.
 cancel.
 rewrite field_at_data_at.
 simpl.
 rewrite Zlength_intlist_to_Zlist, H1'.
 change (LBLOCKz * 4)%Z with 64%Z.
 eapply derives_trans; [apply data_at_data_at_ | ].
 apply derives_refl.
Qed.


