Require Import VST.floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.call_memcpy.
Local Open Scope Z.

Lemma cancel_field_at_array_partial_undef:
 forall {cs: compspecs} sh t t1 n gfs p (al bl: list (reptype t)) blen v1 v2,
  nested_field_type t1 gfs = tarray t n ->
  legal_nested_field t1 gfs ->
  Zlength (al++bl) = n ->
  Zlength bl = blen ->
  JMeq v1 (al++bl) ->
  JMeq v2 (al++repeat (default_val t) (Z.to_nat blen)) ->
  field_at sh t1 gfs v1 p
   |-- field_at sh t1 gfs v2 p.
Proof.
intros.
subst.
assert (exists v1': list (reptype (nested_field_type t1 (gfs SUB 0))), JMeq v1 v1').
clear - H.
rewrite nested_field_type_ind.
revert v1 H.
forget (nested_field_type t1 gfs) as tx.
intros. subst. simpl.
revert v1. rewrite reptype_eq.  simpl.
intros; eauto.
destruct H1 as [v1' H1].
assert (exists v2': list (reptype (nested_field_type t1 (gfs SUB 0))), JMeq v2 v2').
clear - H.
rewrite nested_field_type_ind.
revert v2 H.
forget (nested_field_type t1 gfs) as tx.
intros. subst. simpl.
revert v2. rewrite reptype_eq.  simpl.
intros; eauto.
destruct H2 as [v2' H2].
  pose proof (Zlength_nonneg al);
  pose proof (Zlength_nonneg bl).
rewrite (field_at_Tarray sh t1 gfs t (Zlength (al++bl)) noattr v1 v1')
  by (auto; apply Zlength_nonneg).
rewrite (field_at_Tarray sh t1 gfs t (Zlength (al++bl)) noattr v2 v2')
  by (auto; apply Zlength_nonneg).
rewrite (add_andp _ _ (array_at_local_facts _ _ _ _ _ _ _)).
normalize.
rewrite (split2_array_at _ _ _ 0 (Zlength al) (Zlength (al++bl)))
  by (try lia; rewrite Zlength_app; lia).
rewrite (split2_array_at _ _ _ 0 (Zlength al) (Zlength (al++bl))).
2: rewrite Zlength_app; lia.
2:{
  apply (JMeq_trans (JMeq_sym H4)) in H2.
  erewrite <- list_func_JMeq with (f := Zlength); [| | exact H2].
  2: rewrite nested_field_type_ind; rewrite H; auto.
  autorewrite with sublist. auto.
} 
apply (JMeq_trans (JMeq_sym H3)) in H1.
apply (JMeq_trans (JMeq_sym H4)) in H2.
apply sepcon_derives.
f_equiv.
rewrite Z.sub_0_r.
clear - H1 H2 H5 H.
revert v1' v2' H1 H2.
rewrite nested_field_type_ind.
rewrite H.
simpl.
intros.
apply JMeq_eq in H1; apply JMeq_eq in H2.
rewrite <- H1. rewrite <- H2.
autorewrite with sublist. auto.
eapply derives_trans; [apply array_at_array_at_ | ].
unfold array_at_.
f_equiv.
rewrite Z.sub_0_r.
clear - H2 H5 H.
revert v2' H2.
rewrite nested_field_type_ind.
rewrite H.
simpl.
intros. apply JMeq_eq in H2; rewrite <- H2.
rewrite sublist_app2 by lia.
rewrite Z.sub_diag.
autorewrite with sublist.
auto.
Qed.

Definition Body_final_if1 :=
            (Ssequence
              (Scall None
                (Evar _memset (Tfunction
                                ((tptr tvoid) :: tint :: tuint :: nil)
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
                                                   ((tptr (Tstruct _SHA256state_st noattr)) ::
                                                    (tptr tvoid) :: nil)
                                                   tvoid cc_default))
                  ((Etempvar _c (tptr (Tstruct _SHA256state_st noattr))) ::
                   (Etempvar _p (tptr tuchar)) :: nil)))).

Lemma Byte_repr_128:  Vubyte (Byte.repr 128) = Vint (Int.repr 128).
Proof.
reflexivity.
Qed.

Lemma final_if1:
forall Espec (a : s256abs) (md c : val) (wsh shmd : share) (gv : globals) (r_data : list val)
 (Hwsh: writable_share wsh),
sublist 0 (Zlength (s256a_data a)) r_data = map Vubyte (s256a_data a) ->
Zlength r_data = CBLOCKz ->
semax(OK_spec := Espec) ⊤ (func_tycontext f_SHA256_Final Vprog Gtot nil)
  (PROP ( )
   LOCAL (temp _n (Vint (Int.repr (Zlength (s256a_data a) + 1)));
   temp _p (field_address t_struct_SHA256state_st [StructField _data] c); 
   gvars gv; temp _md md; temp _c c)
   (*LOCAL (temp _n (Vint (Int.repr (Zlength (s256a_data a) + 1)));
   temp _p (field_address t_struct_SHA256state_st [StructField _data] c);
   temp _md md; temp _c c; gvars gv)*)
   SEP (K_vector gv;
   field_at wsh t_struct_SHA256state_st [StructField _h] (map Vint (s256a_regs a)) c;
   field_at wsh t_struct_SHA256state_st [StructField _Nl] (Vint (lo_part (s256a_len a))) c;
   field_at wsh t_struct_SHA256state_st [StructField _Nh] (Vint (hi_part (s256a_len a))) c;
   field_at wsh t_struct_SHA256state_st [StructField _data]
     ((map Vubyte (s256a_data a) ++ [Vint (Int.repr 128)]) ++ sublist (Zlength (s256a_data a) + 1) CBLOCKz r_data) c;
   field_at wsh t_struct_SHA256state_st [StructField _num]
     (Vint (Int.repr (Zlength (s256a_data a)))) c; memory_block shmd 32 md))
  (Sifthenelse
     (Ebinop Ogt (Etempvar _n tuint)
        (Ebinop Osub
           (Ebinop Omul (Econst_int (Int.repr 16) tint) (Econst_int (Int.repr 4) tint) tint)
           (Econst_int (Int.repr 8) tint) tint) tint) Body_final_if1 Sskip)
  (normal_ret_assert (
   EX hashed': list int, EX dd': list byte, EX pad: Z,
   PROP  (pad=0%Z \/ dd'=nil;
              Zlength dd' + 8 <= CBLOCKz;
              0 <= pad < 8;
              (LBLOCKz | Zlength hashed');
              intlist_to_bytelist hashed' ++ dd' =
              intlist_to_bytelist (s256a_hashed a) ++  (s256a_data a)
                  ++ [Byte.repr 128%Z] ++ repeat Byte.zero (Z.to_nat pad))
   LOCAL
   (temp _n (Vint (Int.repr (Zlength dd')));
    temp _p (field_address t_struct_SHA256state_st [StructField _data] c);
    temp _md md; temp _c c;
    gvars gv)
   SEP  (data_at wsh t_struct_SHA256state_st
           (map Vint (hash_blocks init_registers hashed'),
            (Vint (lo_part (s256a_len a)),
             (Vint (hi_part (s256a_len a)),
              (map Vubyte dd'
                 ++ repeat Vundef (Z.to_nat (CBLOCKz - Zlength dd')),
               Vundef))))
           c;
           K_vector gv;
           memory_block shmd 32 md))).
Proof.
intros.
assert (H3 := s256a_data_Zlength_less a).
assert (Hddlen: 0 <= Zlength (s256a_data a) < 64) by Omega1.
assert (CB := CBLOCKz_eq).
abbreviate_semax.
forward_if.
* (* then-clause *)
 make_sequential.
 unfold POSTCONDITION, abbreviate.
 normalize_postcondition.
 rename H1 into H2.
 assert (H1: Zlength (s256a_data a) + 1 > 16 * 4 - 8) by lia.
gather_SEP 
 (field_at _ _ [StructField _h] _ _)
 (field_at _ _ [StructField _Nl] _ _)
 (field_at _ _ [StructField _Nh] _ _)
 (field_at _ _ [StructField _data] _ _)
 (field_at _ _ [StructField _num] _ _).
replace_SEP 0  (data_at wsh t_struct_SHA256state_st
           (map Vint (hash_blocks init_registers (s256a_hashed a)),
           (Vint (lo_part (s256a_len a)),
           (Vint (hi_part (s256a_len a)),
           (map Vubyte (s256a_data a) ++
            [Vint (Int.repr 128)] ++
            repeat Vundef (Z.to_nat (64 - (Zlength (s256a_data a) + 1))),
	        Vint (Int.repr (Zlength (s256a_data a))))))) c).
 unfold_data_at (data_at _ _ _ _).
 rewrite field_at_data_at with (gfs := [StructField _data]) by reflexivity.
 unfold data_at.
 go_lower; simpl; cancel. (* saturate_local makes entailer! is REALLY slow, but (go_lower; cancel) is fast. *)
 change (cons (Vint (Int.repr 128))) with (app [Vint (Int.repr 128)]).
 rewrite !(app_assoc _ [_]).
 rewrite app_nil_r.
 rewrite field_at_data_at with (gfs := [StructField _data]) by reflexivity.
 eapply cancel_field_at_array_partial_undef; try reflexivity; try apply JMeq_refl.
 autorewrite with sublist. lia.
 autorewrite with sublist; apply JMeq_refl.
pattern (s256a_len a); rewrite <- (S256abs_recombine a) at 1 by auto.
rewrite <- bitlength_eq.

clear H0.
assert (H4 := s256a_hashed_divides a).
forget (s256a_hashed a) as hashed.
forget (s256a_data a) as dd.
clear - Hwsh H4 H3 H1.
{
assert (Hddlen: (0 <= Zlength dd < CBLOCKz)%Z) by Omega1.
set (ddlen := Zlength dd) in *.
set (fill_len := (64 - (ddlen + 1))).
 unfold Body_final_if1; abbreviate_semax.
change CBLOCKz with 64 in Hddlen.
unfold_data_at (data_at _ _ _ _).
freeze FR1 := -(field_at wsh t_struct_SHA256state_st (DOT _data) _ c).
eapply semax_seq'.
  eapply (call_memset_tuchar wsh
   (*dst*) t_struct_SHA256state_st [StructField _data] (ddlen+1)
                _ c
   (*src*) Int.zero
   (*len*) (CBLOCKz - (ddlen+1))
   [FRZL FR1]); try reflexivity; try lia; auto.
 split; try lia. change CBLOCKz with 64; rep_lia.
 change CBLOCKz with 64; lia.
 entailer!. {
 rewrite field_address0_offset by auto with field_compatible.
 rewrite field_address_offset by auto with field_compatible.
 simpl. normalize.
}
thaw' FR1; simpl; Intros.
 abbreviate_semax.
replace (ddlen + 1 + (CBLOCKz - (ddlen + 1))) with CBLOCKz by (clear; lia).
change 64 with CBLOCKz.
pose (ddz := ((dd ++ [Byte.repr 128]) ++ repeat Byte.zero (Z.to_nat (CBLOCKz-(ddlen+1))))).

replace (splice_into_list (ddlen + 1) CBLOCKz
           (repeat (Vint Int.zero) (Z.to_nat (CBLOCKz - (ddlen + 1))))
           (map Vubyte dd ++
            Vint (Int.repr 128) :: repeat Vundef (Z.to_nat fill_len)))
  with  (map Vubyte ddz).
2:{
 clear - Hddlen. subst ddz fill_len ddlen. rewrite !map_app.
 change (cons (Vint (Int.repr 128))) with (app [Vint (Int.repr 128)]).
 rewrite map_repeat.
 rewrite ?app_assoc.
 unfold splice_into_list.
 change CBLOCKz with 64 in *.
 autorewrite with sublist. reflexivity. 
}
pose (ddzw := bytelist_to_intlist ddz).
assert (H0': Zlength ddz = CBLOCKz). {
  clear - Hddlen H3. subst ddz ddlen.
  autorewrite with sublist. clear; lia.
}
assert (H1': Zlength ddzw = LBLOCKz). {
  unfold ddzw.
  apply Zlength_bytelist_to_intlist. apply H0'.
}
assert (HU:  ddz = intlist_to_bytelist ddzw). {
  unfold ddzw; rewrite bytelist_to_intlist_to_bytelist; auto.
  rewrite H0'.  exists LBLOCKz; reflexivity.
}
clear H0'.
clearbody ddzw.
forward.  (* n=0; *)
erewrite field_at_data_at with (gfs := [StructField _data]) by reflexivity.
rewrite semax_seq_skip.
assert (Zlength (hash_blocks init_registers hashed) = 8)
 by (rewrite Zlength_length;[apply length_hash_blocks|]; auto).
forward_call (* sha256_block_data_order (c,p); *)
  (hash_blocks init_registers hashed, ddzw, c, wsh,
    field_address t_struct_SHA256state_st [StructField _data] c,
    wsh, gv).
{
  apply sepcon_derives; [ | cancel].
  unfold data_block.
  autorewrite with sublist.
  rewrite H1', <- HU. change (LBLOCKz*4)%Z with 64.
  cancel.
}
 rewrite hash_blocks_last by auto.
 set (pad := (CBLOCKz - (ddlen+1))%Z) in *.
 Exists (hashed ++ ddzw) (@nil byte) pad.
 entailer!.
*
split.
 + rewrite Zlength_app.
  apply Z.divide_add_r; auto. rewrite H1'.
  apply Z.divide_refl.
 +
  rewrite intlist_to_bytelist_app.
  autorewrite with sublist.
  f_equal.
  rewrite <- HU.
  repeat rewrite map_app.
  repeat rewrite <- app_assoc.
 f_equal.
*
 unfold_data_at (data_at _ _ _ _).
 unfold data_block. simpl.
 Intros.
 cancel.
 rewrite field_at_data_at.
 simpl.
 rewrite Zlength_intlist_to_bytelist, H1'.
 change (LBLOCKz * 4)%Z with 64%Z.
 eapply derives_trans; [apply data_at_data_at_ | ].
 apply derives_refl.
}
* (* else-clause *)
forward. (* skip; *)
Exists (s256a_hashed a) ((s256a_data a) ++ [Byte.repr 128]) 0.
unfold_data_at (data_at _ _ _ _).
Time entailer!. (* 10.2 secs (3.8u, 0.s) *)
split3.
autorewrite with sublist. lia.
apply s256a_hashed_divides.
autorewrite with sublist; auto.
rewrite !(field_at_data_at _ _ [_]).
eapply cancel_field_at_array_partial_undef; try reflexivity; try apply JMeq_refl.
autorewrite with sublist; Omega1.
autorewrite with sublist.
apply eq_JMeq. f_equal. rewrite !map_app. reflexivity.
Qed.
