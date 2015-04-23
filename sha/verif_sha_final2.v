Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Local Open Scope Z.
Local Open Scope logic.

Definition Delta_final_if1 : tycontext.
simplify_Delta_from
 (initialized _n  (initialized _p
     (func_tycontext f_SHA256_Final Vprog Gtot))).
Defined.

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
   (EX hashed':list int, EX dd': list Z, EX pad:Z,
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
   SEP  (`(data_at Tsh t_struct_SHA256state_st 
           (map Vint (hash_blocks init_registers hashed'),
            (Vint (lo_part (bitlength hashed dd)),
             (Vint (hi_part (bitlength hashed dd)),
              (map Vint (map Int.repr dd'),
               Vundef))))
           c);
         `(K_vector kv);
         `(memory_block shmd (Int.repr 32) md))).

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
   (`(data_at Tsh t_struct_SHA256state_st
       (map Vint (hash_blocks init_registers hashed),
        (Vint (lo_part (bitlength hashed dd)), 
         (Vint (hi_part (bitlength hashed dd)),
          (map Vint (map Int.repr dd) ++ [Vint (Int.repr 128)],
           Vint (Int.repr (Zlength dd))))))
      c);
    `(K_vector kv);
    `(memory_block shmd (Int.repr 32) md)))
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
assert (Hddlen: (0 <= Zlength dd < CBLOCKz)%Z) by Omega1.
set (ddlen := Zlength dd) in *.
 unfold Delta_final_if1; simplify_Delta; unfold Body_final_if1; abbreviate_semax.
change CBLOCKz with 64 in Hddlen.
unfold_data_at 1%nat.
replace (field_at Tsh t_struct_SHA256state_st [StructField _data]
           (map Vint (map Int.repr dd) ++ [Vint (Int.repr 128)]) c) with
  (field_at Tsh t_struct_SHA256state_st [StructField _data]
          ((map Vint (map Int.repr dd) ++ [Vint (Int.repr 128)]) ++
            list_repeat (Z.to_nat (64 - (ddlen + 1))) Vundef ++ []) c).
Focus 2. {
  rewrite app_nil_r.
  erewrite field_at_data_equal; [reflexivity |].
  apply data_equal_sym, data_equal_list_repeat_default.
} Unfocus.
erewrite array_seg_reroot_lemma with (gfs := [StructField _data]) (lo := ddlen + 1) (hi := 64);
  [| omega | omega | reflexivity | omega | reflexivity | reflexivity 
   | rewrite Zlength_app, !Zlength_map; reflexivity
   | rewrite Zlength_correct, length_list_repeat; rewrite Z2Nat.id by omega; reflexivity ].
normalize.
change (64-(ddlen+1)) with (CBLOCKz-(ddlen+1)).


 assert (CBEQ := CBLOCKz_eq).

forward_call' (* memset (p+n,0,SHA_CBLOCK-n); *)
   ((Tsh,
     (field_address0 t_struct_SHA256state_st
       [ArraySubsc (ddlen + 1); StructField _data] c),
     (CBLOCKz - (ddlen + 1)))%Z,
     Int.zero) vret.

  apply prop_right.
  unfold field_address, field_address0; rewrite !if_true; auto.
  erewrite nested_field_offset2_Tarray by reflexivity.
  normalize.
  eapply field_compatible0_cons_Tarray; [reflexivity | auto | Omega1].
  split; auto. repable_signed.

gather_SEP 1%Z 0%Z 2%Z.
pose (ddz := ((map Int.repr dd ++ [Int.repr 128]) ++ list_repeat (Z.to_nat (CBLOCKz-(ddlen+1))) Int.zero)).
replace_SEP 0%Z (`(field_at Tsh t_struct_SHA256state_st [StructField _data] (map Vint ddz) c)).
{
  unfold ddz.
  rewrite map_app.
  replace (map Vint (map Int.repr dd ++ [Int.repr 128]) ++
            map Vint (list_repeat (Z.to_nat (CBLOCKz - (ddlen + 1))) Int.zero)) with
    (map Vint (map Int.repr dd ++ [Int.repr 128]) ++
            map Vint (list_repeat (Z.to_nat (CBLOCKz - (ddlen + 1))) Int.zero) ++ [])
    by (rewrite app_nil_r; reflexivity).
  erewrite array_seg_reroot_lemma with (gfs := [StructField _data]) (lo := ddlen + 1) (hi := 64);
  [ | omega | omega | reflexivity | omega | reflexivity 
  | reflexivity | | ].
    2: rewrite map_app, Zlength_app, !Zlength_map; reflexivity.
    2: rewrite map_list_repeat, Zlength_correct, length_list_repeat;
       rewrite Z2Nat.id by omega; reflexivity.
  rewrite map_list_repeat.
  rewrite map_app.
  change 64 with CBLOCKz.
  entailer!.
}
pose (ddzw := Zlist_to_intlist (map Int.unsigned ddz)).
assert (H0': length ddz = CBLOCK). {
  subst ddz ddlen. clear - Hddlen H3.
  repeat rewrite app_length. simpl.
   apply Nat2Z.inj.   (* Maybe build this into Omega or MyOmega? *)
   MyOmega.
}
assert (H1': length ddzw = LBLOCK). {
  unfold ddzw.
  apply length_Zlist_to_intlist. rewrite map_length. apply H0'.
}
assert (HU: map Int.unsigned ddz = intlist_to_Zlist ddzw). {
  unfold ddzw; rewrite Zlist_to_intlist_to_Zlist; auto.
  rewrite map_length, H0'; exists LBLOCK; reflexivity.
  unfold ddz; repeat rewrite map_app; repeat rewrite Forall_app; repeat split; auto.
  apply Forall_isbyteZ_unsigned_repr; auto.
  constructor. compute. clear; split; congruence.
  constructor.
  rewrite map_list_repeat.
  apply Forall_list_repeat.
  rewrite Int.unsigned_zero. split; clear; omega.
}
clear H0'.
clearbody ddzw.
forward n_old.  (* n=0; *)
erewrite field_at_data_at with (gfs := [StructField _data]) by reflexivity.
clear n_old H2.
rewrite semax_seq_skip.
forward_call' (* sha256_block_data_order (c,p); *)
  (hashed, ddzw, c,
    field_address t_struct_SHA256state_st [StructField _data] c,
    Tsh, kv).
{
  repeat rewrite sepcon_assoc; apply sepcon_derives; [ | cancel].
  unfold data_block.
  simpl. apply andp_right.
  apply prop_right.
  apply isbyte_intlist_to_Zlist.
  normalize.
  apply derives_refl'.
  rewrite Zlength_correct.
  rewrite length_intlist_to_Zlist.
  rewrite H1'.
  rewrite <- HU.
  unfold tarray.
  rewrite map_map with (g := Int.repr).
  replace (fun x => Int.repr (Int.unsigned x)) with (@id int) by 
    (extensionality xx; rewrite Int.repr_unsigned; auto).
  rewrite map_id.
  reflexivity.
}
 split; auto.
 rewrite Zlength_length. assumption. change LBLOCKz with 16%Z; computable.
 simpl map.
 unfold invariant_after_if1.
 apply exp_right with (hashed ++ ddzw).
 set (pad := (CBLOCKz - (ddlen+1))%Z) in *.
 apply exp_right with (@nil Z).
 apply exp_right with pad.
 entailer.
assert (0 <= pad < 8)%Z by MyOmega.
assert (length (list_repeat (Z.to_nat pad) 0) < 8)%nat by MyOmega.
unfold_data_at 1%nat.
entailer!.
* clear; Omega1.
* rewrite initial_world.Zlength_app.
   apply Zlength_length in H1'; [ | auto]. rewrite H1'.
 clear - H4; destruct H4 as [n ?]; exists (n+1). 
  rewrite Z.mul_add_distr_r; omega.
* rewrite <- app_nil_end.
  rewrite intlist_to_Zlist_app.
  f_equal.
  rewrite <- HU.
  unfold ddz.
  repeat rewrite map_app.
  repeat rewrite app_ass.
 f_equal.
 clear - DDbytes; induction dd; simpl.
  auto.
 inv DDbytes; f_equal; auto.
 apply Int.unsigned_repr; unfold isbyteZ in H1; repable_signed.
 rewrite map_list_repeat.
 simpl.  f_equal.
*
 unfold data_block.
 simpl. apply andp_left2.
 rewrite field_at_data_at by reflexivity.
 normalize.
 replace (Zlength (intlist_to_Zlist ddzw)) with 64%Z.
 apply data_at_data_at_.
 rewrite Zlength_correct; rewrite length_intlist_to_Zlist.
 rewrite H1'; reflexivity.
Qed.

Lemma nth_intlist_to_Zlist_eq:
 forall d (n i j k: nat) al, (i < n)%nat -> (i < j*4)%nat -> (i < k*4)%nat -> 
    nth i (intlist_to_Zlist (firstn j al)) d = nth i (intlist_to_Zlist (firstn k al)) d.
Proof.
 induction n; destruct i,al,j,k; simpl; intros; auto; try omega.
 destruct i; auto. destruct i; auto. destruct i; auto.
 apply IHn; omega.
Qed.

Definition final_loop :=
 Sfor (Sset _xn (Econst_int (Int.repr 0) tint))
        (Ebinop Olt (Etempvar _xn tuint)
          (Ebinop Odiv (Econst_int (Int.repr 32) tint)
            (Econst_int (Int.repr 4) tint) tint) tint)
        (Ssequence
          (Sset _ll
                             (Ederef
                                (Ebinop Oadd
                                   (Efield
                                      (Ederef
                                         (Etempvar _c
                                            (tptr t_struct_SHA256state_st))
                                         t_struct_SHA256state_st) _h
                                      (tarray tuint 8)) (Etempvar _xn tuint)
                                   (tptr tuint)) tuint))
                          (Ssequence
                             (Scall None
                                (Evar ___builtin_write32_reversed
                                   (Tfunction
                                      (Tcons (tptr tuint) (Tcons tuint Tnil))
                                      tvoid cc_default))
                                [Ecast (Etempvar _md (tptr tuchar))
                                   (tptr tuint); Etempvar _ll tuint])
                             (Sset _md
                                (Ebinop Oadd (Etempvar _md (tptr tuchar))
                                   (Econst_int (Int.repr 4) tint)
                                   (tptr tuchar)))))
      (Sset _xn
         (Ebinop Oadd (Etempvar _xn tuint)
          (Econst_int (Int.repr 1) tint) tuint)).

Lemma nth_intlist_to_Zlist_first_hack:
  forall  j i al, 
    (i*4 <= j)%nat ->
    nth (j-i*4) (intlist_to_Zlist [nth i al Int.zero]) 0 =
    nth j (intlist_to_Zlist (firstn (S i) al)) 0.
Proof.
intros.
 assert (j= (j-i*4) + i*4)%nat by omega.
 rewrite H0 at 2.
 forget (j-i*4)%nat as n. clear.
 revert n al; induction i; intros.
 change (0*4)%nat with O.  
 rewrite NPeano.Nat.add_0_r.
 destruct al; try reflexivity.
 simpl firstn.
 rewrite (nth_overflow nil) by (simpl; auto).
 simpl intlist_to_Zlist.
 repeat (destruct n; try reflexivity).
 replace (n + S i * 4)%nat with (n+4 + i*4)%nat
  by (simpl; omega).
 destruct al as [ | a al].
 rewrite (nth_overflow nil) by (simpl; clear; omega).
 simpl firstn. simpl intlist_to_Zlist.
 rewrite (nth_overflow nil) by (simpl; clear; omega).
 repeat (destruct n; try reflexivity).
 simpl nth at 2.
 replace (firstn (S (S i)) (a :: al)) with (a :: firstn (S i) al).
 unfold intlist_to_Zlist at 2; fold intlist_to_Zlist.
 rewrite IHi. clear IHi.
 replace (n + 4 + i*4)%nat with (S (S (S (S (n + i*4)))))%nat by omega.
 reflexivity.
 clear.
 forget (S i) as j.
 revert al; induction j; simpl; intros; auto.
Qed.

Lemma final_part4:
 forall (Espec: OracleKind) md c shmd hashedmsg kv,
 length hashedmsg = 8%nat ->
 writable_share shmd ->
semax
  (initialized _cNl (initialized _cNh Delta_final_if1))
  (PROP  ()
   LOCAL  (temp _md md; temp _c c)
   SEP 
   (`(data_at Tsh t_struct_SHA256state_st
       (map Vint hashedmsg,  (Vundef, (Vundef, (list_repeat 64%nat (Vint Int.zero), Vint Int.zero))))
      c);
    `(K_vector kv);
    `(memory_block shmd (Int.repr 32) md)))
  (Ssequence final_loop (Sreturn None))
  (function_body_ret_assert tvoid
     (PROP  ()
      LOCAL ()
      SEP  (`(K_vector kv);
      `(data_at_ Tsh t_struct_SHA256state_st c);
      `(data_block shmd (intlist_to_Zlist hashedmsg) md)))).
Proof.
intros.
unfold final_loop; abbreviate_semax.
rewrite memory_block_isptr.
normalize. rename H1 into Hmd.

forward_for_simple_bound 8 
  (EX i:Z, 
   PROP  ()
   LOCAL  (temp _md (offset_val (Int.repr (i * 4)) md);
                temp _c c)
   SEP 
   (`(data_at Tsh t_struct_SHA256state_st
       (map Vint hashedmsg, (Vundef, (Vundef, (list_repeat 64%nat (Vint Int.zero), Vint Int.zero))))
      c);
    `(K_vector kv);
    `(data_at shmd (tarray tuchar 32) (map Vint (map Int.repr (intlist_to_Zlist (firstn (Z.to_nat i) hashedmsg)))) md)
     )).
*
 entailer!.
  change 32%Z with (sizeof (tarray tuchar 32)).
  rewrite align_1_memory_block_data_at_ by (eauto; change Int.modulus with 4294967296; simpl; omega).
  auto.
*
  drop_LOCAL 1%nat. (* shouldn't need this *)
  assert (H1': (Z.to_nat i < 8)%nat) by Omega1.
  forward. (* ll=(c)->h[xn]; *)
  {
    entailer!.
    unfold Znth. rewrite if_false by omega.
    rewrite (nth_map' Vint _ Int.zero).
    apply I. omega.
  }
  pose (w := nth (Z.to_nat i) hashedmsg Int.zero).
  pose (bytes := map force_int (map Vint (map Int.repr (intlist_to_Zlist [w])))).

  (* split (data_at shmd (tarray tuchar 32)
          (map Vint (map Int.repr (intlist_to_Zlist (firstn i hashedmsg)))) md)
     into 3 segment *)
      replace (data_at shmd (tarray tuchar 32)
        (map Vint (map Int.repr (intlist_to_Zlist (firstn (Z.to_nat i) hashedmsg)))) md) with
        (data_at shmd (tarray tuchar 32)
          (map Vint (map Int.repr (intlist_to_Zlist (firstn (Z.to_nat i) hashedmsg))) ++
             list_repeat 4 Vundef ++ []) md).
      Focus 2. {
        rewrite app_nil_r.
        apply eq_sym.
        apply equal_f.
        apply data_equal_list_repeat_default.
      } Unfocus.
      rewrite data_at_field_at with (t := tarray tuchar 32).
      erewrite array_seg_reroot_lemma
        with (gfs := []) (lo := (i * 4)%Z) (hi := (i * 4 + 4)%Z);
        [| omega | omega | reflexivity | omega | reflexivity | reflexivity | | ].
      2:  rewrite Zlength_correct,
             !map_length, length_intlist_to_Zlist,
             firstn_length, min_l; Omega1.
      2: rewrite Zlength_correct, length_list_repeat; Omega1.  
      replace (i * 4 + 4 - i * 4) with 4 by omega.
      normalize.
  forward_call' (* builtin_write32_reversed *)
     (field_address0 (tarray tuchar 32) [ArraySubsc (i*4)] md, shmd, bytes).
 +
   entailer!.
   unfold bytes, Basics.compose.
   rewrite H2. simpl force_val. f_equal. f_equal.
  unfold Znth in H2.
  rewrite if_false in H2 by omega.
  rewrite (nth_map' _ _ Int.zero) in H2 by omega.
  inv H2.
       change (map force_int (map Vint (map Int.repr (intlist_to_Zlist [w])))) with
           (firstn (Z.to_nat WORD) (skipn (0%nat * Z.to_nat WORD)
             (map Int.repr (intlist_to_Zlist [w])))).
   apply nth_big_endian_integer; reflexivity.
    unfold field_address0; rewrite if_true; auto.
      erewrite nested_field_offset2_Tarray by reflexivity.
      change (nested_field_offset2 (tarray tuchar 32) []) with 0.
      normalize.
      destruct md; try contradiction; reflexivity.
      unfold field_address0 in H3.
      if_tac in H3; auto; destruct H3; contradiction.
 +
     split; auto.
      rewrite Zlength_correct; subst bytes.
      simpl.
      omega.
 +
  forward md_old. (* md += 4; *)
  {
    entailer!.
    f_equal. f_equal. omega.
    replace (data_at shmd (tarray tuchar 32)
        (map Vint (map Int.repr (intlist_to_Zlist (firstn (Z.to_nat (i+1)) hashedmsg)))) md) with
        (data_at shmd (tarray tuchar 32)
        (map Vint (map Int.repr (intlist_to_Zlist (firstn (Z.to_nat i) hashedmsg) ++ intlist_to_Zlist [w] ++ []))) md).
      Focus 2. {
        assert (forall i0 : Z, 0 <= i0 < 32 ->
          Znth i0 (map Vint (map Int.repr
           (intlist_to_Zlist (firstn (Z.to_nat i) hashedmsg) ++ intlist_to_Zlist [w]))) (default_val tuchar) =
          Znth i0 (map Vint (map Int.repr (intlist_to_Zlist (firstn (Z.to_nat (i+1)) hashedmsg))))
           (default_val tuchar)).
        Focus 1. {
          intros.
          f_equal.
          f_equal.
          f_equal.
          rewrite Z2Nat.inj_add by omega. change (Z.to_nat 1) with 1%nat.  
          rewrite <- firstn_app.
          rewrite intlist_to_Zlist_app.
          f_equal; f_equal.
          apply firstn_1_skipn.
          omega.
        } Unfocus.
        apply pred_ext;
        apply stronger_array_ext;
           intros; rewrite H2 by auto; apply stronger_refl.      
      } Unfocus.
      rewrite data_at_field_at with (t := tarray tuchar 32).
      rewrite !map_app.
      erewrite array_seg_reroot_lemma
        with (gfs := []) (lo := (i * 4)%Z) (hi := (i * 4 + 4)%Z);
        [| omega | omega | reflexivity | omega | reflexivity | reflexivity | | ].
      Focus 2. {
        rewrite !Zlength_map, Zlength_intlist_to_Zlist,
               Zlength_correct, firstn_length.
        rewrite min_l by omega. rewrite Z.mul_comm.
        rewrite Z2Nat.id by omega. auto.
      } Unfocus.
      Focus 2. {
        rewrite !Zlength_map, Zlength_intlist_to_Zlist.
        change (WORD * Zlength [w])%Z with 4.
        omega.
      } Unfocus.
      replace (i * 4 + 4 - i * 4) with 4 by omega.
      entailer!.
 }
*
  rewrite (firstn_same _ 8) by omega.
  change 64%nat with CBLOCK.
  forward. (* return; *)
  unfold data_block.
  rewrite prop_true_andp with (P:= Forall isbyteZ (intlist_to_Zlist hashedmsg))
    by apply isbyte_intlist_to_Zlist.
  entailer.
    rewrite Zlength_intlist_to_Zlist, Zlength_correct, H.
  cancel.
Qed.
