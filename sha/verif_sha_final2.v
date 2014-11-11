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

Definition invariant_after_if1 hashed (dd: list Z) c md shmd  hi lo kv:= 
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
    temp _p (offset_val (Int.repr 40) (force_ptr c));
    temp _md md; temp _c c;
    var _K256 (tarray tuint CBLOCKz) kv)
   SEP  (`(data_at Tsh t_struct_SHA256state_st 
           (map Vint (hash_blocks init_registers hashed'),
            (Vint lo,
             (Vint hi,
              (map Vint (map Int.repr dd'),
               Vundef))))
           c);
         `(K_vector kv);
         `(memory_block shmd (Int.repr 32) md))).

Lemma ifbody_final_if1:
  forall (Espec : OracleKind) (hashed : list int) (md c : val) (shmd : share)
  (hi lo : int) (dd : list Z) (kv: val)
 (H4: (LBLOCKz  | Zlength hashed))
 (H7: ((Zlength hashed * 4 + Zlength dd)*8 = hilo hi lo)%Z)
 (H3: Zlength dd < CBLOCKz)
 (DDbytes: Forall isbyteZ dd),
  semax Delta_final_if1
  (PROP  ()
   LOCAL 
   (`(typed_true tint)
      (eval_expr
         (Ebinop Ogt (Etempvar _n tuint)
            (Ebinop Osub
               (Ebinop Omul (Econst_int (Int.repr 16) tint)
                  (Econst_int (Int.repr 4) tint) tint)
               (Econst_int (Int.repr 8) tint) tint) tint));
    temp _n (Vint (Int.repr (Zlength dd + 1)));
    temp _p (offset_val (Int.repr (nested_field_offset2 t_struct_SHA256state_st [StructField _data])) c);
    temp _md md; temp _c c;
    var _K256 (tarray tuint CBLOCKz) kv)
   SEP 
   (`(data_at Tsh t_struct_SHA256state_st
       (map Vint (hash_blocks init_registers hashed),
        (Vint lo, 
         (Vint hi,
          (map Vint (map Int.repr dd) ++ [Vint (Int.repr 128)],
           Vint (Int.repr (Zlength dd))))))
      c);
    `(K_vector kv);
    `(memory_block shmd (Int.repr 32) md)))
  Body_final_if1
  (normal_ret_assert (invariant_after_if1 hashed dd c md shmd hi lo kv)).
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
unfold_field_at 1%nat.
rewrite split2_array_at with (mid := ddlen + 1) by omega.
normalize.
erewrite array_at_data_at with (lo := ddlen + 1); 
  [| omega | omega | | reflexivity | reflexivity |reflexivity]; [| omega].
normalize.
forward_call (* memset (p+n,0,SHA_CBLOCK-n); *)
   ((Tsh,
     offset_val (Int.repr
       (nested_field_offset2 t_struct_SHA256state_st
          [ArraySubsc (ddlen + 1); StructField _data])) c,
     (CBLOCKz - (ddlen + 1)))%Z,
     Int.zero).
  {

  remember (data_at Tsh (Tarray tuchar (64 - (ddlen + 1)) noattr)
       (skipn (Z.to_nat (ddlen + 1 - 0))
          (map Vint (map Int.repr dd) ++ [Vint (Int.repr 128)]))
       (offset_val
          (Int.repr
             (nested_field_offset2 t_struct_SHA256state_st
                [ArraySubsc (ddlen + 1); StructField _data])) c))
     as A.
  change 64 with CBLOCKz.
  entailer!.  (* It works on Saturday without the previouse line but not work *)
  + change CBLOCKz with 64%Z; assert (Int.max_unsigned > 64%Z) by computable; omega.
  + f_equal.
    f_equal.
    erewrite nested_field_offset2_Tarray by reflexivity.
    change (sizeof tuchar) with 1.
    rewrite Z.mul_1_l.
    reflexivity.
  + change CBLOCKz with 64%Z.
    normalize.
     repeat rewrite <- sepcon_assoc;
      pull_left (data_at Tsh (Tarray tuchar (64 - (ddlen + 1)) noattr)
     (skipn (Z.to_nat (ddlen + 1 - 0))
        (map Vint (map Int.repr dd) ++ [Vint (Int.repr 128)]))
     (offset_val
        (Int.repr
           (nested_field_offset2 t_struct_SHA256state_st
              [ArraySubsc (ddlen + 1); StructField _data])) c)).
     repeat rewrite sepcon_assoc; apply sepcon_derives; [ | cancel].
    eapply derives_trans; [apply data_at_data_at_; reflexivity |].
    assert (sizeof (Tarray tuchar (64 - (ddlen + 1)) noattr) = 64 - (ddlen + 1)).
    Focus 1. {
Opaque Z.sub Z.mul.
      simpl.
Transparent Z.sub Z.mul.
      rewrite Z.max_r by omega.
      rewrite Z.mul_1_l.
      reflexivity.
    } Unfocus.
    assert (Int.modulus = 4294967296) by reflexivity.
    rewrite data_at__memory_block; [| reflexivity | reflexivity | omega].
    apply andp_left2.
    apply derives_refl'.
    f_equal.
    f_equal.
    auto.
}
after_call.
gather_SEP 1%Z 0%Z.
pose (ddz := ((map Int.repr dd ++ [Int.repr 128]) ++ list_repeat (Z.to_nat (CBLOCKz-(ddlen+1))) Int.zero)).
replace_SEP 0%Z (`(array_at Tsh t_struct_SHA256state_st [StructField _data] 0 64 (map Vint ddz) c)).
{
  unfold ddz.
  rewrite map_app.
  rewrite split2_array_at0 with (lo := 0) (mid := ddlen + 1) (hi := 64); [| omega |
    rewrite map_app, Zlength_app;
    rewrite !Zlength_map;
    change (Zlength [Int.repr 128]) with 1;
    unfold ddlen;
    omega].
  normalize.
  erewrite array_at_data_at with (lo :=  ddlen + 1);
    [| omega | omega | | reflexivity | reflexivity | reflexivity]; [| omega].
  normalize.
Opaque Z.sub Z.mul.
  entailer!.
Transparent Z.sub Z.mul.
  rewrite map_list_repeat.
  rewrite map_app.
  cancel.
}
pose (ddzw := Zlist_to_intlist (map Int.unsigned ddz)).
assert (H0': length ddz = CBLOCK). {
  unfold ddz; repeat rewrite app_length.
  rewrite length_list_repeat by omega.
  rewrite Z2Nat.inj_sub by omega.
  rewrite Z2Nat.inj_add by omega.
  change (Z.to_nat CBLOCKz) with CBLOCK.
  unfold ddlen; rewrite Zlength_correct. 
  rewrite (Nat2Z.id).
  rewrite map_length; simpl length; change (Z.to_nat 1) with 1%nat.
  clear - Hddlen. unfold ddlen in Hddlen.
  destruct Hddlen. 
  rewrite Zlength_correct in H0.
  change 64 with (Z.of_nat CBLOCK) in H0.
  apply Nat2Z.inj_lt in H0. omega.
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
forward.  (* n=0; *)
forward_call (* sha256_block_data_order (c,p); *)
  (hashed, ddzw, c, offset_val (Int.repr (nested_field_offset2 t_struct_SHA256state_st
              [ArraySubsc 0; StructField _data])) c, Tsh, kv).
{
  rewrite Zlength_correct, H1'.
  entailer!.
  repeat rewrite sepcon_assoc; apply sepcon_derives; [ | cancel].
  unfold data_block.
  simpl. apply andp_right.
  apply prop_right.
  apply isbyte_intlist_to_Zlist.
  apply derives_refl'; f_equal.
  erewrite array_at_data_at; [| omega | omega | | reflexivity | reflexivity| reflexivity]; [| omega].
  normalize.
  rewrite Z.sub_0_r.
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
after_call.
unfold invariant_after_if1.
 apply exp_right with (hashed ++ ddzw).
set (pad := (CBLOCKz - (ddlen+1))%Z) in *.
 apply exp_right with (@nil Z).
 apply exp_right with pad.
entailer.
normalize in H8.
apply ltu_repr in H8; [ | split; computable 
  | change CBLOCKz with 64 in Hddlen; Omega1].
simpl in H8.
assert (0 <= pad < 8)%Z.
  unfold pad.
  change CBLOCKz with 64.
  omega.
assert (length (list_repeat (Z.to_nat pad) 0) < 8)%nat.
  rewrite length_list_repeat.
  apply Nat2Z.inj_lt.
  rewrite Z2Nat.id by omega.
  Omega1.
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
 unfold_field_at 1%nat.
 erewrite array_at_data_at; [| omega | omega | | reflexivity | reflexivity | reflexivity].
 normalize.
 replace (Zlength (intlist_to_Zlist ddzw)) with 64%Z.
 apply data_at_data_at_.
 reflexivity.
 rewrite Zlength_correct; rewrite length_intlist_to_Zlist.
 rewrite H1'; reflexivity.
 omega.
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
 (Ssequence (Sset _xn (Econst_int (Int.repr 0) tint))
                 (Sloop
                    (Ssequence
                       (Sifthenelse
                          (Ebinop Olt (Etempvar _xn tuint)
                             (Ebinop Odiv (Econst_int (Int.repr 32) tint)
                                (Econst_int (Int.repr 4) tint) tint) tint)
                          Sskip Sbreak)
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
                                   (tptr tuchar))))))
                    (Sset _xn
                       (Ebinop Oadd (Etempvar _xn tuint)
                          (Econst_int (Int.repr 1) tint) tuint)))).

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

Definition part4_inv  c shmd hashedmsg md kv delta (i: nat) :=
   (PROP  ((i <= 8)%nat)
   LOCAL  (temp _xn (Vint (Int.repr (Z.of_nat i - delta)));
                temp _md (offset_val (Int.repr (Z.of_nat i * 4)) md);
                temp _c c)
   SEP 
   (`(data_at Tsh t_struct_SHA256state_st
       (map Vint hashedmsg, (Vundef, (Vundef, (list_repeat 64%nat (Vint Int.zero), Vint Int.zero))))
      c);
    `(K_vector kv);
    `(data_at shmd (tarray tuchar 32) (map Vint (map Int.repr (intlist_to_Zlist (firstn i hashedmsg)))) md))).

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
forward.  (* xn=0; *)
forward_for 
   (EX i:_, part4_inv c shmd hashedmsg md kv 0 i) 
   (EX i:_, part4_inv c shmd hashedmsg md kv 1 i) 
   (part4_inv c shmd hashedmsg md kv 0 8).
{
  apply exp_right with 0%nat. unfold part4_inv; rewrite Z.sub_0_r.
  entailer!.
  change 32%Z with (sizeof (tarray tuchar 32)).
  rewrite align_1_memory_block_data_at_ by (eauto; change Int.modulus with 4294967296; simpl; omega).
  auto.
}
{
  quick_typecheck.
}
{
  unfold part4_inv.  repeat rewrite Z.sub_0_r.
  rewrite (firstn_same _ 8) by omega.
  entailer.
  rewrite <- H2 in *.
  simpl in H5.
  simpl_compare.
  change (Int.divs (Int.repr 32) (Int.repr 4)) with (Int.repr 8) in H5.
  apply ltu_repr_false in H5; try repable_signed; try omega.
  assert (i=8)%nat by omega.
  subst i. change (Z.of_nat 8) with 8%Z.
  entailer!.
  rewrite (firstn_same _ 8) by omega. auto.
}
  unfold part4_inv.
  rewrite insert_local.
  match goal with |- semax _ (PROPx _ (LOCALx (_:: ?Q) ?R)) _ _ =>
    apply semax_pre with (PROP ((i<8)%nat) (LOCALx Q R))
  end.
  Focus 1. {
    rewrite Z.sub_0_r.
    entailer!.
    change (Int.divs (Int.repr 32) (Int.repr 4)) with (Int.repr 8) in H2.
    apply ltu_repr in H2; try repable_signed; try omega.
  } Unfocus.
  normalize.
  rewrite Z.sub_0_r.
  forward. (* ll=(c)->h[xn]; *)
  {
    entailer!.
    unfold Znth. rewrite if_false by omega.
    rewrite Nat2Z.id.
    rewrite (nth_map' Vint _ Int.zero).
    apply I.
    omega.
  }
  pose (w := nth i hashedmsg Int.zero).
  pose (bytes := map force_int (map Vint (map Int.repr (intlist_to_Zlist [w])))).

  (* split (data_at shmd (tarray tuchar 32)
          (map Vint (map Int.repr (intlist_to_Zlist (firstn i hashedmsg)))) md)
     into 3 segment *)
      replace (data_at shmd (tarray tuchar 32)
        (map Vint (map Int.repr (intlist_to_Zlist (firstn i hashedmsg)))) md) with
        (data_at shmd (tarray tuchar 32)
          (map Vint (map Int.repr (intlist_to_Zlist (firstn i hashedmsg))) ++
             list_repeat 4 Vundef ++ []) md).
      Focus 2. {
        assert (forall i0 : Z, 0 <= i0 < 32 ->
            (Znth i0 (map Vint (map Int.repr (intlist_to_Zlist (firstn i hashedmsg)))) Vundef) =
            (Znth i0 (map Vint (map Int.repr (intlist_to_Zlist (firstn i hashedmsg))) ++
              list_repeat 4 Vundef) Vundef)).
        Focus 1. {
          intros.
          unfold Znth; rewrite !if_false by omega.
          destruct (lt_dec (Z.to_nat i0) (4 * i)%nat).
          + rewrite app_nth1; [reflexivity |].
            rewrite !map_length.
            rewrite length_intlist_to_Zlist.
            rewrite firstn_length.
            rewrite min_l by omega.
            exact l.
          + pattern (map Vint (map Int.repr (intlist_to_Zlist (firstn i hashedmsg)))) at 1.
            replace (map Vint (map Int.repr (intlist_to_Zlist (firstn i hashedmsg)))) with
              (map Vint (map Int.repr (intlist_to_Zlist (firstn i hashedmsg))) ++ [])
              by (rewrite app_nil_r; reflexivity).
            assert (Z.to_nat i0 >=
              length (map Vint (map Int.repr (intlist_to_Zlist (firstn i hashedmsg)))))%nat.
            Focus 1. {
              rewrite !map_length.
              rewrite length_intlist_to_Zlist.
              rewrite firstn_length.
              rewrite min_l by omega.
              omega.
            } Unfocus.
            rewrite !app_nth2 by auto.
            forget (Z.to_nat i0 - length
              (map Vint (map Int.repr (intlist_to_Zlist (firstn i hashedmsg)))))%nat as nn.
            destruct nn; try reflexivity.
            destruct nn; try reflexivity.
            destruct nn; try reflexivity.
            destruct nn; try reflexivity.
            destruct nn; try reflexivity.
          } Unfocus.
        apply pred_ext; 
         (apply stronger_array_ext; [reflexivity |];
          intros; rewrite H2 by auto; apply stronger_refl).
      } Unfocus.
      unfold_data_at 2%nat.
      change (map Vint (map Int.repr (intlist_to_Zlist (firstn i hashedmsg))) ++
        [Vundef; Vundef; Vundef; Vundef]) with
        (map Vint (map Int.repr (intlist_to_Zlist (firstn i hashedmsg))) ++
      [Vundef; Vundef; Vundef; Vundef] ++ []).
      rewrite split3seg_array_at with (ml := (Z.of_nat i * 4)%Z) (mr := (Z.of_nat i * 4 + 4)%Z);
        [| omega | omega | omega | | rewrite Zlength_correct; simpl; omega].
      Focus 2. {
        rewrite Zlength_correct.
        rewrite !map_length.
        rewrite length_intlist_to_Zlist.
        rewrite firstn_length.
        rewrite min_l by omega.
        rewrite Nat2Z.inj_mul.
        change (Z.of_nat 4) with 4; omega.
      } Unfocus.
      simpl.
      erewrite array_at_data_at with (lo := (Z.of_nat i * 4)%Z) (hi := (Z.of_nat i * 4 + 4)%Z);
        [| omega | omega | | reflexivity | reflexivity| reflexivity]; [| omega].
      normalize.

  forward_call (* builtin_write32_reversed *)
     (offset_val
        (Int.repr
           (nested_field_offset2 (tarray tuchar 32)
              [ArraySubsc (Z.of_nat i * 4)])) md, shmd, bytes).
  {
    entailer!.
    + destruct md; inversion Hmd.
      simpl.
      erewrite nested_field_offset2_Tarray by reflexivity.
      change (nested_field_offset2 (tarray tuchar 32) []) with 0.
      change (sizeof tuchar) with 1.
      rewrite Z.mul_1_l.
      rewrite Z.add_0_l.
      reflexivity.
    + unfold Znth in H6.
      rewrite if_false in H6 by omega.
      rewrite Nat2Z.id in H6.
      rewrite (nth_map' _ _ Int.zero) in H6 by omega.
      inv H6.
      symmetry; unfold bytes, Basics.compose.
       change (map force_int (map Vint (map Int.repr (intlist_to_Zlist [w])))) with
           (firstn (Z.to_nat WORD) (skipn (0%nat * Z.to_nat WORD)
             (map Int.repr (intlist_to_Zlist [w])))).
      apply nth_big_endian_integer; reflexivity.
    + change 4 with (sizeof (tarray tuchar 4)).
      rewrite memory_block_data_at_;
        [| reflexivity | reflexivity | | change Int.modulus with 4294967296; simpl; omega].
      Focus 2. {
        unfold align_compatible; simpl.
        destruct md; simpl; auto; apply Z.divide_1_l.
      } Unfocus.
      simpl sizeof.
      replace (Z.of_nat i * 4 + 4 - Z.of_nat i * 4) with 4 by omega.
      pull_left (data_at shmd (Tarray tuchar 4 noattr) [Vundef; Vundef; Vundef; Vundef]
        (offset_val (Int.repr
           (nested_field_offset2 (tarray tuchar 32)
              [ArraySubsc (Z.of_nat i * 4)])) md)).
      repeat rewrite sepcon_assoc; apply sepcon_derives; [ | cancel_frame].
      apply data_at_data_at_; auto.
  } 
  after_call.
  normalize.
  forward. (* md += 4; *)
  {
    unfold part4_inv. 
    unfold loop1_ret_assert;  simpl update_tycon.
    entailer!.
    apply exp_right with (S i). rewrite inj_S.
    entailer!.
    + f_equal; f_equal; omega.
    + destruct md; try (contradiction Hmd); simpl; f_equal.
      f_equal. f_equal.
      omega.
    + replace (data_at shmd (tarray tuchar 32)
        (map Vint (map Int.repr (intlist_to_Zlist (firstn (S i) hashedmsg)))) md) with
        (data_at shmd (tarray tuchar 32)
        (map Vint (map Int.repr (intlist_to_Zlist (firstn i hashedmsg) ++ intlist_to_Zlist [w]))) md).
      Focus 2. {
        assert (forall i0 : Z, 0 <= i0 < 32 ->
          Znth i0 (map Vint (map Int.repr
           (intlist_to_Zlist (firstn i hashedmsg) ++ intlist_to_Zlist [w]))) (default_val tuchar) =
          Znth i0 (map Vint (map Int.repr (intlist_to_Zlist (firstn (S i) hashedmsg))))
           (default_val tuchar)).
        Focus 1. {
          intros.
          f_equal.
          f_equal.
          f_equal.
          replace (S i) with (i + 1)%nat by omega.
          rewrite <- firstn_app.
          rewrite intlist_to_Zlist_app.
          f_equal; f_equal.
          apply firstn_1_skipn.
          omega.
        } Unfocus.
        apply pred_ext;
          (apply stronger_array_ext; [reflexivity |];
           intros; rewrite H6 by auto; apply stronger_refl).
      } Unfocus.
      unfold_data_at 2%nat.
      rewrite !map_app.
      match goal with
      | |- appcontext [?A ++ ?B] => change (A ++ B) with (A ++ B ++ [])
      end.
      rewrite split3seg_array_at with (ml := (Z.of_nat i * 4)%Z) (mr := (Z.of_nat i * 4 + 4)%Z);
        [| omega | omega | omega | | rewrite Zlength_correct; simpl; omega].
      Focus 2. {
        rewrite !common_lemmas.Zlength_map.
        rewrite Zlength_intlist_to_Zlist.
        rewrite Zlength_correct, firstn_length.
        rewrite min_l by omega.
        change WORD with 4; rewrite Z.mul_comm.
        omega.
      } Unfocus.
      simpl;
      erewrite array_at_data_at with (lo := (Z.of_nat i * 4)%Z) (hi := (Z.of_nat i * 4 + 4)%Z);
        [| omega | omega | | reflexivity | reflexivity | reflexivity]; [| omega].
      replace (Z.of_nat i * 4 + 4 - Z.of_nat i * 4) with 4 by omega.
      entailer!.
}
 (* for-loop increment *)
{
  unfold part4_inv. apply extract_exists_pre; intro i.
  normalize.
  forward. (* xn++; *)
  apply exp_right with i.
  unfold part4_inv.
  rewrite Z.sub_0_r.
  entailer.
  apply prop_right. f_equal. omega.
}
  (* after the loop *)
  unfold part4_inv. 
   rewrite (firstn_same _ 8) by omega.
  forward. (* return; *)
  unfold data_at_.
  unfold data_block.
  rewrite prop_true_andp with (P:= Forall isbyteZ (intlist_to_Zlist hashedmsg))
    by apply isbyte_intlist_to_Zlist.
  entailer.
  replace (Zlength (intlist_to_Zlist hashedmsg)) with 32%Z.
  Focus 2. {
    rewrite Zlength_intlist_to_Zlist.
    rewrite Zlength_correct.
    rewrite H.
    reflexivity.
  } Unfocus.
  cancel.
  apply data_at_data_at_.
  reflexivity.
Qed.
