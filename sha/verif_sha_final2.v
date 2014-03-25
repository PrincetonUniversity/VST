Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Local Open Scope logic.

Definition Delta_final_if1 : tycontext :=
 initialized _n  (initialized _p
     (func_tycontext f_SHA256_Final Vprog Gtot)).

Definition Body_final_if1 := 
  (Ssequence
              (Scall None
                (Evar _memset (Tfunction
                                (Tcons (tptr tvoid)
                                  (Tcons tint (Tcons tuint Tnil)))
                                (tptr tvoid)))
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
                                                       Tnil)) tvoid))
                  ((Etempvar _c (tptr t_struct_SHA256state_st)) ::
                   (Etempvar _p (tptr tuchar)) :: nil)))).

Definition invariant_after_if1 hashed (dd: list Z) c md shmd  hi lo:= 
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
   (`(eq (Vint (Int.repr (Zlength dd')))) (eval_id _n);
   `eq (eval_id _p)
     (`(offset_val (Int.repr 40)) (`force_ptr (eval_id _c)));
   `(eq md) (eval_id _md); `(eq c) (eval_id _c))
   SEP  (`(array_at tuint Tsh (ZnthV tuint (map Vint (hash_blocks init_registers hashed'))) 0 8 c);
   `(field_at Tsh t_struct_SHA256state_st _Nl (Vint lo) c);
   `(field_at Tsh t_struct_SHA256state_st _Nh (Vint hi) c);
   `(array_at tuchar Tsh (ZnthV tuchar (map Vint (map Int.repr dd'))) 0 64 
                          (offset_val (Int.repr 40) c));
   `(field_at_ Tsh t_struct_SHA256state_st _num c);
     K_vector;
   `(memory_block shmd (Int.repr 32) md))).

Lemma ifbody_final_if1:
  forall (Espec : OracleKind) (hashed : list int) (md c : val) (shmd : share)
  (hi lo : int) (dd : list Z)
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
   `(eq (Vint (Int.repr (Zlength dd + 1)))) (eval_id _n);
   `eq (eval_id _p) (`(offset_val (Int.repr 40)) (`force_ptr (eval_id _c)));
   `(eq md) (eval_id _md); `(eq c) (eval_id _c))
   SEP 
   (`(array_at tuint Tsh
        (ZnthV tuint (map Vint (hash_blocks init_registers hashed))) 0 8 c);
   `(field_at Tsh t_struct_SHA256state_st _Nl (Vint lo) c);
   `(field_at Tsh t_struct_SHA256state_st _Nh (Vint hi) c);
   `(array_at tuchar Tsh
       (ZnthV tuchar (map Vint (map Int.repr dd) ++ [Vint (Int.repr 128)])) 0 64
       (offset_val (Int.repr 40) c));
   `(field_at Tsh t_struct_SHA256state_st _num (Vint (Int.repr (Zlength dd))) c);
   K_vector; `(memory_block shmd (Int.repr 32) md)))
  Body_final_if1
  (normal_ret_assert (invariant_after_if1 hashed dd c md shmd hi lo)).
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
forward_call (* memset (p+n,0,SHA_CBLOCK-n); *)
   ((Tsh,
     offset_val (Int.repr (ddlen + 1)) (offset_val (Int.repr 40) c)%Z, 
     (CBLOCKz - (ddlen + 1)))%Z,
     Int.zero).
  {entailer!.
  + rewrite Int.unsigned_repr; auto. 
      change CBLOCKz with 64 in Hddlen; repable_signed.
  + change CBLOCKz with 64 in Hddlen.
   rewrite (split_array_at (ddlen+1) tuchar) by omega.
   repeat rewrite <- sepcon_assoc;
    pull_left (array_at tuchar Tsh (ZnthV tuchar (map Vint (map Int.repr dd) ++ [Vint (Int.repr 128)]))
   (ddlen + 1) 64 (offset_val (Int.repr 40) c)).
   repeat rewrite sepcon_assoc; apply sepcon_derives; [ | cancel].
  change CBLOCKz with 64%Z.
  destruct (zlt (ddlen+1) 64).
Focus 2. {
 replace (ddlen+1)%Z with 64%Z by omega. rewrite array_at_emp.
 rewrite Z.sub_diag.
 destruct c; try (contradiction Pc). simpl. 
 rewrite memory_block_zero. normalize.
 } Unfocus.
 rewrite memory_block_array_tuchar by Omega1.
 replace (offset_val (Int.repr (40 + (ddlen+1))) c)%Z
  with (offset_val (Int.repr (sizeof tuchar * (ddlen+1))) (offset_val (Int.repr 40) c))%Z
  by (normalize; Omega1).
   rewrite <- offset_val_array_at_.
  rewrite Z.add_0_r.
 replace (ddlen + 1 + (64 - (ddlen+1)))%Z with 64%Z by (clear; omega).
 cancel.
}
  forward.  (* n=0; *)
gather_SEP 4%Z 0%Z.
pose (ddz := ((map Int.repr dd ++ [Int.repr 128]) ++ list_repeat (Z.to_nat (CBLOCKz-(ddlen+1))) Int.zero)).
replace_SEP 0%Z (  `(array_at tuchar Tsh
        (ZnthV tuchar (map Vint ddz)) 0 64
        (offset_val (Int.repr 40) c))).
{entailer!.
 normalize in H0.
 change CBLOCKz with 64 in Hddlen.
 apply ltu_repr in H0; [ | Omega1 | Omega1].
 change (16*4)%Z with (CBLOCKz) in H0.
 rewrite (split_array_at (ddlen+1) tuchar _ _ 0 64) by Omega1.
 apply sepcon_derives.
 + apply derives_refl'; apply equal_f; apply array_at_ext; intros.
    unfold ZnthV. if_tac; try omega.
    unfold ddz.
    repeat rewrite map_app. simpl map.
   set (dd1 :=  map Vint (map Int.repr dd) ++ [Vint (Int.repr 128)%Z]).
   rewrite app_nth1. auto. 
   unfold dd1; rewrite app_length. 
   clear - H1; unfold ddlen in *; rewrite Zlength_correct in *;
   rewrite map_length in *. simpl.
    apply Nat2Z.inj_lt. rewrite Z2Nat.id by Omega1.
  rewrite map_length; rewrite Nat2Z.inj_add; Omega1.
 +  clear - Pc_ Hddlen.
 assert (ddlen = Zlength dd) by reflexivity.
  replace (Int.repr (40+(ddlen+1))%Z)
   with (Int.add  (Int.repr 40) (Int.repr (sizeof tuchar * (ddlen+1))))%Z
  by normalize.
 rewrite <- offset_offset_val.
 rewrite <- offset_val_array_at.
 rewrite Z.add_0_r.
 change CBLOCKz with 64%Z.
 replace (ddlen + 1 + (64 - (ddlen + 1)))%Z with 64%Z by omega.
 apply derives_refl'; apply equal_f; apply array_at_ext; intros.
 symmetry.
 unfold ZnthV. rewrite if_false by omega.
 unfold ddz. clear ddz. rewrite map_app.
 rewrite app_nth2;  rewrite map_length; rewrite app_length.
  rewrite (nth_map' Vint _ Int.zero).
 f_equal.
 apply nth_list_repeat.
  simpl. rewrite map_length, length_list_repeat.
 change CBLOCKz with 64.
 replace (length dd + 1)%nat with (Z.to_nat (ddlen + 1)).
 rewrite <- Z2Nat.inj_sub by omega.
 apply Z2Nat.inj_lt; try omega. rewrite H.
 rewrite Z2Nat.inj_add; try omega.
 rewrite Zlength_correct, Nat2Z.id. auto.
 rewrite map_length; simpl. Omega1.
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
change CBLOCKz with (Z.of_nat CBLOCK) in H0.
apply Nat2Z.inj_lt in H0. omega.
}
assert (H1: length ddzw = LBLOCK). {
unfold ddzw.
apply length_Zlist_to_intlist. rewrite map_length. apply H0'.
}
assert (H0: map Int.unsigned ddz = intlist_to_Zlist ddzw). {
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
 forward_call (* sha256_block_data_order (c,p); *)
  (hashed, ddzw, c, offset_val (Int.repr 40) c, Tsh).
 {entailer!.
* rewrite Zlength_correct, H1; reflexivity.
* cancel.
 repeat rewrite sepcon_assoc; apply sepcon_derives; [ | cancel].
 unfold data_block.
 simpl. apply andp_right.
 apply prop_right.
 apply isbyte_intlist_to_Zlist.
 apply derives_refl'; f_equal. 
 unfold tuchars. f_equal. f_equal.
 rewrite <- H0.
 rewrite map_map.
 replace (fun x => Int.repr (Int.unsigned x)) with (@id int) by 
  (extensionality xx; rewrite Int.repr_unsigned; auto).
 symmetry; apply map_id.
 rewrite Zlength_correct;rewrite length_intlist_to_Zlist;
  rewrite H1; reflexivity.
}
unfold invariant_after_if1.
 apply exp_right with (hashed ++ ddzw).
set (pad := (CBLOCKz - (ddlen+1))%Z) in *.
 apply exp_right with (@nil Z).
 apply exp_right with pad.
entailer.
normalize in H5.
apply ltu_repr in H5; [ | split; computable 
  | change CBLOCKz with 64 in Hddlen; Omega1].
simpl in H2.
assert (0 <= pad < 8)%Z.
unfold pad.
change (16*4)%Z with (CBLOCKz) in H5. 
change (CBLOCKz) with CBLOCKz in H5|-*; omega.
assert (length (list_repeat (Z.to_nat pad) 0) < 8)%nat.
rewrite length_list_repeat.
apply Nat2Z.inj_lt.
rewrite Z2Nat.id by omega.
Omega1. 
entailer!.
* clear; Omega1.
* rewrite initial_world.Zlength_app.
   apply Zlength_length in H1; [ | auto]. rewrite H1.
 clear - H4; destruct H4 as [n ?]; exists (n+1). 
  rewrite Z.mul_add_distr_r; omega.
* rewrite <- app_nil_end.
  rewrite intlist_to_Zlist_app.
  f_equal.
  rewrite <- H0.
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
* cancel.
  unfold data_block.
 simpl. apply andp_left2.
  replace (Zlength (intlist_to_Zlist ddzw)) with 64%Z.
 apply array_at_array_at_.
 rewrite Zlength_correct; rewrite length_intlist_to_Zlist.
 rewrite H1;  reflexivity.
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
                                      tvoid))
                                [Ecast (Etempvar _md (tptr tuchar))
                                   (tptr tuint), Etempvar _ll tuint])
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
 destruct n; try reflexivity.
 destruct n; try reflexivity.
 destruct n; try reflexivity.
 destruct n; try reflexivity.
 destruct n; try reflexivity.
 replace (n + S i * 4)%nat with (n+4 + i*4)%nat
  by (simpl; omega).
 destruct al as [ | a al].
 rewrite (nth_overflow nil) by (simpl; clear; omega).
 simpl firstn. simpl intlist_to_Zlist.
 rewrite (nth_overflow nil) by (simpl; clear; omega).
 destruct n; try reflexivity.
 destruct n; try reflexivity.
 destruct n; try reflexivity.
 destruct n; try reflexivity.
 destruct n; try reflexivity.
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
 forall (Espec: OracleKind) md c shmd hashedmsg,
 length hashedmsg = 8%nat ->
 writable_share shmd ->
semax
  (initialized _cNl (initialized _cNh Delta_final_if1))
  (PROP  ()
   LOCAL  (`(eq md) (eval_id _md); `(eq c) (eval_id _c))
   SEP 
   (`(array_at tuchar Tsh (fun _ : Z => Vint Int.zero) 0 64
        (offset_val (Int.repr 40) c));
   `(array_at tuint Tsh (tuints hashedmsg) 0 8 c); K_vector;
   `(field_at_ Tsh t_struct_SHA256state_st _Nl c);
   `(field_at_ Tsh t_struct_SHA256state_st _Nh c);
   `(field_at Tsh t_struct_SHA256state_st _num (Vint (Int.repr 0)) c);
   `(memory_block shmd (Int.repr 32) md)))
  (Ssequence final_loop (Sreturn None))
  (function_body_ret_assert tvoid
     (PROP  ()
      LOCAL ()
      SEP  (K_vector; `(data_at_ Tsh t_struct_SHA256state_st c);
      `(data_block shmd (intlist_to_Zlist hashedmsg) md)))).
Proof.
intros.
unfold final_loop; simplify_Delta; abbreviate_semax.
rewrite memory_block_isptr by computable.
normalize. rename H1 into Hmd.
forward.  (* xn=0; *)

Definition part4_inv  c shmd hashedmsg md delta (i: nat) :=
   (PROP  ((i <= 8)%nat)
   LOCAL  (`(eq (Vint (Int.repr (Z.of_nat i - delta)))) (eval_id _xn);
      `(eq (offset_val (Int.repr (Z.of_nat i * 4)) md)) (eval_id _md);
   `(eq c) (eval_id _c))
   SEP 
   (`(array_at tuchar Tsh (fun _ : Z => Vint Int.zero) 0 64
        (offset_val (Int.repr 40) c));
   `(array_at tuint Tsh (tuints hashedmsg) 0 8 c); K_vector;
   `(field_at_ Tsh t_struct_SHA256state_st _Nl c);
   `(field_at_ Tsh t_struct_SHA256state_st _Nh c);
   `(field_at Tsh t_struct_SHA256state_st _num (Vint (Int.repr 0)) c);
   `(array_at tuchar shmd (tuchars (map Int.repr (intlist_to_Zlist (firstn i hashedmsg))))
              0 32 md))).

forward_for 
   (EX i:_, part4_inv c shmd hashedmsg md 0 i) 
   (EX i:_, part4_inv c shmd hashedmsg md 1 i) 
   (part4_inv c shmd hashedmsg md 0 8).
* apply exp_right with 0%nat. unfold part4_inv; rewrite Z.sub_0_r.
  entailer!.
  change 32%Z with (sizeof (tarray tuchar 32)).
  rewrite memory_block_typed by reflexivity.
  simpl_data_at. cancel.
* unfold part4_inv; entailer!.
* unfold part4_inv.  repeat rewrite Z.sub_0_r.
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
* unfold part4_inv.
 rewrite insert_local.
 match goal with |- semax _ (PROPx _ (LOCALx (_:: ?Q) ?R)) _ _ =>
   apply semax_pre with (PROP ((i<8)%nat) (LOCALx Q R))
  end.
 rewrite Z.sub_0_r.
 entailer!.
 change (Int.divs (Int.repr 32) (Int.repr 4)) with (Int.repr 8) in H3.
 apply ltu_repr in H3; try repable_signed; try omega.
 normalize.
 rewrite Z.sub_0_r.
 forward. (* ll=(c)->h[xn]; *)
  entailer!.
  unfold tuints, ZnthV. rewrite if_false by omega.
  rewrite Nat2Z.id.
  rewrite (nth_map' Vint _ Int.zero).
  apply I.
  omega.
 pose (w := nth i hashedmsg Int.zero).
 pose (bytes := Basics.compose force_int (ZnthV tuchar (map Vint (map Int.repr (intlist_to_Zlist [w]))))).
  forward_call (* builtin_write32_reversed *)
     (offset_val (Int.repr (Z.of_nat i * 4)) md, shmd, bytes).
 entailer!.
  rewrite Int.signed_repr in H3 by repable_signed.
  auto.
 destruct md; try (contradiction Hmd); reflexivity.
 unfold tuints, ZnthV in H3.
 rewrite Int.signed_repr in H3 by repable_signed.
  rewrite if_false in H3 by omega.
 rewrite Nat2Z.id in H3.
 rewrite (nth_map' _ _ Int.zero) in H3 by omega.
 inv H3.
 symmetry; unfold bytes, Basics.compose;
 replace (fun x : Z =>
   force_int
     (ZnthV tuchar
        (map Vint (map Int.repr (intlist_to_Zlist [w]))) x))
  with 
  (fun x : Z =>
   force_int
     (ZnthV tuchar
        (map Vint (map Int.repr (intlist_to_Zlist [w]))) 
              (x + Z.of_nat O * 4)))
 by (extensionality j; repeat f_equal; simpl; apply Z.add_0_r).
 apply nth_big_endian_integer.
 reflexivity.
{
 entailer.
 change (Int.repr 4) with (Int.repr (sizeof (tarray tuchar 4))); 
  rewrite memory_block_typed by reflexivity; simpl_data_at.
 rewrite (split_array_at (Z.of_nat i * 4) tuchar _ _ 0 32 md)
  by (split; omega).
 rewrite (split_array_at (Z.of_nat (S i) * 4) tuchar _ _ _ 32 md)
   by (rewrite inj_S; split; omega).
 repeat rewrite <- sepcon_assoc;
 pull_left  (array_at tuchar shmd
    (tuchars (map Int.repr (intlist_to_Zlist (firstn i hashedmsg))))
    (Z.of_nat i * 4) (Z.of_nat (S i) * 4) md);
 repeat rewrite sepcon_assoc; apply sepcon_derives; [ | cancel_frame].
 replace (offset_val (Int.repr (Z.of_nat i * 4)))
   with (offset_val (Int.repr (sizeof tuchar * (Z.of_nat i * 4))))
  by (f_equal; f_equal; apply Z.mul_1_l).
 rewrite array_at_ZnthV_nil.

 rewrite <- offset_val_array_at_.
 rewrite Z.add_0_r.
 replace  (Z.of_nat (S i) * 4)%Z  with (Z.of_nat i * 4 + 4)%Z; 
   [ apply array_at_array_at_ |].
 rewrite inj_S. unfold Z.succ.
 rewrite Z.mul_add_distr_r. reflexivity.
}
 normalize.
 forward. (* md += 4; *)
 entailer!.
 unfold loop1_ret_assert;  simpl update_tycon.
 unfold part4_inv. apply exp_right with (S i). rewrite inj_S.
{
 entailer!.
 f_equal; omega.
 destruct md; try (contradiction Hmd); simpl; f_equal.
 f_equal. f_equal.
 unfold Z.succ. rewrite Z.mul_add_distr_r. reflexivity.
 replace (match hashedmsg with
               | [] => []
               | a :: l => a :: firstn i l
               end) with (firstn (S i) hashedmsg)
  by (clear; destruct hashedmsg; auto).
 rewrite (split_array_at (Z.of_nat i * 4) tuchar _ _ 0 32 md)
  by (split; omega).
 rewrite (split_array_at (Z.of_nat (S i) * 4) tuchar _ _ (Z.of_nat i * 4) 32 md)
   by (rewrite inj_S; split; omega).
 replace (offset_val (Int.repr (Z.of_nat i * 4)))
   with (offset_val (Int.repr (sizeof tuchar * (Z.of_nat i * 4))))
  by (f_equal; f_equal; apply Z.mul_1_l).
 rewrite <- offset_val_array_at.
 repeat rewrite <- sepcon_assoc.
 pull_left (array_at tuchar shmd
  (tuchars (map Int.repr (intlist_to_Zlist (firstn i hashedmsg)))) 0
  (Z.of_nat i * 4) md).
 repeat apply sepcon_derives; auto.
 apply derives_refl'; apply equal_f; apply array_at_ext; intros.
 unfold tuchars, ZnthV. rewrite if_false by omega.
 rewrite if_false by omega.
 rewrite map_map. rewrite map_map.
 rewrite (nth_map' _ _ 0%Z).
Focus 2.
 clear - H4 H H1. rewrite length_intlist_to_Zlist. rewrite firstn_length.
  rewrite min_l by omega. destruct H4.
  apply Nat2Z.inj_lt. rewrite Z2Nat.id by omega.
  rewrite Nat2Z.inj_mul; rewrite Z.mul_comm; auto.
 rewrite (nth_map' _ _ 0%Z).
Focus 2. clear - H4 H H1. rewrite length_intlist_to_Zlist. rewrite firstn_length.
  rewrite min_l by omega. destruct H4.
  apply Nat2Z.inj_lt. rewrite Z2Nat.id by omega.
  rewrite Nat2Z.inj_mul. 
 rewrite Z.mul_comm; rewrite inj_S.
 unfold Z.succ; rewrite Z.mul_add_distr_r. 
 change (1 * Z.of_nat 4) with 4.  change (Z.of_nat 4) with 4; omega.
 do 2 f_equal.
apply (nth_intlist_to_Zlist_eq _ (S (Z.to_nat i0))); try omega.
 apply Nat2Z.inj_lt. rewrite Z2Nat.id by (clear - H4; omega).
  rewrite Nat2Z.inj_mul; apply H4.
 apply Nat2Z.inj_lt. rewrite Z2Nat.id by (clear - H4; omega).
 clear - H4; rewrite Nat2Z.inj_mul; rewrite inj_S;
  unfold Z.succ; rewrite Z.mul_add_distr_r.
  change (Z.of_nat 4) with 4; omega.
 rewrite Z.add_0_r.
 replace  (Z.of_nat (S i) * 4)%Z  with (Z.of_nat i * 4 + 4)%Z
  by (rewrite inj_S; unfold Z.succ; rewrite Z.mul_add_distr_r; reflexivity).
 apply derives_refl'; apply equal_f; apply array_at_ext; intros.
 unfold cVint, bytes, tuchars, ZnthV, Basics.compose.
 rewrite if_false by omega. rewrite if_false by omega.
 repeat rewrite map_map.
 rewrite (nth_map' _ _ 0).
Focus 2.
 simpl. apply Nat2Z.inj_lt. rewrite Z2Nat.id by omega.
 change (Z.of_nat 4) with 4; omega.
 rewrite (nth_map' _ _ 0).
Focus 2. clear - H4 H H1. rewrite length_intlist_to_Zlist. 
 rewrite firstn_length;  rewrite min_l by omega. destruct H4.
  apply Nat2Z.inj_lt. rewrite Z2Nat.id by omega.
  rewrite Nat2Z.inj_mul. 
 rewrite Z.mul_comm; rewrite inj_S.
 unfold Z.succ; rewrite Z.mul_add_distr_r. 
 change (1 * Z.of_nat 4) with 4.  change (Z.of_nat 4) with 4; omega.
 unfold force_int. f_equal. f_equal.
 clear - H4.
 assert (Z.to_nat i0 = (Z.to_nat i0 - i*4) + (i * 4))%nat.
 destruct H4 as [? _]. apply Z2Nat.inj_le in H; try omega.
 change 4 with (Z.of_nat 4) in H. rewrite <- Nat2Z.inj_mul in H.  
 rewrite Nat2Z.id in H. omega. clear H4.
 unfold w; clear w.
 rewrite Z2Nat.inj_sub by omega.
  change 4 with (Z.of_nat 4). rewrite <- Nat2Z.inj_mul.  
 rewrite Nat2Z.id. 
 assert (i*4 <= Z.to_nat i0)%nat by omega.
 apply nth_intlist_to_Zlist_first_hack; auto.
 rewrite inj_S.
 apply derives_refl'; apply equal_f; apply array_at_ext; intros.
 unfold tuchars, ZnthV. rewrite if_false by omega.
 rewrite if_false by omega.
 rewrite map_map. rewrite map_map.
 rewrite nth_overflow.
Focus 2. {
  rewrite map_length, length_intlist_to_Zlist, firstn_length.
   rewrite min_l by omega.
  unfold Z.succ in H4.
  destruct H4 as [H4 _].
 apply Z2Nat.inj_le in H4; try omega.
 rewrite Z.mul_add_distr_r in H4.
 rewrite Z2Nat.inj_add in H4 by omega.
 change (Z.to_nat (1*4)) with 4%nat in H4.
 rewrite mult_comm.
 replace (i*4)%nat with (Z.to_nat (Z.of_nat i * 4)); [omega | ].
 clear. change 4 with (Z.of_nat 4); rewrite <- Nat2Z.inj_mul;
  rewrite Nat2Z.id; auto.
} Unfocus.
 rewrite nth_overflow; [reflexivity | ]. {
 rewrite map_length, length_intlist_to_Zlist, firstn_length.
  rewrite min_l by omega.
 clear - H4 H H1.
 destruct H4 as [H4 _].
 apply Z2Nat.inj_le in H4; try omega.
 unfold Z.succ in H4.
 rewrite Z.mul_add_distr_r in H4.
 rewrite Z.mul_1_l in H4.
 change 4 with (Z.of_nat 4) in H4.
 rewrite <- Nat2Z.inj_mul, <- Nat2Z.inj_add in H4.
 rewrite Nat2Z.id in H4.
 rewrite mult_comm.
 replace (S i) with (i+1)%nat by omega.
 rewrite  NPeano.Nat.mul_add_distr_r.
 apply H4.
}
}
* (* for-loop increment *)
 unfold part4_inv. apply extract_exists_pre; intro i.
 normalize.
 forward. (* xn++; *)
 unfold part4_inv. normalize.
 apply exp_right with i.
  rewrite Z.sub_0_r.
 entailer.
 apply prop_right. inv H3. 
 normalize. f_equal. omega.
* (* after the loop *)
 unfold part4_inv. 
  rewrite (firstn_same _ 8) by omega.
 forward. (* return; *)
 simpl_data_at.
 repeat rewrite array_at_ZnthV_nil.
 unfold at_offset.  unfold data_block.
 rewrite prop_true_andp by apply isbyte_intlist_to_Zlist.
 replace (Zlength (intlist_to_Zlist hashedmsg)) with 32%Z.
 cancel.
 rewrite Zlength_correct; rewrite length_intlist_to_Zlist; rewrite H; reflexivity.
Qed.
