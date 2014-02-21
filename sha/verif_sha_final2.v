Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.sha_lemmas.
Require Import sha.spec_sha.
Local Open Scope logic.

Hint Rewrite eval_var_env_set : norm. (* needed? *)

Definition Delta_final_if1 : tycontext :=
 initialized _n
          (initialized _p
     (func_tycontext f_SHA256_Final Vprog Gtot)).

Lemma map_swap_involutive:
 forall l, map swap (map swap l)  = l.
Proof. intros.
 rewrite map_map. 
 replace (fun x => swap (swap x)) with (@Datatypes.id int).
 apply map_id. extensionality x. symmetry; apply swap_swap.
Qed.

Lemma K_vector_globals:
  forall Delta rho g,  tc_environ Delta rho /\
       (var_types Delta) ! _K256 = None /\ (glob_types Delta) ! _K256 = Some g ->
       K_vector (globals_only rho) = K_vector rho.
Proof. 
  intros; unfold K_vector.
  unfold_lift.
  erewrite elim_globals_only; eauto.
Qed.

Definition Body_final_if1 := 
  (Ssequence
              (Ssequence
                (Scall (Some _ignore')
                  (Evar _memset (Tfunction
                                  (Tcons (tptr tvoid)
                                    (Tcons tint (Tcons tuint Tnil)))
                                  (tptr tvoid)))
                  ((Ebinop Oadd (Etempvar _p (tptr tuchar))
                     (Etempvar _n tuint) (tptr tuchar)) ::
                   (Econst_int (Int.repr 0) tint) ::
                   (Ebinop Osub
                     (Ebinop Omul (Econst_int (Int.repr 16) tint)
                       (Econst_int (Int.repr 4) tint) tint)
                     (Etempvar _n tuint) tuint) :: nil))
                (Sset _ignore (Etempvar _ignore' (tptr tvoid))))
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
              NPeano.divide LBLOCK (length hashed');
              intlist_to_Zlist hashed' ++ dd' =
              intlist_to_Zlist hashed ++  dd 
                  ++ [128%Z] ++ map Int.unsigned (zeros pad)   )          
   LOCAL 
   (`(eq (Vint (Int.repr (Zlength dd')))) (eval_id _n);
   `eq (eval_id _p)
     (`(offset_val (Int.repr 40)) (`force_ptr (eval_id _c)));
   `(eq md) (eval_id _md); `(eq c) (eval_id _c))
   SEP  (`(array_at tuint Tsh (ZnthV tuint (map Vint (process_msg init_registers hashed'))) 0 8 c);
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
 (H4: NPeano.divide LBLOCK (length hashed))
 (H7: ((Zlength hashed * 4 + Zlength dd)*8 = hilo hi lo)%Z)
 (H3: (length dd < CBLOCK)%nat)
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
        (ZnthV tuint (map Vint (process_msg init_registers hashed))) 0 8 c);
   `(field_at Tsh t_struct_SHA256state_st _Nl (Vint lo) c);
   `(field_at Tsh t_struct_SHA256state_st _Nh (Vint hi) c);
   `(array_at tuchar Tsh
       (ZnthV tuchar (map Vint (map Int.repr dd) ++ [Vint (Int.repr 128)])) 0 64
       (offset_val (Int.repr 40) c));
   `(field_at Tsh t_struct_SHA256state_st _num (Vint (Int.repr (Zlength dd))) c);
   K_vector; `(memory_block shmd (Int.repr 32) md))) Body_final_if1
  (normal_ret_assert (invariant_after_if1 hashed dd c md shmd hi lo)).
Proof.
assert (H:=True).
name md_ _md.
name c_ _c.
name p _p.
name n _n.
name cNl _cNl.
name cNh _cNh.
name ignore _ignore.
intros.
assert (Hddlen: (0 <= Zlength dd < 64)%Z) by Omega1.
set (ddlen := Zlength dd) in *.
 unfold Delta_final_if1; simplify_Delta; unfold Body_final_if1; abbreviate_semax.
 forward.
  {instantiate (1:= (Tsh,
     offset_val (Int.repr (ddlen + 1)) (offset_val (Int.repr 40) c)%Z, 
     (Z.of_nat CBLOCK - (ddlen + 1))%Z,
     Int.zero)) in (Value of witness).
  unfold tc_exprlist. simpl denote_tc_assert.  (* this line should not be necessary *)
  entailer!.
  + normalize in H1; rewrite H1; reflexivity.
  + rewrite (split_array_at (ddlen+1) tuchar) by omega.
   repeat rewrite <- sepcon_assoc;
    pull_left (array_at tuchar Tsh (ZnthV tuchar (map Vint (map Int.repr dd) ++ [Vint (Int.repr 128)]))
   (ddlen + 1) 64 (offset_val (Int.repr 40) c)).
   repeat rewrite sepcon_assoc; apply sepcon_derives; [ | cancel].
  change (Z.of_nat CBLOCK) with 64%Z.
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
 apply array_at__array_at.
 }
  forward. (* finish the call *)
  forward.  (* n=0; *)
replace_SEP 0%Z (
      `(array_at tuchar Tsh (fun _ => Vint Int.zero) 0
          (Z.of_nat CBLOCK - (ddlen + 1))
          (offset_val (Int.repr (ddlen + 1)) (offset_val (Int.repr 40) c)))).
entailer!.
gather_SEP 4%Z 0%Z.
pose (ddz := ((map Int.repr dd ++ [Int.repr 128]) ++ zeros (Z.of_nat CBLOCK-(ddlen+1)))%Z).
replace_SEP 0%Z (  `(array_at tuchar Tsh
        (ZnthV tuchar (map Vint ddz)) 0 64
        (offset_val (Int.repr 40) c))).
{entailer!.
 normalize in H0. (* rewrite mul_repr, sub_repr in H0. *)
 apply ltu_repr in H0; [ | Omega1 | Omega1].
 change (16*4)%Z with (Z.of_nat CBLOCK) in H0.
 rewrite (split_array_at (ddlen+1) tuchar _ _ 0 64).
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
 change (Z.of_nat CBLOCK) with 64%Z.
 replace (ddlen + 1 + (64 - (ddlen + 1)))%Z with 64%Z by omega.
 apply derives_refl'; apply equal_f; apply array_at_ext; intros.
 symmetry.
 unfold ZnthV. rewrite if_false by omega.
 unfold ddz. clear ddz. rewrite map_app.
 rewrite app_nth2;  rewrite map_length; rewrite app_length.
 rewrite nth_map_zeros; [reflexivity |].
 simpl. rewrite map_length; Omega1.
 simpl. rewrite map_length;  Omega1.
 + Omega1.
 }
pose (ddzw := Zlist_to_intlist (map Int.unsigned ddz)).
assert (H0': length ddz = CBLOCK). {
unfold ddz; repeat rewrite app_length.
rewrite length_zeros by omega.
rewrite Z2Nat.inj_sub by omega.
rewrite Z2Nat.inj_add by omega.
rewrite (Nat2Z.id). unfold ddlen; rewrite Zlength_correct. 
rewrite (Nat2Z.id). rewrite map_length; simpl length; change (Z.to_nat 1) with 1%nat; omega.
}
assert (H1: length ddzw = LBLOCK). {
unfold ddzw.
apply length_Zlist_to_intlist. rewrite map_length. apply H0'.
}
assert (H0: map Int.unsigned ddz = intlist_to_Zlist ddzw). {
unfold ddzw; rewrite Zlist_to_intlist_to_Zlist; auto.
rewrite map_length, H0'; exists LBLOCK; reflexivity.
unfold ddz; repeat rewrite map_app; repeat rewrite Forall_app; repeat split; auto.
Lemma Forall_isbyteZ_unsigned_repr:
 forall l, Forall isbyteZ l -> Forall isbyteZ (map Int.unsigned (map Int.repr l)).
Proof. induction 1. constructor.
constructor. rewrite Int.unsigned_repr; auto.
unfold isbyteZ in H; repable_signed.
apply IHForall.
Qed.
apply Forall_isbyteZ_unsigned_repr; auto.
constructor. compute. clear; split; congruence.
constructor.
apply isbyte_zeros.
}
clear H0'.
clearbody ddzw.

 forward. (* sha256_block_data_order (c,p); *)
 match goal with H : True |- _ => clear H 
            (* WARNING__ is a bit over-eager;
                need to tell it that K_vector is closed *)
  end.

simpl typeof.
instantiate (1:=(hashed, 
                           ddzw,
                           c, 
                           offset_val (Int.repr 40) c,
                           Tsh)) in (Value of witness).
{entailer!.
* subst;  simpl in *. normalize in H5.
* erewrite K_vector_globals by (split3; [eassumption | reflexivity.. ]).
 cancel.
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
set (pad := (Z.of_nat CBLOCK - (ddlen+1))%Z) in *.
 apply exp_right with (@nil Z).
 apply exp_right with pad.
entailer.
normalize in H5.
apply ltu_repr in H5; [ | split; computable | Omega1].
simpl in H2.
assert (0 <= pad < 8)%Z.
unfold pad.
change (16*4)%Z with (Z.of_nat CBLOCK) in H5. 
change (64)%Z with (Z.of_nat CBLOCK) in Hddlen; omega.
assert (length (zeros pad) < 8)%nat. 
rewrite length_zeros.
apply Nat2Z.inj_lt.
rewrite Z2Nat.id by omega.
Omega1. 
entailer!.
* clear; Omega1.
* apply divide_length_app.
  auto. exists 1%nat; rewrite H1; reflexivity.
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
* erewrite K_vector_globals by (split3; [eassumption | reflexivity.. ]).
  cancel.
  unfold data_block.
 simpl. apply andp_left2.
  replace (Zlength (intlist_to_Zlist ddzw)) with 64%Z.
 apply array_at__array_at.
 rewrite Zlength_correct; rewrite length_intlist_to_Zlist.
 rewrite H1;  reflexivity.
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

Lemma final_part4:
 forall (Espec: OracleKind) md c shmd hashedmsg,
 length hashedmsg = 8%nat ->
 writable_share shmd ->
semax
  (initialized _ignore'2
     (initialized _cNl
        (initialized _cNh
           (initialized _ignore (initialized _ignore'1 Delta_final_if1)))))
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
  forward. (* builtin_write32_reversed *)
  instantiate (1:= (offset_val (Int.repr (Z.of_nat i * 4)) md,
                             shmd, bytes)) in (Value of witness).
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
   [ apply array_at__array_at |].
 rewrite inj_S. unfold Z.succ.
 rewrite Z.mul_add_distr_r. reflexivity.
 normalize.
 forward.
 entailer!.
 unfold loop1_ret_assert;  simpl update_tycon.
 unfold part4_inv. apply exp_right with (S i). rewrite inj_S.
 entailer!.
 f_equal; omega.
 destruct md; try (contradiction Hmd); simpl; f_equal.
 f_equal. f_equal.
 unfold Z.succ. rewrite Z.mul_add_distr_r. reflexivity.
 replace (match hashedmsg with
               | [] => []
               | a :: l => a :: firstn i l
               end) with (firstn (S i) hashedmsg).
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
 rewrite (nth_map' _ _ 0%Z)
   by admit.  (* straightforward *)
 rewrite (nth_map' _ _ 0%Z)
   by admit.  (* straightforward *)
 do 2 f_equal.
 admit. (* straightforward, probably even true *)
 rewrite Z.add_0_r.
 replace  (Z.of_nat (S i) * 4)%Z  with (Z.of_nat i * 4 + 4)%Z
  by (rewrite inj_S; unfold Z.succ; rewrite Z.mul_add_distr_r; reflexivity).
 apply derives_refl'; apply equal_f; apply array_at_ext; intros.
 unfold cVint, bytes, tuchars, ZnthV, Basics.compose.
 rewrite if_false by omega. rewrite if_false by omega.
 rewrite (nth_map' _ _ Int.zero).
 rewrite (nth_map' _ _ Int.zero).
 unfold force_int. f_equal.
 admit. (* straightforward *)
 admit. (* straightforward *)
 admit. (* straightforward *)
 rewrite inj_S.
 apply derives_refl'; apply equal_f; apply array_at_ext; intros.
 unfold tuchars, ZnthV. rewrite if_false by omega.
 rewrite if_false by omega.
 rewrite map_map. rewrite map_map.
 rewrite (nth_map' _ _ 0%Z)
   by admit.  (* straightforward *)
 rewrite (nth_map' _ _ 0%Z)
   by admit.  (* straightforward *)
 do 2 f_equal.
 admit. (* straightforward, perhaps even true *)
 simpl. auto.
* (* for-loop increment *)
 unfold part4_inv. apply extract_exists_pre; intro i.
 normalize.
 forward.
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
 unfold K_vector; normalize;
 erewrite elim_globals_only by (split3; [eassumption | reflexivity.. ]).
 simpl_data_at.
 repeat rewrite array_at_ZnthV_nil.
 unfold at_offset.  unfold data_block.
 rewrite prop_true_andp by apply isbyte_intlist_to_Zlist.
 replace (Zlength (intlist_to_Zlist hashedmsg)) with 32%Z.
Hint Resolve array_at__array_at : cancel.
 cancel.
 rewrite Zlength_correct; rewrite length_intlist_to_Zlist; rewrite H; reflexivity.
Qed.
