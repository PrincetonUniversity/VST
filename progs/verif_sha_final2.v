Require Import floyd.proofauto.
Require Import progs.sha.
Require Import progs.SHA256.
Require Import progs.sha_lemmas.
Require Import progs.spec_sha.
Local Open Scope logic.

Lemma const_liftx0:
  forall B (P: B), (fun _ : environ => P) = `P.
Proof. reflexivity. Qed.
Hint Rewrite const_liftx0 : norm.

Lemma sizeof_tarray_tuchar:
 forall (n:Z), (n>0)%Z -> (sizeof (tarray tuchar n) =  n)%Z.
Proof. intros.
 unfold sizeof,tarray; cbv beta iota.
  rewrite Z.max_r by omega.
  unfold alignof, tuchar; cbv beta iota.
  repeat  rewrite align_1. rewrite Z.mul_1_l. auto.
Qed.

Lemma Zlength_zeros: 
    forall n, (n>=0)%Z -> Zlength (zeros n) = n.
Proof.
intros.
rewrite <- (Z2Nat.id n) in * by omega.
clear H.
induction (Z.to_nat n).
reflexivity.
rewrite inj_S.
rewrite zeros_equation.
pose proof (Zgt_cases (Z.succ (Z.of_nat n0)) 0).
destruct (Z.succ (Z.of_nat n0) >? 0); try omega.
rewrite Zlength_cons.
f_equal.  rewrite <- IHn0.
f_equal. f_equal. omega.
Qed.

Lemma nth_map_zeros:
 forall i j v, (Z.of_nat i < j)%Z -> nth i (map Vint (zeros j)) v = Vint Int.zero.
Proof.
intros.
rewrite <- (Z2Nat.id j) in * by omega.
apply Nat2Z.inj_lt in H.
replace (Z.to_nat j) with (Z.to_nat j - S i + S i) by omega.
forget (Z.to_nat j - S i) as k.
clear j H.
rewrite Nat2Z.inj_add.
rewrite inj_S.
induction i.
rewrite zeros_equation.
pose proof (Zgt_cases (Z.of_nat k + Z.succ (Z.of_nat 0)) 0).
destruct (Z.of_nat k + Z.succ (Z.of_nat 0) >? 0); try omega.
simpl. reflexivity.
rewrite zeros_equation.
pose proof (Zgt_cases (Z.of_nat k + Z.succ (Z.of_nat (S i))) 0).
destruct (Z.of_nat k + Z.succ (Z.of_nat (S i)) >? 0); try omega.
rewrite map_cons.
unfold nth.
rewrite <- IHi.
unfold nth.
f_equal.
f_equal.
f_equal.
rewrite inj_S.
omega.
Qed.

Hint Rewrite eval_var_env_set : norm. (* needed? *)

Arguments sem_cmp_default c t1 t2 v1 v2 / .

Lemma closed_env_set:
 forall {B} i v (P: environ -> B) rho, 
     closed_wrt_vars (eq i) P -> 
     P (env_set rho i v) = P rho.
Proof.
 intros. hnf in H.
 symmetry; destruct rho; apply H.
 intros; simpl; destruct (ident_eq i i0). left; auto.
 right; rewrite Map.gso; auto.
Qed.
Hint Rewrite @closed_env_set using (solve[auto 50 with closed]) : norm.

Lemma ltu_repr: forall i j, 
 (0 <= i <= Int.max_unsigned -> 
  0 <= j <= Int.max_unsigned -> 
  Int.ltu (Int.repr i) (Int.repr j) = true -> i<j)%Z.
Proof.
intros. unfold Int.ltu in H1. if_tac in H1; inv H1.
repeat rewrite Int.unsigned_repr in H2 by assumption.
auto.
Qed.

Lemma length_zeros: forall n,  (n >= 0)%Z -> length (zeros n) = Z.to_nat n.
Proof.
intros. pose proof (Zlength_zeros n H). 
rewrite Zlength_correct in H0.
rewrite <- H0 at 2.
rewrite Nat2Z.id. auto.
Qed.

Definition Delta_final_if1 : tycontext :=
 initialized _n
          (initialized _p
     (func_tycontext f_SHA256_Final Vprog Gtot)).

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

Definition invariant_after_if1 hashed dd c md shmd  hi lo:= 
   (EX hashed':list int, EX dd': list int, EX pad:Z,
   PROP  (length (map Int.unsigned dd') + 8 <= CBLOCK;
              (0 <= pad < 8)%Z;
              NPeano.divide LBLOCK (length hashed');
              intlist_to_Zlist (map swap hashed') ++ map Int.unsigned dd' =
              intlist_to_Zlist (map swap hashed) ++ map Int.unsigned dd 
                  ++ [128%Z] ++ map Int.unsigned (zeros pad)   )          
   LOCAL 
   (`(eq (Vint (Int.repr (Zlength dd')))) (eval_id _n);
   `eq (eval_id _p)
     (`(offset_val (Int.repr 40)) (`force_ptr (eval_id _c)));
   `(eq md) (eval_id _md); `(eq c) (eval_id _c))
   SEP  (`(array_at tuint Tsh (ZnthV tuint (map Vint (process_msg init_registers hashed'))) 0 8 c);
   `(field_at Tsh t_struct_SHA256state_st _Nl (Vint lo) c);
   `(field_at Tsh t_struct_SHA256state_st _Nh (Vint hi) c);
   `(array_at tuchar Tsh (ZnthV tuchar (map Vint dd')) 0 64 
                          (offset_val (Int.repr 40) c));
   `(field_at_ Tsh t_struct_SHA256state_st _num c);
     K_vector;
   `(memory_block shmd (Int.repr 32) md))).

Lemma map_swap_involutive:
 forall l, map swap (map swap l)  = l.
Proof. intros.
 rewrite map_map. 
 replace (fun x => swap (swap x)) with (@Datatypes.id int).
 apply map_id. extensionality x. symmetry; apply swap_swap.
Qed.

Lemma ifbody_final_if1:
  forall (Espec : OracleKind) (hashed : list int) (md c : val) (shmd : share)
  (hi lo : int) (dd : list int)
 (H4: NPeano.divide LBLOCK (length hashed))
 (H7: (Zlength hashed * 4 + Zlength dd = hilo hi lo)%Z)
 (H3: length dd < CBLOCK),
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
       (ZnthV tuchar (map Vint dd ++ [Vint (Int.repr 128)])) 0 64
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
assert (Hddlen: (0 <= Zlength dd < 64)%Z).
  split; auto; rewrite Zlength_correct; try omega.
 apply Z2Nat.inj_lt; try omega. rewrite Nat2Z.id. apply H3.
set (ddlen := Zlength dd) in *.
intros.
assert (H3': (ddlen < 64)%Z)
 by (unfold ddlen; rewrite Zlength_correct; change 64%Z with (Z.of_nat CBLOCK);
  apply Nat2Z.inj_lt; auto).
 unfold Delta_final_if1; simplify_Delta; unfold Body_final_if1; abbreviate_semax.
 forward.
  {instantiate (1:= (Tsh,
     offset_val (Int.repr (ddlen + 1)) (offset_val (Int.repr 40) c)%Z, 
     (Z.of_nat CBLOCK - (ddlen + 1))%Z,
     Int.zero)) in (Value of witness).
  unfold tc_exprlist. simpl denote_tc_assert.  (* this line should not be necessary *)
  entailer!.
  + hnf. rewrite mul_repr, sub_repr in H1. rewrite H1. reflexivity.
  + simpl. destruct c; try (contradiction Pc); simpl.
       f_equal; rewrite mul_repr. rewrite Int.add_assoc; f_equal.
       rewrite add_repr; change (align 1 1)%Z with 1%Z.
       rewrite Z.mul_1_l. f_equal; apply Z.add_comm.
  + rewrite (split_array_at (ddlen+1) tuchar) by omega.
   repeat rewrite <- sepcon_assoc;
    pull_left (array_at tuchar Tsh (ZnthV tuchar (map Vint dd ++ [Vint (Int.repr 128)]))
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
    replace (64 - (ddlen + 1))%Z
     with (sizeof (tarray tuchar (64 - (ddlen + 1))))%Z
    by (apply sizeof_tarray_tuchar; omega).
   rewrite memory_block_typed.
    replace (offset_val (Int.repr (40 + (ddlen+1))) c)%Z
    with (offset_val (Int.repr (sizeof tuchar * (ddlen+1))) (offset_val (Int.repr 40) c))%Z.
  set (jj:= (64-(ddlen+1))%Z).
  simpl_data_at.
   rewrite <- offset_val_array_at.
  rewrite Z.add_0_r.
 replace (ddlen + 1 + jj)%Z with 64%Z by (unfold jj; omega). clear jj.
 apply derives_refl'; apply equal_f; apply array_at_ext; intros.
 unfold ZnthV.
 rewrite if_false by omega.
 rewrite if_false by omega.
 repeat rewrite nth_overflow; auto.
 simpl; omega.
 rewrite app_length; rewrite map_length; simpl.
apply Nat2Z.inj_le. rewrite Z2Nat.id by omega.
 rewrite Nat2Z.inj_add. replace (Z.of_nat (length dd)) with ddlen.
 change (Z.of_nat 1) with 1%Z; omega.
 unfold ddlen. rewrite Zlength_correct; auto.
 rewrite offset_offset_val; f_equal.
 rewrite add_repr; simpl sizeof. change (align 1 1) with 1%Z.
 rewrite Z.mul_1_l. auto.
   reflexivity.
 }
  forward. (* finish the call *)
  forward.  (* n=0; *)
replace_SEP 0%Z (
      `(array_at tuchar Tsh (fun _ => Vint Int.zero) 0
          (Z.of_nat CBLOCK - (ddlen + 1))
          (offset_val (Int.repr (ddlen + 1)) (offset_val (Int.repr 40) c)))).
entailer!.
gather_SEP 4%Z 0%Z.
pose (ddz := ((dd ++ [Int.repr 128]) ++ zeros (Z.of_nat CBLOCK-(ddlen+1)))%Z).
replace_SEP 0%Z (  `(array_at tuchar Tsh
        (ZnthV tuchar (map Vint ddz)) 0 64
        (offset_val (Int.repr 40) c))).
{entailer!.
 rewrite mul_repr, sub_repr in H0.
 apply ltu_repr in H0.
 2: split; computable.
 2: assert (64 < Int.max_unsigned)%Z by computable; omega.
 change (16*4)%Z with (Z.of_nat CBLOCK) in H0.
 rewrite (split_array_at (ddlen+1) tuchar _ _ 0 64).
 apply sepcon_derives.
 + apply derives_refl'; apply equal_f; apply array_at_ext; intros.
    unfold ZnthV. if_tac; try omega.
    unfold ddz.
    repeat rewrite map_app. simpl map.
   set (dd1 :=  map Vint dd ++ [Vint (Int.repr 128)%Z]).
   rewrite app_nth1. auto. 
   unfold dd1; rewrite app_length. 
   clear - H1; unfold ddlen in *; rewrite Zlength_correct in *;
   rewrite map_length in *. simpl. 
   apply Nat2Z.inj_lt. rewrite Z2Nat.id by omega.
   rewrite Nat2Z.inj_add. change (Z.of_nat 1) with 1%Z. omega.
 +  clear - Pc_ Hddlen.
 assert (ddlen = Zlength dd) by reflexivity.
  replace (Int.repr (40+(ddlen+1))%Z)
   with (Int.add  (Int.repr 40) (Int.repr (sizeof tuchar * (ddlen+1))))%Z
  by (rewrite add_repr;  change (sizeof tuchar) with 1%Z;
  rewrite Z.mul_1_l; auto).
 rewrite <- offset_offset_val.
 rewrite <- offset_val_array_at.
 rewrite Z.add_0_r.
 change (Z.of_nat CBLOCK) with 64%Z.
 replace (ddlen + 1 + (64 - (ddlen + 1)))%Z with 64%Z by omega.
 apply derives_refl'; apply equal_f; apply array_at_ext; intros.
 symmetry.
 unfold ZnthV. rewrite if_false by omega.
 unfold ddz. clear ddz. rewrite map_app.
 rewrite app_nth2.
 rewrite nth_map_zeros; [reflexivity |].
 change (Z.of_nat CBLOCK) with 64%Z.
 rewrite map_length; rewrite app_length.
 apply Z2Nat.inj_lt; try omega.
 rewrite Nat2Z.id.
 replace (length dd + length [Int.repr 128]) with (Z.to_nat (ddlen + 1)).
 rewrite <- Z2Nat.inj_sub.
 apply Z2Nat.inj_lt; try omega. omega.
 rewrite H; simpl. rewrite Zlength_correct.
 rewrite Z2Nat.inj_add by omega. rewrite Nat2Z.id. f_equal.
 rewrite map_length, app_length.
  replace (length dd + length [Int.repr 128]) with (Z.to_nat (ddlen + 1)).
 apply Nat2Z.inj_ge; try omega.
 rewrite Z2Nat.id by omega.
 rewrite Z2Nat.id by omega.
 omega.
 rewrite H; simpl. rewrite Zlength_correct.
 rewrite Z2Nat.inj_add by omega. rewrite Nat2Z.id. f_equal.
 + omega.
 }

destruct (exists_intlist_to_Zlist' LBLOCK (map Int.unsigned ddz))
  as [ddzw [? ?]].
apply Nat2Z.inj. rewrite map_length.
unfold ddz; repeat rewrite app_length.
repeat rewrite Nat2Z.inj_add.
repeat rewrite <- Zlength_correct.
rewrite Zlength_zeros.
rewrite Zlength_cons; rewrite Zlength_nil.
unfold ddlen.
change (LBLOCK*4)%nat with CBLOCK.
clear; omega.
 change (Z.of_nat CBLOCK) with 64%Z; omega.
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
* subst;  simpl in *.
 rewrite mul_repr, sub_repr in H5. apply H5.
* unfold K_vector. normalize.
 erewrite elim_globals_only by (split3; [eassumption | reflexivity.. ]).
 cancel.
 repeat rewrite sepcon_assoc; apply sepcon_derives; [ | cancel].
 unfold data_block.
 apply derives_refl'; f_equal. 
 unfold tuchars. f_equal. f_equal.
 rewrite <- H0.
 rewrite map_map.
 replace (fun x => Int.repr (Int.unsigned x)) with (@id int) by 
  (extensionality xx; rewrite Int.repr_unsigned; auto).
 symmetry; apply map_id.
 rewrite Zlength_correct;rewrite length_intlist_to_Zlist; rewrite map_length;
  rewrite H1; reflexivity.
}
unfold invariant_after_if1.
 apply exp_right with (hashed ++ (* map swap *) ddzw).
set (pad := (Z.of_nat CBLOCK - (ddlen+1))%Z) in *.
 apply exp_right with (@nil int).
 apply exp_right with pad.
entailer.
rewrite mul_repr, sub_repr in H5.
apply ltu_repr in H5.
2: split; computable.
2: assert (64 < Int.max_unsigned)%Z by computable; omega.
simpl in H2.
assert (0 <= pad < 8)%Z.
unfold pad.
change (16*4)%Z with (Z.of_nat CBLOCK) in H5. 
change (64)%Z with (Z.of_nat CBLOCK) in Hddlen; omega.
assert (length (zeros pad) < 8). 
rewrite length_zeros.
apply Nat2Z.inj_lt.
rewrite Z2Nat.id by omega. 
change (Z.of_nat 8) with 8%Z. omega.
omega.
entailer!.
* change CBLOCK with 64; clear; omega.
* apply divide_length_app.
  auto. exists 1; rewrite H1; reflexivity.
* rewrite <- app_nil_end.
  rewrite map_app. 
  rewrite intlist_to_Zlist_app.
  repeat rewrite app_ass.
  f_equal.
  rewrite <- H0.
  unfold ddz.
  repeat rewrite map_app.
  repeat rewrite app_ass.
  simpl.
  rewrite Int.unsigned_repr; auto.
  repable_signed.
* unfold K_vector. normalize.
 erewrite elim_globals_only by (split3; [eassumption | reflexivity.. ]).
  cancel.
  unfold data_block.
  replace (Zlength (intlist_to_Zlist (map swap ddzw))) with 64%Z.
 apply array_at__array_at.
 rewrite Zlength_correct; rewrite length_intlist_to_Zlist.
 rewrite map_length; rewrite H1.
 reflexivity.
Qed.

Lemma ltu_repr_false: forall i j, 
 (0 <= i <= Int.max_unsigned -> 
  0 <= j <= Int.max_unsigned -> 
  Int.ltu (Int.repr i) (Int.repr j) = false -> i>=j)%Z.
Proof.
intros. unfold Int.ltu in H1. if_tac in H1; inv H1.
repeat rewrite Int.unsigned_repr in H2 by assumption.
auto.
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

Lemma lastblock_lemma:
  forall (hi lo : int) (pad : Z) (hashed dd hashed' dd' : list int),
length (map Int.unsigned dd') + 8 <= CBLOCK ->
(0 <= pad < 8)%Z ->
NPeano.divide LBLOCK (length hashed') ->
length dd < CBLOCK ->
NPeano.divide LBLOCK (length hashed) ->
intlist_to_Zlist (map swap hashed') ++ map Int.unsigned dd' =
intlist_to_Zlist (map swap hashed) ++
map Int.unsigned dd ++ [128%Z] ++ map Int.unsigned (zeros pad) ->
(Zlength hashed * 4 + Zlength dd)%Z = hilo hi lo ->
map Int.repr
  (intlist_to_Zlist
     (map swap
        (list_drop (length hashed')
           (generate_and_pad
              (intlist_to_Zlist (map swap hashed) ++ map Int.unsigned dd) 0)))) =
dd' ++
zeros (Z.of_nat CBLOCK - 8 - Zlength dd') ++
map Int.repr (intlist_to_Zlist (map swap [hi, lo])).
Proof.
intros.
Admitted.

Lemma nth_map':
  forall {A B} (f: A -> B) d d' i al,
  i < length al ->
   nth i (map f al) d = f (nth i al d').
Proof.
induction i; destruct al; simpl; intros; try omega; auto.
apply IHi; omega.
Qed.


Lemma array_at_ZnthV_nil:
  forall t sh, array_at t sh (ZnthV t nil) = array_at_ t sh.
Proof. intros.
unfold array_at_.
extensionality lo hi.
apply array_at_ext; intros.
unfold ZnthV. if_tac; auto. rewrite nth_overflow; auto.
simpl; omega.
Qed.


Lemma semax_for : 
 forall Espec Delta Q test body incr PreIncr Post,
     bool_type (typeof test) = true ->
     local (tc_environ Delta) && Q |-- local (tc_expr Delta test) ->
     local (tc_environ Delta) 
      && local (`(typed_false (typeof test)) (eval_expr test)) 
      && Q |-- Post EK_normal None ->
     @semax Espec Delta (local (`(typed_true (typeof test)) (eval_expr test)) && Q)
             body (loop1_ret_assert PreIncr Post) ->
     @semax Espec Delta PreIncr incr (normal_ret_assert Q) ->
     @semax Espec Delta Q
       (Sloop (Ssequence (Sifthenelse test Sskip Sbreak) body) incr)
       Post.
Proof.
intros.
apply semax_loop with PreIncr.
eapply semax_seq.
apply semax_pre_simple with  (local (tc_expr Delta test) && Q).
apply andp_right; auto.
apply andp_left2; auto.
apply semax_ifthenelse; auto.
eapply semax_post_flipped.
apply semax_skip.
intros.
unfold normal_ret_assert.
normalize. simpl exit_tycon.
unfold overridePost. rewrite if_true by auto. rewrite prop_true_andp by auto.
apply derives_refl.
eapply semax_pre_simple; [ | apply semax_break].
unfold overridePost. rewrite if_false by congruence.
unfold loop1_ret_assert.
eapply derives_trans; [ | apply H1].
rewrite andp_assoc.
apply andp_derives; auto.
rewrite andp_comm.
auto.
simpl update_tycon. 
apply semax_extensionality_Delta with Delta.
apply tycontext_eqv_sub.
apply tycontext_eqv_symm.
apply join_tycon_same.
eapply semax_pre_simple; [ | apply H2].
apply andp_left2.
apply andp_left2.
rewrite andp_comm. auto.
eapply semax_post_flipped. apply H3.
intros.
apply andp_left2.
unfold normal_ret_assert, loop2_ret_assert.
normalize.
Qed.

Lemma semax_for' : 
 forall Espec Delta P Q R test body incr PreIncr Post,
     bool_type (typeof test) = true ->
     PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (tc_expr Delta test) ->
     PROPx P (LOCALx (tc_environ Delta :: `(typed_false (typeof test)) (eval_expr test) :: Q) (SEPx R)) |-- Post EK_normal None ->
     @semax Espec Delta (PROPx P (LOCALx (`(typed_true (typeof test)) (eval_expr test) :: Q) (SEPx R)))
             body (loop1_ret_assert PreIncr Post) ->
     @semax Espec Delta PreIncr incr (normal_ret_assert (PROPx P (LOCALx Q (SEPx R)))) ->
     @semax Espec Delta (PROPx P (LOCALx Q (SEPx R))) 
       (Sloop (Ssequence (Sifthenelse test Sskip Sbreak) body) incr)
       Post.
Proof.
intros.
apply semax_for with PreIncr; auto.
rewrite insert_local; auto.
rewrite andp_assoc; repeat rewrite insert_local; auto.
rewrite insert_local; auto.
Qed.

Ltac forward_for Inv PreIncr Postcond :=
  first [ignore (Inv: environ->mpred) 
         | fail 1 "Invariant (first argument to forward_while) must have type (environ->mpred)"];
  first [ignore (Postcond: environ->mpred)
         | fail 1 "Postcondition (second argument to forward_while) must have type (environ->mpred)"];
  apply semax_pre with Inv;
    [  unfold_function_derives_right 
    | (apply semax_seq with Postcond;
       [ first 
          [ apply semax_for' with PreIncr
          | apply semax_for with PreIncr
          ]; 
          [ compute; auto 
          | unfold_and_local_derives
          | unfold_and_local_derives
          | unfold_and_local_semax
          | unfold_and_local_semax
          ] 
       | simpl update_tycon 
       ])
    ]; abbreviate_semax; autorewrite with ret_assert.

Lemma final_part4:
 forall (Espec: OracleKind) md c shmd hashedmsg,
 length hashedmsg = 8 ->
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

Definition part4_inv  c shmd hashedmsg md delta i :=
   (PROP  (i <= 8)
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
* apply exp_right with 0. unfold part4_inv; rewrite Z.sub_0_r.
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
 assert (i=8) by omega.
 subst i. change (Z.of_nat 8) with 8%Z.
 entailer!.
  rewrite (firstn_same _ 8) by omega. auto. 
* unfold part4_inv.
 rewrite insert_local.
 match goal with |- semax _ (PROPx _ (LOCALx (_:: ?Q) ?R)) _ _ =>
   apply semax_pre with (PROP (i<8) (LOCALx Q R))
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
 pose (bytes := Basics.compose force_int (ZnthV tuchar (map Vint (map Int.repr (intlist_to_Zlist ([swap w])))))).
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
        (map Vint (map Int.repr (intlist_to_Zlist ([swap w])))) x))
  with 
  (fun x : Z =>
   force_int
     (ZnthV tuchar
        (map Vint (map Int.repr (intlist_to_Zlist (map swap [w])))) 
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

Lemma offset_val_array_at_:
 forall ofs t sh lo hi v,
  array_at_ t sh (ofs + lo) (ofs + hi) v =
  array_at_ t sh lo hi (offset_val (Int.repr (sizeof t * ofs)) v).
Proof.
intros.
unfold array_at_.
etransitivity; [ | apply offset_val_array_at].
f_equal.
Qed.

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
 rewrite Int.add_assoc; f_equal.
 normalize. f_equal. 
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
 replace (Zlength (intlist_to_Zlist hashedmsg)) with 32%Z.
Hint Resolve array_at__array_at : cancel.
 cancel.
 rewrite Zlength_correct; rewrite length_intlist_to_Zlist; rewrite H; reflexivity.
Qed.
