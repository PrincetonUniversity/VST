Require Import floyd.proofauto.
Require Import progs.sha.
Require Import progs.SHA256.
Require Import progs.sha_lemmas.
Require Import progs.spec_sha.
Local Open Scope logic.


Lemma liftSEPlift1:
 forall (R:  mpred) f, 
     `(SEP (`R)) f = `R.
Proof. intros. 
unfold SEPx. 
 super_unfold_lift.
extensionality rho.
simpl. rewrite sepcon_emp.
auto.
Qed.

Definition sha_update_inv sh hashed len c d (frag: list int) data r_Nh r_Nl (done: bool) :=
   (EX blocks:list int,
   PROP  (len >= length blocks*4 - length frag /\
              NPeano.divide LBLOCK (length blocks) /\ 
              intlist_to_Zlist (map swap blocks) = map Int.unsigned frag ++ firstn (length blocks * 4 - length frag) data /\
             if done then len-(length blocks*4 - length frag) < CBLOCK else True)
   LOCAL  (`(eq (offset_val (Int.repr 40) c)) (eval_id _p);
   `(eq c) (eval_id _c); `(eq (offset_val (Int.repr (Z.of_nat (length blocks*4-length frag))) d)) (eval_id _data);
   `(eq (Vint (Int.repr (Z.of_nat (len- (length blocks*4 - length frag)))))) (eval_id _len))
   SEP  (`(array_at tuint Tsh (ZnthV tuint K) 0 (Zlength K)) (eval_var _K256 (tarray tuint 64));
    `(array_at tuint Tsh (ZnthV tuint (process_msg init_registers (hashed ++ blocks))) 0 8 c);
    `(sha256_length (hilo r_Nh r_Nl + Z.of_nat len) c);
   `(array_at_ tuchar Tsh 0 64 (offset_val (Int.repr 40) c));
   `(field_mapsto_ Tsh t_struct_SHA256state_st _num c);
   `(data_block sh data d))).

Lemma Hblocks'lem:
 forall {blocks frag: list int} {data},
 intlist_to_Zlist (map swap blocks) = map Int.unsigned frag ++ firstn (length blocks * 4 - length frag) data ->
 length frag <= length blocks * 4.
Proof.
intros.
assert (length (intlist_to_Zlist (map swap blocks)) = 
               length (   map Int.unsigned frag ++
     firstn (length blocks * 4 - length frag) data)) by congruence.
 rewrite length_intlist_to_Zlist, map_length, app_length in H0.
 rewrite map_length in H0.
 rewrite mult_comm; omega.
Qed.

Lemma Hblocks''lem:
 forall {blocks frag: list int} {data},
 intlist_to_Zlist blocks = map Int.unsigned frag ++ firstn (length blocks * 4 - length frag) data ->
 length frag <= length blocks * 4.
Proof.
intros.
assert (length (intlist_to_Zlist blocks) = 
               length (   map Int.unsigned frag ++
     firstn (length blocks * 4 - length frag) data)) by congruence.
 rewrite length_intlist_to_Zlist, app_length, map_length in H0.
 rewrite mult_comm; omega.
Qed.

Lemma intro_update_inv:
 forall (len: nat) (blocks : list int) (frag: list int) (data: list Z) (P' Q: Prop),
  (forall (Hblocks_len: len >= length blocks * 4 - length frag)
            (Hdiv: NPeano.divide LBLOCK (length blocks))
            (Hblocks: intlist_to_Zlist (map swap blocks) = map Int.unsigned frag ++ firstn (length blocks * 4 - length frag) data)
            (DONE: P')
            (Hblocks': length blocks * 4 >= length frag),
            Q) ->
    (len >= length blocks*4 - length frag /\
    NPeano.divide LBLOCK (length blocks) /\ 
    intlist_to_Zlist (map swap blocks) = map Int.unsigned frag ++ firstn (length blocks * 4 - length frag) data /\
              P' -> Q). 
Proof.
intros.
 destruct H0 as  [Hblocks_len [Hdiv [Hblocks DONE]]].
 apply H; clear H; auto.
 apply Hblocks'lem in Hblocks; auto.
Qed.

Lemma split3_data_block:
  forall lo n sh data d,
  lo+n <= length data ->
  data_block sh data d = 
  data_block sh (firstn lo data) d *
  data_block sh (firstn n (list_drop lo data)) (offset_val (Int.repr (Z.of_nat lo)) d) *
  data_block sh (list_drop (lo+n) data)  (offset_val (Int.repr (Z.of_nat (lo+n))) d).
Admitted.

 Lemma divide_length_app:
 forall {A} n (al bl: list A), 
      NPeano.divide n (length al) -> 
      NPeano.divide n (length bl) ->
      NPeano.divide n (length (al++bl)).
Proof.
 intros. destruct H,H0. exists (x+x0).
 rewrite app_length,H,H0;  rewrite  mult_plus_distr_r; omega.
Qed.

Lemma SHA256_Update_aux:
 forall (Espec : OracleKind) (sh: share) (hashed : list int) (r_data: list int) (data : list Z) (c d : val)
  (len : nat) (r_h : list int) (r_Nl r_Nh : int)
   (Delta : tycontext) (blocks bl : list int)
 (HDelta: Delta = initialized _p (initialized _n (initialized _data
                     (func_tycontext f_SHA256_Update Vprog Gtot))))
 (H: len <= length data)
 (Hdiv: NPeano.divide LBLOCK (length blocks))
 (HBOUND: (s256a_len (S256abs hashed (map Int.unsigned r_data)) < BOUND)%Z)
 (H0: r_h = process_msg init_registers hashed)
 (H1: Zlength (intlist_to_Zlist hashed ++ map Int.unsigned r_data) = hilo r_Nh r_Nl)
 (H4: NPeano.divide LBLOCK (length hashed))
 (Hblocks: intlist_to_Zlist (map swap blocks) = (map Int.unsigned r_data) ++ firstn (length blocks * 4 - length r_data) data)
 (H3 : length (map Int.unsigned r_data) < CBLOCK)
 (Hlen: (Z.of_nat len <= Int.max_unsigned)%Z)
 (Hlen_ge: len - (length blocks * 4 - length r_data) >= CBLOCK)
 (H6: firstn CBLOCK (list_drop (length blocks * 4 - length r_data) data) =
     intlist_to_Zlist (map swap bl))
 (H7: length bl = LBLOCK),
semax Delta
  (PROP  ()
   LOCAL 
   (`(typed_true
        (typeof
           (Ebinop Oge (Etempvar _len tuint)
              (Ebinop Omul (Econst_int (Int.repr 16) tint)
                 (Econst_int (Int.repr 4) tint) tint) tint)))
      (eval_expr
         (Ebinop Oge (Etempvar _len tuint)
            (Ebinop Omul (Econst_int (Int.repr 16) tint)
               (Econst_int (Int.repr 4) tint) tint) tint));
   `(eq (offset_val (Int.repr 40) c)) (eval_id _p); `(eq c) (eval_id _c);
   `(eq
       (offset_val (Int.repr (Z.of_nat (length blocks * 4 - length r_data)))
          d)) (eval_id _data);
   `(eq
       (Vint
          (Int.repr (Z.of_nat (len - (length blocks * 4 - length r_data))))))
     (eval_id _len))
   SEP 
   (`(array_at tuint Tsh (ZnthV tuint K) 0 (Zlength K)) (eval_var _K256 (tarray tuint 64));
    `(array_at tuint Tsh
        (ZnthV tuint (process_msg init_registers (hashed ++ blocks))) 0 8 c);
   `(sha256_length (hilo r_Nh r_Nl + Z.of_nat len) c);
   `(array_at_ tuchar Tsh 0 64 (offset_val (Int.repr 40) c));
   `(field_mapsto_ Tsh t_struct_SHA256state_st _num c);
   `(data_block sh data d)))
  (Ssequence
     (Scall None
        (Evar _sha256_block_data_order
           (Tfunction
              (Tcons (tptr t_struct_SHA256state_st) (Tcons (tptr tvoid) Tnil))
              tvoid))
        [Etempvar _c (tptr t_struct_SHA256state_st),
        Etempvar _data (tptr tuchar)])
     (Ssequence
        (Sset _data
           (Ebinop Oadd (Etempvar _data (tptr tuchar))
              (Ebinop Omul (Econst_int (Int.repr 16) tint)
                 (Econst_int (Int.repr 4) tint) tint) (tptr tuchar)))
        (Sset _len
           (Ebinop Osub (Etempvar _len tuint)
              (Ebinop Omul (Econst_int (Int.repr 16) tint)
                 (Econst_int (Int.repr 4) tint) tint) tuint))))
  (loop1_ret_assert
     (sha_update_inv sh hashed len c d r_data data r_Nh r_Nl false)
     (normal_ret_assert
        (sha_update_inv sh hashed len c d r_data data r_Nh r_Nl true))).
Proof.
intros.
name c' _c.
name data_ _data_.
name len' _len.
name data' _data.
name p _p.
name n _n.
subst Delta; simplify_Delta; abbreviate_semax.
forward. (* sha256_block_data_order (c,data); *)
instantiate (1:=(hashed++ blocks, 
                           bl,
                           c, 
                           offset_val (Int.repr (Z.of_nat (length blocks * 4 - length r_data))) d,
                           sh)) in (Value of witness).
 instantiate (1:= [
   `(sha256_length (hilo r_Nh r_Nl + Z.of_nat len) c),
  `(array_at_ tuchar Tsh 0 64 (offset_val (Int.repr 40) c)),
  `(field_mapsto_ Tsh t_struct_SHA256state_st _num c),
  `(data_block sh (firstn (length blocks * 4 - length r_data)  data) d),
  `(data_block sh (list_drop (length blocks * 4 - length r_data + CBLOCK) data) 
                 (offset_val (Int.repr (Z.of_nat (length blocks * 4 - length r_data + CBLOCK))) d))])
    in (Value of Frame).
 unfold Frame, witness; clear Frame witness.
 cbv beta iota.
entailer!.
rewrite mul_repr in H5; rewrite H5; reflexivity.
apply divide_length_app; auto.
 replace (eval_var _K256 (tarray tuint 64)
         (env_set
            (env_set (globals_only rho) _in
               (offset_val
                  (Int.repr (Z.of_nat (length blocks * 4 - length r_data))) d))
            _ctx c')) with (eval_var _K256 (tarray tuint 64) rho)
 by (repeat rewrite eval_var_env_set; 
      erewrite elim_globals_only by (split3; [eassumption | reflexivity.. ]);
       reflexivity).
 rewrite <- H6.
 rewrite (split3_data_block (length blocks * 4 - length r_data) CBLOCK sh data) by omega.
 cancel.

replace_SEP 0%Z
  (`(array_at tuint Tsh
          (ZnthV tuint
             (process_msg init_registers ((hashed ++ blocks) ++ bl))) 0 8 c) *
      `(data_block sh (intlist_to_Zlist (map swap bl))
          (offset_val
             (Int.repr (Z.of_nat (length blocks * 4 - length r_data))) d)) *
      `(array_at tuint Tsh (ZnthV tuint K) 0 (Zlength K))
        (eval_var _K256 (tarray tuint 64))).
 entailer!.
  erewrite elim_globals_only by (split3; [eassumption | reflexivity.. ]);
  auto.
 normalize.

 forward. (* data += SHA_CBLOCK; *)
 entailer. 
 forward. (* len  -= SHA_CBLOCK; *)
 unfold loop1_ret_assert.
 unfold sha_update_inv.
 apply exp_right with (blocks++ bl).
 entailer.
 clear TC0 TC.
 rewrite negb_true_iff in H8.
 unfold Int.ltu in H8.
 if_tac in H8; inv H8.
 rewrite mul_repr in H0.
 change (Int.unsigned (Int.repr (16 * 4)))%Z with 64%Z in H0.
 rewrite Int.unsigned_repr in H0
  by (clear - Hlen; split; [omega | ];
        rewrite Nat2Z.inj_sub_max;
        apply Z.max_lub; omega).

 assert (Hblocks' := Hblocks'lem Hblocks).
 apply andp_right; [ apply prop_right; repeat split | cancel].
*
 rewrite app_length.
 rewrite  mult_plus_distr_r. 
 rewrite plus_comm.
 rewrite <- NPeano.Nat.add_sub_assoc by (clear - Hblocks'; omega).
 rewrite H7.
 clear - H0.
 rewrite Nat2Z.inj_sub_max in H0.
 rewrite Zmax_spec in H0. if_tac in H0; try omega.
 clear H.
 apply Nat2Z.inj_ge.
 rewrite Nat2Z.inj_add.
 change (Z.of_nat (LBLOCK*4)) with 64%Z. omega.
* rewrite app_length.
 clear - Hdiv H7. rewrite H7. destruct Hdiv as [x ?]; exists (S x).
 simpl; omega.
*
 rewrite map_app; rewrite intlist_to_Zlist_app.
 rewrite Hblocks; rewrite <- H6.
 rewrite app_ass.
 f_equal. rewrite app_length. rewrite H7.
  rewrite  mult_plus_distr_r. change (LBLOCK*4)%nat with CBLOCK.
 rewrite NPeano.Nat.add_sub_swap by auto.
 apply firstn_app.
*
 destruct d; inv Pd; simpl. f_equal.
 rewrite Int.add_assoc. f_equal.
 rewrite mul_repr.
 rewrite app_length.
 rewrite H7.
 rewrite add_repr.
 f_equal.
 rewrite  mult_plus_distr_r.
 change (LBLOCK*4) with CBLOCK.
rewrite NPeano.Nat.add_sub_swap by auto.
 rewrite Nat2Z.inj_add.
 f_equal.
*
 f_equal.
 rewrite app_length. rewrite mult_plus_distr_r. rewrite H7.
 change (16*4)%Z with  (Z.of_nat (LBLOCK*4)).
 symmetry.  rewrite <- Nat2Z.inj_sub by auto.
 f_equal.
 rewrite <- NPeano.Nat.sub_add_distr by auto.
 f_equal.
 rewrite NPeano.Nat.add_sub_swap by auto.
 auto.
*
 rewrite app_ass.
 rewrite (split3_data_block (length blocks * 4 - length r_data) CBLOCK sh data)
  by omega.
 cancel.
apply derives_refl'. f_equal. auto.
Qed.

Lemma Zlength_intlist_to_Zlist_app:
 forall al bl,  Zlength (intlist_to_Zlist (al++bl)) =
    (Zlength (intlist_to_Zlist al) + Zlength (intlist_to_Zlist bl))%Z.
Proof.
Admitted.

Lemma body_SHA256_Update: semax_body Vprog Gtot f_SHA256_Update SHA256_Update_spec.
Proof.
start_function.
name c' _c.
name data_ _data_.
name len' _len.
name data' _data.
name p _p.
name n _n.
name fragment _fragment.
rename H0 into HBOUND.
forward.  (* data=data_; *)

unfold sha256_length, sha256state_.
normalize.
intros [r_h [r_Nl [r_Nh [r_data r_num]]]].
normalize.
unfold s256a_len.
unfold s256_relate in H0.
destruct a as [hashed data0].
simpl_typed_mapsto.
unfold s256_h, s256_Nh,s256_Nl, s256_num, s256_data, fst,snd in H0|-*.
destruct H0 as [? [? [? [? [? ?]]]]].
revert POSTCONDITION; subst data0.
intro.
subst r_h.

forward.  (* SHA256_addlength(c, len); *)
instantiate (1:= (len,c, hilo r_Nh r_Nl)) in (Value of witness).
entailer!.
unfold sha256_length.
normalize; apply exp_right with r_Nl. 
normalize; apply exp_right with r_Nh.
entailer!.
cbv beta iota.
normalize.
(* rewrite elim_globals_only'. *)

forward. (* n = c->num; *)
forward. (* p=c->data; *)
entailer. simpl.
apply semax_pre with
 (PROP  ( (Z.of_nat len <= Int.max_unsigned)%Z)
   LOCAL 
   (`(eq  (offset_val (Int.repr 40) c)) (eval_id _p);
   `(eq (Vint r_num)) (eval_id _n);
   `(eq c) (eval_id _c); `(eq d) (eval_id _data);
   `(eq (Vint (Int.repr (Z.of_nat len)))) (eval_id _len))
   SEP  (`(array_at tuint Tsh (ZnthV tuint (process_msg init_registers hashed)) 0 8 c);
    `(sha256_length (hilo r_Nh r_Nl + Z.of_nat len) c);
   `(array_at tuchar Tsh (ZnthV tuchar r_data) 0 64 (offset_val (Int.repr 40) c));
   `(field_mapsto Tsh t_struct_SHA256state_st _num c (Vint r_num));
   `(array_at tuint Tsh (ZnthV tuint K) 0 (Zlength K))  (eval_var _K256 (tarray tuint 64));
   `(data_block sh data d))).
entailer!.
rewrite H2.
destruct (Int.unsigned_range_2 len'); auto.
rewrite H2; apply Int.repr_unsigned.
apply semax_extract_PROP; intro Hlen.

forward_if (sha_update_inv sh hashed len c d r_data data r_Nh r_Nl false).
* entailer!.   (* cond-expression typechecks *)
* (* then clause *)
forward.  (* fragment = SHA_CBLOCK-n; *)
rewrite semax_seq_skip.
forward_if (sha_update_inv sh hashed len c d r_data data r_Nh r_Nl false).
 + entailer!.  (* cond-expression typechecks *)
    rewrite H2; reflexivity.
 + (* then clause: len >= fragment *)
    admit.
 + (* else clause: len < fragment *)
    admit.
 + forward. (* bogus skip *)
    rewrite overridePost_normal'.
    apply andp_left2; auto.
* (* else clause *)
forward.  (* skip; *)
rewrite overridePost_normal'.
apply exp_right with nil. rewrite <- app_nil_end.
entailer.
 rewrite negb_false_iff in H2;  apply int_eq_e in H2; subst n;
 destruct r_data; inv H5.
 apply andp_right; [apply prop_right; repeat split | ].
 + clear; omega.
 + exists 0; reflexivity.
 +  repeat f_equal; omega.
 + rewrite <- app_nil_end. cancel.
* (* after if (n!=0) *)
eapply semax_seq' with
     (sha_update_inv sh hashed len c d r_data data r_Nh r_Nl true).
apply semax_while.
+ reflexivity.
+ entailer!.
+ rewrite normal_ret_assert_elim.
  unfold sha_update_inv.
  normalize.
  rewrite andp_assoc; do 2 rewrite insert_local.
  apply exp_right with blocks.
  entailer.
  rename H7 into Hblocks;  assert (Hblocks' := Hblocks'lem Hblocks).
  apply prop_right.
  change (Int.mul (Int.repr 16) (Int.repr 4)) with (Int.repr 64) in H8;
  rewrite negb_false_iff in H8;
  apply Int.ltu_inv in H8.  
  rewrite Int.unsigned_repr in H8.
  destruct H8 as [_ H8].
  apply Nat2Z.inj_lt.
 apply H8.
  split; [ clear; omega | ].
  rewrite Nat2Z.inj_sub by auto. omega.
+ unfold LOOP_BODY, abbreviate; clear LOOP_BODY MORE_COMMANDS POSTCONDITION.
  unfold sha_update_inv at 1.
  normalize.
  apply extract_exists_pre; intro blocks.
  rewrite insert_local.
  apply semax_extract_PROP; apply intro_update_inv; intros.
 match goal with |- semax _ (PROPx _ ?QR) _ _ =>
 apply semax_pre with (PROP (len - (length blocks*4 - length r_data) >= CBLOCK) QR)
 end.
 {entailer.
  rewrite mul_repr in H2; rewrite H2. 
  apply prop_right; split; [ | reflexivity].
  rewrite negb_true_iff in H2;
   unfold Int.ltu in H2;
  if_tac in H2; inv H2.
  rewrite Int.unsigned_repr in H6;
  change (Int.unsigned (Int.mul (Int.repr 16) (Int.repr 4)))
    with (Z.of_nat CBLOCK) in H6.
  apply Nat2Z.inj_ge.
 apply H6.
  split; [clear; omega | ].
  rewrite Nat2Z.inj_sub by auto.
  omega.
}

Lemma exists_intlist_to_Zlist':
  forall n (al: list Z), 
   length al = (n * 4)%nat ->
   exists bl, al = intlist_to_Zlist (map swap bl) /\ length bl = n.
Admitted.

  apply semax_extract_PROP; intro Hlen_ge.
  destruct (exists_intlist_to_Zlist' LBLOCK (firstn CBLOCK (list_drop (length blocks*4 - length r_data) data)))
      as [bl [? ?]].
  rewrite firstn_length.
  rewrite min_l; [reflexivity |].
 rewrite list_drop_length.
  transitivity (len - (length blocks*4 - length r_data)); [ | clear - H; omega].
  apply Hlen_ge.
  clear - Hlen_ge H H3 H5 ; omega.
 simple apply (SHA256_Update_aux Espec sh hashed r_data data c d len (process_msg init_registers hashed) r_Nl r_Nh Delta blocks bl); 
   try assumption.
simplify_Delta; reflexivity.
reflexivity.
+
  abbreviate_semax.
  unfold sha_update_inv.   apply extract_exists_pre; intro blocks.
  apply semax_extract_PROP; apply intro_update_inv; intros.
  forward.    (* c->num=len; *)
  forward_if  (EX  a' : s256abs,
                    PROP  (update_abs (firstn len data) (S256abs hashed (map Int.unsigned r_data)) a')
                    LOCAL ()
                    SEP 
                    (`(array_at tuint Tsh (ZnthV tuint K) 0 (Zlength K))
                       (eval_var _K256 (tarray tuint 64));
                    `(sha256state_ a' c); `(data_block sh data d))).
 entailer.
 admit.  (* then-clause *)
 forward. (* else-clause *)
 normalize.
 rewrite overridePost_normal'.
 apply exp_right 
   with (S256abs (hashed++blocks) nil).
 entailer.
 rewrite negb_false_iff in H2; apply int_eq_e in H2.
 assert (H2': Int.unsigned (Int.repr (Z.of_nat (len - (length blocks * 4 - length r_data)))) = 
              Int.unsigned Int.zero) by (f_equal; apply H2).
 rewrite Int.unsigned_zero in H2'.
 rewrite Int.unsigned_repr in H2'
 by (split; [clear; omega | rewrite Nat2Z.inj_sub by auto; clear - Hlen; omega]).
 assert (H7: len = length blocks * 4 - length r_data).
   rewrite Nat2Z.inj_sub in H2' by auto.
    apply Nat2Z.inj. clear - H2'; omega.
 apply andp_right.
 apply prop_right.
 constructor; auto.
 change CBLOCK with 64; simpl; clear; omega.
 rewrite <- app_nil_end.
 rewrite Hblocks.
 rewrite <- H7.
 reflexivity.
 unfold sha256state_.
 cancel.
 unfold sha256_length.
 normalize.
 apply exp_right with 
              (process_msg init_registers (hashed ++ blocks),
                (lo, (hi, (nil, 
                 Int.zero)))).
 simpl_typed_mapsto; unfold s256_relate.
unfold s256_h, s256_Nh,s256_Nl, s256_num, s256_data, fst,snd.
 apply andp_right; [apply prop_right | cancel].
 repeat split; simpl; auto.
 rewrite <- app_nil_end.
 rewrite Zlength_intlist_to_Zlist_app.
 replace (Zlength (intlist_to_Zlist blocks)) with
    (Zlength (intlist_to_Zlist (map swap blocks)))
 by (repeat rewrite Zlength_correct, length_intlist_to_Zlist; rewrite map_length; reflexivity).
 rewrite Hblocks.
 rewrite H6.
 rewrite H7.
 rewrite Nat2Z.inj_sub by auto.
 rewrite (Zlength_correct (_ ++ _)).
 rewrite app_length. rewrite map_length. rewrite Nat2Z.inj_add.
 rewrite <- H1.
 repeat rewrite Zlength_correct; rewrite app_length; rewrite map_length.
 rewrite firstn_length.
 rewrite min_l.  rewrite Nat2Z.inj_add.
 rewrite Nat2Z.inj_sub by auto.
 clear; omega.
 omega.
 change CBLOCK with 64; clear; omega.
 apply divide_length_app; auto.
 rewrite H2'.
 cancel.
 apply extract_exists_pre; intro a'.
 forward.
 apply exp_right with a'.
 erewrite elim_globals_only by (split3; [eassumption | reflexivity.. ]) .
           (* should try to automate the line above *)
 entailer!.
Qed.
