Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Local Open Scope nat.
Local Open Scope logic.


Lemma cVint_force_int_ZnthV:
 forall sh contents hi, 
  (hi <= Zlength contents)%Z ->
  array_at tuchar sh (cVint (force_int oo ZnthV tuchar (map Vint contents))) 0 hi = 
  array_at tuchar sh (ZnthV tuchar (map Vint contents)) 0 hi.
Proof.
unfold ZnthV; simpl.
intros.
apply array_at_ext; intros.
unfold cVint,Basics.compose.
if_tac. omega.
assert (Z.to_nat i < length contents).
apply Nat2Z.inj_lt.
rewrite <- Zlength_correct; rewrite Z2Nat.id by omega.
omega.
clear - H2; revert contents H2; induction (Z.to_nat i); intros; destruct contents; 
simpl in *; try omega; auto.
apply IHn. omega.
Qed.

Definition update_inner_if :=
              (Sifthenelse (Ebinop Oge (Etempvar _len tuint)
                             (Etempvar _fragment tuint) tint)
                (Ssequence
                  (Ssequence
                    (Scall (Some _ignore')
                      (Evar _memcpy (Tfunction
                                      (Tcons (tptr tvoid)
                                        (Tcons (tptr tvoid)
                                          (Tcons tuint Tnil))) (tptr tvoid)))
                      ((Ebinop Oadd (Etempvar _p (tptr tuchar))
                         (Etempvar _n tuint) (tptr tuchar)) ::
                       (Etempvar _data (tptr tuchar)) ::
                       (Etempvar _fragment tuint) :: nil))
                    (Sset _ignore (Etempvar _ignore' (tptr tvoid))))
                  (Ssequence
                    (Scall None
                      (Evar _sha256_block_data_order (Tfunction
                                                       (Tcons
                                                         (tptr t_struct_SHA256state_st)
                                                         (Tcons (tptr tvoid)
                                                           Tnil)) tvoid))
                      ((Etempvar _c (tptr t_struct_SHA256state_st)) ::
                       (Etempvar _p (tptr tuchar)) :: nil))
                    (Ssequence
                      (Sset _data
                        (Ebinop Oadd (Etempvar _data (tptr tuchar))
                          (Etempvar _fragment tuint) (tptr tuchar)))
                      (Ssequence
                        (Sset _len
                          (Ebinop Osub (Etempvar _len tuint)
                            (Etempvar _fragment tuint) tuint))
                        (Ssequence
                          (Scall (Some _ignore'1)
                            (Evar _memset (Tfunction
                                            (Tcons (tptr tvoid)
                                              (Tcons tint (Tcons tuint Tnil)))
                                            (tptr tvoid)))
                            ((Etempvar _p (tptr tuchar)) ::
                             (Econst_int (Int.repr 0) tint) ::
                             (Ebinop Omul (Econst_int (Int.repr 16) tint)
                               (Econst_int (Int.repr 4) tint) tint) :: nil))
                          (Sset _ignore (Etempvar _ignore'1 (tptr tvoid))))))))
                (Ssequence
                  (Ssequence
                    (Scall (Some _ignore'2)
                      (Evar _memcpy (Tfunction
                                      (Tcons (tptr tvoid)
                                        (Tcons (tptr tvoid)
                                          (Tcons tuint Tnil))) (tptr tvoid)))
                      ((Ebinop Oadd (Etempvar _p (tptr tuchar))
                         (Etempvar _n tuint) (tptr tuchar)) ::
                       (Etempvar _data (tptr tuchar)) ::
                       (Etempvar _len tuint) :: nil))
                    (Sset _ignore (Etempvar _ignore'2 (tptr tvoid))))
                  (Ssequence
                    (Sassign
                      (Efield
                        (Ederef (Etempvar _c (tptr t_struct_SHA256state_st))
                          t_struct_SHA256state_st) _num tuint)
                      (Ebinop Oadd (Etempvar _n tuint)
                        (Ecast (Etempvar _len tuint) tuint) tuint))
                    (Sreturn None)))).

Definition inv_at_inner_if sh hashed len c d dd data hi lo:=
 (PROP ()
   (LOCAL 
   (`(eq (Vint (Int.repr (64- Zlength dd)))) (eval_id _fragment);
   `(eq  (offset_val (Int.repr 40) c)) (eval_id _p);
   `(eq (Vint (Int.repr (Zlength dd)))) (eval_id _n);
   `(eq c) (eval_id _c); `(eq d) (eval_id _data);
   `(eq (Vint (Int.repr (Z.of_nat len)))) (eval_id _len))
   SEP  (`(array_at tuint Tsh (tuints (process_msg init_registers hashed)) 0 8 c);
    `(sha256_length (hilo hi lo + (Z.of_nat len)*8) c);
   `(array_at tuchar Tsh (ZnthV tuchar (map Vint (map Int.repr dd))) 0 64 (offset_val (Int.repr 40) c));
   `(field_at Tsh t_struct_SHA256state_st _num (Vint (Int.repr (Zlength dd))) c);
   K_vector;
   `(data_block sh data d)))).

Definition sha_update_inv sh hashed len c d (frag: list Z) (data: list Z) r_Nh r_Nl (done: bool) :=
   (EX blocks:list int,
   PROP  (len >= length blocks*4 - length frag /\
              NPeano.divide LBLOCK (length blocks) /\ 
              intlist_to_Zlist blocks = frag ++ firstn (length blocks * 4 - length frag) data /\
             if done then len-(length blocks*4 - length frag) < CBLOCK else True)
   LOCAL  (`(eq (offset_val (Int.repr 40) c)) (eval_id _p);
   `(eq c) (eval_id _c); `(eq (offset_val (Int.repr (Z.of_nat (length blocks*4-length frag))) d)) (eval_id _data);
   `(eq (Vint (Int.repr (Z.of_nat (len- (length blocks*4 - length frag)))))) (eval_id _len))
   SEP  (K_vector;
    `(array_at tuint Tsh (tuints (process_msg init_registers (hashed ++ blocks))) 0 8 c);
    `(sha256_length (hilo r_Nh r_Nl + (Z.of_nat len)*8) c);
   `(array_at_ tuchar Tsh 0 64 (offset_val (Int.repr 40) c));
   `(field_at_ Tsh t_struct_SHA256state_st _num c);
   `(data_block sh data d))).

Lemma update_inner_if_proof:
 forall (Espec: OracleKind) (hashed: list int) (dd data: list Z)
            (c d: val) (sh: share) (len: nat) (hi lo: int)
 (H: len <= length data)
 (H7 : ((Zlength hashed * 4 + Zlength dd) * 8)%Z = hilo hi lo)
 (H3 : length dd < CBLOCK)
 (H3' : Forall isbyteZ dd)
 (H4 : NPeano.divide LBLOCK (length hashed))
 (Hlen : (Z.of_nat len <= Int.max_unsigned)%Z),
semax
  (initialized _fragment  (initialized _p
     (initialized _n
        (initialized _data (func_tycontext f_SHA256_Update Vprog Gtot)))))
  (inv_at_inner_if sh hashed len c d dd data hi lo)
  update_inner_if
  (overridePost (sha_update_inv sh hashed len c d dd data hi lo false)
     (function_body_ret_assert tvoid
        (EX  a' : s256abs,
         PROP  (update_abs (firstn len data) (S256abs hashed dd) a')
         LOCAL ()
         SEP  (K_vector; `(sha256state_ a' c); `(data_block sh data d))))).
Proof.
intros.
name c' _c.
name data_ _data_.
name len' _len.
name data' _data.
name p _p.
name n _n.
name fragment_ _fragment.
simplify_Delta.
unfold sha_update_inv, inv_at_inner_if, update_inner_if.
abbreviate_semax.
rewrite semax_seq_skip.
 set (j := (40 + Zlength dd)%Z).
 set (k := (64-Zlength dd)%Z).
assert (0 < k <= 64)%Z
 by (unfold k; clear - H3;
     apply Nat2Z.inj_lt in H3; rewrite Zlength_correct;
    change (Z.of_nat CBLOCK) with 64%Z in *;
    omega).
 assert (64 < Int.max_unsigned)%Z
  by (compute; reflexivity).
apply Nat2Z.inj_le in H; rewrite <- Zlength_correct in H.
unfold data_block; simpl. normalize.
rename H2 into DBYTES.
forward_if (sha_update_inv sh hashed len c d dd data hi lo false).
 + entailer!.  (* cond-expression typechecks *)
 + (* then clause: len >= fragment *)
  simpl typeof.
  unfold K_vector.
  apply (remember_value (eval_id _fragment)); intro fragment.
  forward. (* ignore = memcpy (p+n,data,fragment); *)
  simpl split. simpl @snd.
  instantiate (1:=((sh,Tsh), 
                           offset_val (Int.repr (Zlength dd)) (offset_val (Int.repr 40) c),
                           d, 
                           Int.unsigned (force_int fragment),
                           Basics.compose force_int (ZnthV tuchar (map Vint (map Int.repr data)))))
        in (Value of witness).
  unfold witness. 
 normalize.
 fold j; fold k.
 entailer!.
 rewrite H6; reflexivity.
 clear POSTCONDITION MORE_COMMANDS.
 unfold witness in *; clear witness. clear fragment H5.
 rewrite negb_true_iff in H6. 
 apply ltu_repr_false in H6; [ | repable_signed | omega].
 clear TC TC1 TC0.
 unfold j,k in *; clear j k.
rewrite cVint_force_int_ZnthV
 by (rewrite initial_world.Zlength_map; omega).
 rewrite memory_block_array_tuchar by omega.
 rewrite (split_array_at (Zlength dd) _ _ (ZnthV tuchar (map Vint (map Int.repr dd))))
    by omega.
 rewrite (split_array_at (64-Zlength dd) _ _ (tuchars (map Int.repr data)))
    by omega.
 replace (offset_val (Int.repr (40 + Zlength dd)) c)
          with (offset_val (Int.repr (sizeof tuchar * Zlength dd)) (offset_val (Int.repr 40) c))
  by (change (sizeof tuchar) with 1%Z; rewrite Z.mul_1_l; rewrite offset_offset_val, add_repr; auto).
rewrite <- offset_val_array_at_.
  rewrite Z.add_0_r.
  replace (Zlength dd + (64-Zlength dd))%Z with 64%Z by omega.
 cancel.
 cbv beta iota.
 autorewrite with norm subst.
 forward. (* finish the call *)
 admit.
 + (* else clause: len < fragment *)
   simpl typeof; unfold K_vector.
   forward. (* ignore'2 := memcpy (p+n, data, len); *)
  simpl split. simpl @snd.
  instantiate (1:=((sh,Tsh), 
                           offset_val (Int.repr (Zlength dd)) (offset_val (Int.repr 40) c),
                           d, 
                           Z.of_nat len,
                           Basics.compose force_int (ZnthV tuchar (map Vint (map Int.repr data)))))
        in (Value of witness).
  unfold witness. 
 normalize.
 clear POSTCONDITION MORE_COMMANDS.
 fold j; fold k.
 entailer!.
 rewrite H5; reflexivity.
 rewrite cVint_force_int_ZnthV
 by (rewrite initial_world.Zlength_map; omega).
 rewrite negb_false_iff in H5.
 apply ltu_repr in H5; [ | repable_signed | omega].
 unfold j,k in *; clear j k.
 replace (offset_val (Int.repr (40 + Zlength dd)) c)
          with (offset_val (Int.repr (sizeof tuchar * Zlength dd)) (offset_val (Int.repr 40) c))
  by (change (sizeof tuchar) with 1%Z; rewrite Z.mul_1_l; rewrite offset_offset_val, add_repr; auto).

 rewrite memory_block_array_tuchar';  [ | destruct c; try contradiction Pc; apply I | omega].
 rewrite <- offset_val_array_at_.
  rewrite Z.add_0_r.
 unfold tuchars.
 rewrite (split_array_at (Zlength dd) _ _ (ZnthV tuchar (map Vint (map Int.repr dd))))
    by omega.
 rewrite (split_array_at (Zlength dd + Z.of_nat len) _ _ (ZnthV tuchar (map Vint (map Int.repr dd)))
                              (Zlength dd))
    by omega.
 rewrite (split_array_at (Z.of_nat len) _ _ (tuchars (map Int.repr data)))
    by omega.
 unfold tuchars.
 cancel.
 cbv beta iota.
 autorewrite with norm subst.
 forward. (* finish the call *)
 forward. (* c->num = n+(unsigned int)len; *)
 fold j; fold k.
 forward. (* return; *)
 apply exp_right with (S256abs hashed (dd ++ firstn len data)).
 unfold id.
 unfold data_block.
 unfold K_vector.
 repeat rewrite TT_andp.
 rewrite cVint_force_int_ZnthV
 by (rewrite initial_world.Zlength_map; omega).
rewrite array_at_tuchar_isbyteZ. 
 rewrite (prop_true_andp (Forall _ data)) by auto.
 rewrite negb_false_iff in H5.
 apply ltu_repr in H5; [ | repable_signed | omega].
 clear TC1 TC TC3 TC2 TC0.
 unfold k in H0,H5.
 rewrite (prop_true_andp (_ /\ _)).
Focus 2. {
 split; auto.
 rewrite (app_nil_end hashed) at 2.
 apply (Update_abs _ hashed nil dd (dd++firstn len data)); auto.
 rewrite app_length. rewrite firstn_length. rewrite min_l.
 apply Nat2Z.inj_lt. rewrite Nat2Z.inj_add.
 rewrite <- Zlength_correct. change (Z.of_nat CBLOCK) with 64%Z.
 omega.
 apply Nat2Z.inj_le; rewrite <- Zlength_correct; assumption.
 exists 0. reflexivity.
} Unfocus.
 unfold sha256state_.
 normalize. clear H8.
 admit. (* getting there *)
 + forward. (* bogus skip *)
    rewrite overridePost_normal'.
    apply andp_left2; auto.
Qed.
