Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.verif_sha_update2.
Require Import sha.verif_sha_update3.
Require Import sha.verif_sha_update4.
Local Open Scope nat.
Local Open Scope logic.

Definition update_last_if :=
  (Sifthenelse (Ebinop One (Etempvar _len tuint)
                               (Econst_int (Int.repr 0) tint) tint)
                  (Scall None
                    (Evar _memcpy (Tfunction
                                    (Tcons (tptr tvoid)
                                      (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                                    (tptr tvoid) cc_default))
                    ((Etempvar _p (tptr tuchar)) ::
                     (Etempvar _data (tptr tuchar)) ::
                     (Etempvar _len tuint) :: nil))
                  Sskip).


Lemma replace_SEP'':
 forall n R' P Q Rs Post,
 (PROPx P (LOCALx Q (SEPx (my_nth n Rs TT ::  nil)))) |-- R' ->
 PROPx P (LOCALx Q (SEPx (replace_nth n Rs R'))) |-- Post ->
 PROPx P (LOCALx Q (SEPx Rs)) |-- Post.
Proof.
intros.
eapply derives_trans; [ | apply H0].
clear - H.
unfold PROPx, LOCALx, SEPx in *; intro rho; specialize (H rho).
unfold local, lift1 in *.
simpl in *; unfold_lift; unfold_lift in H.
normalize.
rewrite prop_true_andp in H by auto.
rewrite prop_true_andp in H by auto.
clear - H.
rewrite sepcon_emp in H.
revert Rs H; induction n; destruct Rs; simpl ; intros; auto;
apply sepcon_derives; auto.
Qed.

Ltac replace_SEP n R :=
  first [apply (replace_SEP' (nat_of_Z n) R) | apply (replace_SEP'' (nat_of_Z n) R)];
  unfold my_nth,replace_nth; simpl nat_of_Z;
   repeat simpl_nat_of_P; cbv beta iota; cbv beta iota.

Lemma update_last_if_proof:
 forall  (Espec : OracleKind) (hashed : list int) 
           (dd data : list Z) (c d : val) (sh : share) (len : nat) kv
   (H : len <= length data)
   (HBOUND : (s256a_len (S256abs hashed dd) + Z.of_nat len * 8 < two_p 64)%Z)
   (c' : name _c)
   (data_ : name _data_)
   (len' : name _len)
   (data' : name _data)
   (p : name _p)
   (n : name _n)
   (fragment : name _fragment)
   (bitlen : Z)
   (H7 : ((Zlength hashed * 4 + Zlength dd) * 8)%Z = bitlen)
   (H3 : (Zlength dd < CBLOCKz)%Z)
   (H3' : Forall isbyteZ dd) 
   (H4 : (LBLOCKz | Zlength hashed)%Z)
   (Hlen : (Z.of_nat len <= Int.max_unsigned)%Z)
   (blocks : list int)
   (Hblocks_len : len >= length blocks * 4 - length dd)
   (Hdiv : (LBLOCKz | Zlength blocks)) 
   (Hblocks : intlist_to_Zlist blocks =
          dd ++ firstn (length blocks * 4 - length dd) data)
   (DONE : len - (length blocks * 4 - length dd) < CBLOCK) 
   (Hblocks' : length blocks * 4 >= length dd),
semax
  (initialized _p
     (initialized _n
        (initialized _data (func_tycontext f_SHA256_Update Vprog Gtot))))
  (PROP  ()
   LOCAL  (temp _p (offset_val (Int.repr 40) c); temp _c c;
                temp _data (offset_val (Int.repr (Z.of_nat (length blocks * 4 - length dd))) d);
                temp _len (Vint (Int.repr (Z.of_nat (len - (length blocks * 4 - length dd)))));
                var  _K256 (tarray tuint CBLOCKz) kv)
   SEP  (`(K_vector kv);
           `(data_at Tsh t_struct_SHA256state_st
                 (map Vint (hash_blocks init_registers (hashed++blocks)),
                  (Vint (lo_part (bitlen + (Z.of_nat len)*8)),
                   (Vint (hi_part (bitlen + (Z.of_nat len)*8)),
                    (nil, 
                     Vint (Int.repr (Z.of_nat (len - (length blocks * 4 - length dd))))))))
                c);
            `(data_block sh data d)))
  update_last_if
  (normal_ret_assert
     (EX  a' : s256abs,
      PROP  (update_abs (firstn len data) (S256abs hashed dd) a')
      LOCAL (var  _K256 (tarray tuint CBLOCKz) kv)
      SEP  (`(K_vector kv);
             `(sha256state_ a' c); `(data_block sh data d)))).
Proof.
  intros.
  unfold update_last_if; simplify_Delta; abbreviate_semax.
  forward_if'.
  + (* then-clause *)
    assert_PROP (Z.of_nat (len - (length blocks * 4 - length dd)) <> 0)%Z. {
      entailer!.
      intro Hz; rewrite Hz in H1; clear Hz. inv H1.
    } drop_LOCAL 0.
    unfold data_block; simpl; normalize.
    rename H0 into Dbytes.
    set (b4d := length blocks * 4 - length dd) in *.
 set (dd' := firstn (len - b4d) (skipn b4d data)).
   assert (H2: Z.of_nat (len-b4d) = Zlength dd'). {
     unfold dd'.
     rewrite Zlength_correct, firstn_length, min_l.
     reflexivity.
     rewrite skipn_length.
     apply minus_le_compat_r.
     omega. omega.
    }
eapply semax_post_flipped3.
evar (Frame: list (LiftEnviron mpred)).
  eapply(call_memcpy_tuchar
   (*dst*) Tsh t_struct_SHA256state_st [StructField _data] 0 nil c
   (*src*) sh (tarray tuchar (Zlength data)) [] (Z.of_nat b4d)
                   (map Int.repr data)
                   d
   (*len*) (Z.of_nat (len - b4d))
        Frame);
   [ auto | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | ].
  unfold_data_at 1. entailer!.
  simpl update_tycon; rewrite insert_local.
  replace_SEP 6%Z (`(K_vector kv)). entailer!.  (* Shouldn't need this *)
  
 apply exp_right with (S256abs (hashed++blocks) dd').
 entailer!.
* clear TC1 TC.
 apply Update_abs; auto.
 rewrite <- H2; change CBLOCKz with (Z.of_nat CBLOCK);
  apply Nat2Z.inj_lt; assumption.
 rewrite Hblocks.
 repeat rewrite app_ass.
 f_equal.
 unfold dd'; rewrite firstn_app.
 f_equal.
 clear - Hblocks_len; omega.
*
 unfold data_block.
 rewrite prop_true_andp by auto.
 clear POSTCONDITION H0 rho.
 (***)
 unfold sha256state_.
 normalize.
 rewrite splice_into_list_simplify2;
  [
  | reflexivity | omega
  |  rewrite Nat2Z.id, Zlength_correct;
     rewrite skipn_length by (repeat rewrite map_length; omega);
    repeat rewrite map_length; rewrite Z.sub_0_r; apply Nat2Z.inj_le; omega
  ].
 simpl app at 1. rewrite Z.sub_0_r, Nat2Z.id, Nat2Z.id.
 apply exp_right with 
              (map Vint (hash_blocks init_registers (hashed ++ blocks)),
                (Vint (lo_part ((Zlength hashed * 4 + Zlength dd) * 8 + Z.of_nat len * 8)),
                 (Vint (hi_part ((Zlength hashed * 4 + Zlength dd) * 8 + Z.of_nat len * 8)),
                  (map Vint (map Int.repr dd'), Vint (Int.repr (Zlength dd')))))).
 entailer!.
 -
    unfold s256_relate; repeat split; auto.
    exists (hi_part ((Zlength hashed * 4 + Zlength dd) * 8 + Z.of_nat len * 8)),
              (lo_part ((Zlength hashed * 4 + Zlength dd) * 8 + Z.of_nat len * 8)).
    repeat split; auto.
    rewrite hilo_lemma2.
    rewrite <- Z.mul_add_distr_r. f_equal. rewrite Zlength_app.
    rewrite Z.mul_add_distr_r.
    repeat rewrite <- Z.add_assoc. f_equal.
    unfold dd'; rewrite (Zlength_correct (firstn _ _)).
    rewrite firstn_length.
    rewrite skipn_length by omega.
    rewrite min_l  by omega.
    rewrite Nat2Z.inj_sub by omega.
    unfold b4d.
   rewrite Nat2Z.inj_sub by omega.
   rewrite Nat2Z.inj_mul. 
   repeat rewrite <- Zlength_correct. change (Z.of_nat 4) with WORD.
   clear; omega.
   
   split; [ | assumption]. rewrite <- Z.mul_add_distr_r.
   apply Z.mul_nonneg_nonneg; try computable.
   apply Z.add_nonneg_nonneg.
   apply Z.add_nonneg_nonneg.
   apply Z.mul_nonneg_nonneg; try computable.
   apply Zlength_nonneg.
   apply Zlength_nonneg.
   clear; omega.

   rewrite <- H2. 
   change CBLOCKz with (Z.of_nat CBLOCK);
   apply Nat2Z.inj_lt; auto.

  unfold dd'; apply Forall_firstn; apply Forall_skipn; auto.
  apply divide_length_app; auto.
 -
   rewrite <- H2.
   unfold_data_at 1. entailer!.
   apply derives_refl'; f_equal.
   unfold dd'.
   repeat rewrite skipn_map. repeat rewrite firstn_map. auto.
+ (* else-clause *)
 forward. 
 normalize.
 apply exp_right with (S256abs (hashed++blocks) nil).
 entailer.
 rewrite negb_false_iff in H1; apply int_eq_e in H1.
 assert (H2': Int.unsigned (Int.repr (Z.of_nat (len - (length blocks * 4 - length dd)))) = 
              Int.unsigned Int.zero) by (f_equal; apply H1).
 rewrite Int.unsigned_zero in H2'.
 rewrite Int.unsigned_repr in H2'
 by (split; [clear; omega | rewrite Nat2Z.inj_sub by auto; clear - Hlen; omega]).
 assert (H7': len - (length blocks * 4 - length dd) = 0).
   apply Nat2Z.inj. rewrite H2'. reflexivity.
 rewrite H7'. change (Z.of_nat 0) with 0%Z.
 entailer!.
 constructor; auto.
 rewrite <- app_nil_end.
 rewrite Hblocks. f_equal. f_equal. clear - Hblocks_len H7'; omega.
 unfold sha256state_.
 set (bitlen := ((Zlength hashed * 4 + Zlength dd) * 8 + Z.of_nat len * 8)%Z).
 
 apply exp_right with 
              (map Vint (hash_blocks init_registers (hashed ++ blocks)),
                (Vint (lo_part bitlen), 
                 (Vint (hi_part bitlen),
                  (nil, Vint Int.zero)))).
 entailer!.
 unfold s256_relate.
 unfold s256_h, s256_Nh,s256_Nl, s256_num, s256_data, fst,snd.
 repeat split; simpl; auto.
 do 2 econstructor; repeat split; try reflexivity.
 rewrite hilo_lemma2. rewrite Zlength_nil, Z.add_0_r.
 unfold bitlen; clear bitlen.
 rewrite Zlength_app.
 rewrite <- (Z.mul_add_distr_r _ _ 8). f_equal.
 rewrite Z.mul_add_distr_r.
 rewrite <- Z.add_assoc. f_equal.
 replace len with (length blocks * 4 - length dd) by (clear - Hblocks_len H7'; omega).
  rewrite Nat2Z.inj_sub by (clear - Hblocks'; omega).
 rewrite Nat2Z.inj_mul. change (Z.of_nat 4) with 4%Z.
 rewrite (Zlength_correct blocks), (Zlength_correct dd).
 change WORD with 4%Z; clear; omega.

 unfold bitlen; simpl in HBOUND. split; [ | assumption].
   apply Z.add_nonneg_nonneg.
   apply Z.mul_nonneg_nonneg; try computable.
   apply Z.add_nonneg_nonneg.
   apply Z.mul_nonneg_nonneg; try computable.
   apply Zlength_nonneg.
   apply Zlength_nonneg.
   apply Z.mul_nonneg_nonneg; try computable.
   clear; omega.

 apply divide_length_app; auto.
Qed.

Lemma hilo_lo:
  forall hi lo, lo_part (hilo hi lo) = lo.
Proof.
intros.
unfold lo_part, hilo; simpl.
apply Int.eqm_repr_eq. econstructor; reflexivity.
Qed.

Lemma hilo_hi:
  forall hi lo, hi_part (hilo hi lo) = hi.
Proof.
intros.
unfold hi_part, hilo; simpl.
rewrite Z.div_add_l by (compute; congruence).
rewrite Z.div_small by apply Int.unsigned_range.
rewrite Z.add_0_r. apply Int.repr_unsigned.
Qed.

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
rename H0 into HBOUND'.
rename H1 into HBOUND.

fold update_inner_if_then in *.
fold update_inner_if_else in *.
fold update_inner_if in *.
fold sha_update_loop_body in *.
forward.  (* data=data_; *)
fold (temp _data d).  (* shouldn't be necessary *)
assert (LEN: (0 <= s256a_len a)%Z). {
 destruct a; simpl.
 apply Z.mul_nonneg_nonneg; try computable.
 apply Z.add_nonneg_nonneg.
 apply Z.mul_nonneg_nonneg; try computable.
 apply Zlength_nonneg.
 apply Zlength_nonneg.
}
unfold sha256state_. normalize.
intros [r_h [lo' [hi' [r_data r_num]]]].
normalize.
unfold s256_relate in H0.
destruct a as [hashed dd].
unfold s256_h, s256_Nh,s256_Nl, s256_num, s256_data, fst,snd in H0|-*.
destruct H0 as [H0 [H1 [H8 [[H3 H3'] [H4 H5]]]]].
destruct H1 as [hi [lo [H1 [H6 H7]]]].
subst.
unfold_data_at 1%nat.
simpl in LEN.

forward_call  (* SHA256_addlength(c, len); *)
  (len, c, s256a_len (S256abs hashed dd)).
unfold s256a_len.
rewrite H7, hilo_hi, hilo_lo.
entailer!.
rewrite <- H7. apply HBOUND.

after_call.
cbv beta iota. normalize.
forward. (* n = c->num; *)
forward. (* p=c->data; *)
entailer. 
simpl.
replace Delta with (initialized _p (initialized _n (initialized _data
                     (func_tycontext f_SHA256_Update Vprog Gtot))))
 by (simplify_Delta; reflexivity).
fold update_outer_if.
apply semax_seq with (sha_update_inv sh hashed (Z.to_nat len) c d dd data kv (hilo hi lo) false).
unfold POSTCONDITION, abbreviate.
eapply semax_pre; [ | simple apply update_outer_if_proof; try assumption].
rewrite <- H7.
unfold_data_at 1%nat.
entailer!. f_equal. apply Z2Nat.id. omega. rewrite Z2Nat.id by omega; auto.
rewrite <- ZtoNat_Zlength. apply Z2Nat.inj_le; auto; omega.
rewrite Z2Nat.id by omega; auto.
rewrite Z2Nat.id by omega; omega.
(* after if (n!=0) *)
eapply semax_seq' with
     (sha_update_inv sh hashed (Z.to_nat len) c d dd data kv (hilo hi lo) true).
clear POSTCONDITION MORE_COMMANDS Delta.
simple apply update_while_proof; try assumption.
rewrite <- ZtoNat_Zlength. apply Z2Nat.inj_le; auto; omega.
rewrite Z2Nat.id by omega; auto.
rewrite Z2Nat.id by omega; omega.
simplify_Delta; abbreviate_semax.
unfold sha_update_inv.   apply extract_exists_pre; intro blocks.
apply semax_extract_PROP; apply intro_update_inv; intros.
forward.    (* c->num=len; *)

apply semax_seq with (EX  a' : s256abs,
                    PROP  (update_abs (firstn (Z.to_nat len) data) (S256abs hashed dd) a')
                    LOCAL (var  _K256 (tarray tuint CBLOCKz) kv)
                    SEP 
                    (`(K_vector kv);
                     `(sha256state_ a' c); `(data_block sh data d))).

replace Delta with (initialized _p (initialized _n (initialized _data
                     (func_tycontext f_SHA256_Update Vprog Gtot))))
 by (simplify_Delta; reflexivity).
 unfold POSTCONDITION, abbreviate; clear POSTCONDITION Delta MORE_COMMANDS.

make_sequential.
rewrite overridePost_normal'.
fold update_last_if.

apply semax_pre0 with  (* should be able to do "eapply" *)
       (PROP  ()
        LOCAL  (temp _p (offset_val (Int.repr 40) c); temp _c c;
        temp _data
          (offset_val (Int.repr (Z.of_nat (length blocks * 4 - length dd))) d);
        temp _len
          (Vint (Int.repr (Z.of_nat (Z.to_nat len - (length blocks * 4 - length dd)))));
        var _K256 (tarray tuint CBLOCKz) kv)
        SEP  (`(K_vector kv);
        `(data_at Tsh t_struct_SHA256state_st
            (map Vint (hash_blocks init_registers (hashed ++ blocks)),
            (Vint (lo_part (hilo hi lo + Z.of_nat (Z.to_nat len) * 8)),
            (Vint (hi_part (hilo hi lo + Z.of_nat (Z.to_nat len) * 8)),
            ([],
            Vint
              (Int.repr (Z.of_nat (Z.to_nat len - (length blocks * 4 - length dd))))))))
            c); `(data_block sh data d)));
 [ | simple apply update_last_if_proof];
  [entailer! | try assumption .. ].
rewrite <- ZtoNat_Zlength. apply Z2Nat.inj_le; auto; omega.
rewrite Z2Nat.id by omega; auto.
rewrite Z2Nat.id by omega; omega.
abbreviate_semax.
(* after the last if *)
 apply extract_exists_pre; intro a'.
 forward.  (* return; *)
 apply exp_right with a'.
 entailer!.
Qed.
