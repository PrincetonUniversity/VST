Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Local Open Scope nat.
Local Open Scope logic.

Definition update_inner_if_then :=
  (Ssequence
      (Scall None
           (Evar _memcpy
              (Tfunction
                 (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                 (tptr tvoid) cc_default))
           [Ebinop Oadd (Etempvar _p (tptr tuchar)) (Etempvar _n tuint)
              (tptr tuchar), Etempvar _data (tptr tuchar),
           Etempvar _fragment tuint])
     (Ssequence
        (Scall None
           (Evar _sha256_block_data_order
              (Tfunction
                 (Tcons (tptr t_struct_SHA256state_st)
                    (Tcons (tptr tvoid) Tnil)) tvoid cc_default))
           [Etempvar _c (tptr t_struct_SHA256state_st),
           Etempvar _p (tptr tuchar)])
        (Ssequence
           (Sset _data
              (Ebinop Oadd (Etempvar _data (tptr tuchar))
                 (Etempvar _fragment tuint) (tptr tuchar)))
           (Ssequence
              (Sset _len
                 (Ebinop Osub (Etempvar _len tuint)
                    (Etempvar _fragment tuint) tuint))
                 (Scall None
                    (Evar _memset
                       (Tfunction
                          (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil)))
                          (tptr tvoid) cc_default))
                    [Etempvar _p (tptr tuchar), Econst_int (Int.repr 0) tint,
                    Ebinop Omul (Econst_int (Int.repr 16) tint)
                      (Econst_int (Int.repr 4) tint) tint]))))).

Definition  update_inner_if_else :=
                (Ssequence
                    (Scall None
                      (Evar _memcpy (Tfunction
                                      (Tcons (tptr tvoid)
                                        (Tcons (tptr tvoid)
                                          (Tcons tuint Tnil))) (tptr tvoid) cc_default))
                      ((Ebinop Oadd (Etempvar _p (tptr tuchar))
                         (Etempvar _n tuint) (tptr tuchar)) ::
                       (Etempvar _data (tptr tuchar)) ::
                       (Etempvar _len tuint) :: nil))
                  (Ssequence
                    (Sassign
                      (Efield
                        (Ederef (Etempvar _c (tptr t_struct_SHA256state_st))
                          t_struct_SHA256state_st) _num tuint)
                      (Ebinop Oadd (Etempvar _n tuint)
                        (Ecast (Etempvar _len tuint) tuint) tuint))
                    (Sreturn None))).

Definition update_inner_if :=
        Sifthenelse (Ebinop Oge (Etempvar _len tuint)
                             (Etempvar _fragment tuint) tint)
         update_inner_if_then
         update_inner_if_else.

Definition inv_at_inner_if sh hashed len c d dd data kv hi lo:=
 (PROP ()
   (LOCAL 
   (`(eq (Vint (Int.repr (64- Zlength dd)))) (eval_id _fragment);
   `(eq  (offset_val (Int.repr 40) c)) (eval_id _p);
   `(eq (Vint (Int.repr (Zlength dd)))) (eval_id _n);
   `(eq c) (eval_id _c); `(eq d) (eval_id _data);
   `(eq (Vint (Int.repr (Z.of_nat len)))) (eval_id _len);
   `(eq kv) (eval_var _K256 (tarray tuint CBLOCKz)))
   SEP  (`(array_at tuint Tsh (tuints (hash_blocks init_registers hashed)) 0 8 c);
    `(sha256_length (hilo hi lo + (Z.of_nat len)*8) c);
   `(array_at tuchar Tsh (ZnthV tuchar (map Vint (map Int.repr dd))) 0 64 (offset_val (Int.repr 40) c));
   `(field_at Tsh t_struct_SHA256state_st [_num] (Vint (Int.repr (Zlength dd))) c);
   `(K_vector kv);
   `(data_block sh data d)))).

Definition sha_update_inv sh hashed len c d (frag: list Z) (data: list Z) kv r_Nh r_Nl (done: bool) :=
   (EX blocks:list int,
   PROP  (len >= length blocks*4 - length frag /\
              (LBLOCKz | Zlength blocks) /\ 
              intlist_to_Zlist blocks = frag ++ firstn (length blocks * 4 - length frag) data /\
             if done then len-(length blocks*4 - length frag) < CBLOCK else True)
   LOCAL  (`(eq (offset_val (Int.repr 40) c)) (eval_id _p);
   `(eq c) (eval_id _c); `(eq (offset_val (Int.repr (Z.of_nat (length blocks*4-length frag))) d)) (eval_id _data);
   `(eq (Vint (Int.repr (Z.of_nat (len- (length blocks*4 - length frag)))))) (eval_id _len);
   `(eq kv) (eval_var _K256 (tarray tuint CBLOCKz)))
   SEP  (`(K_vector kv);
    `(array_at tuint Tsh (tuints (hash_blocks init_registers (hashed ++ blocks))) 0 8 c);
    `(sha256_length (hilo r_Nh r_Nl + (Z.of_nat len)*8) c);
   `(array_at_ tuchar Tsh 0 64 (offset_val (Int.repr 40) c));
   `(field_at_ Tsh t_struct_SHA256state_st [_num] c);
   `(data_block sh data d))).

Lemma closed_make_args:
  forall (Q: environ -> mpred) funsig el,
     closed_wrt_vars (fun _ => True) Q ->
  `Q (make_args' funsig el) = Q.
Proof.
intros.
extensionality rho.
unfold_lift.
hnf in H.
unfold make_args'.
specialize (H rho (te_of (make_args (map fst (fst funsig)) (el rho) rho))).
rewrite H.
f_equal.
destruct rho; simpl.
forget (el (mkEnviron ge ve te)) as vl.
forget (map fst (fst funsig)) as il.
induction il; destruct vl; simpl.
unfold globals_only. simpl.
Abort.  (* need to be closed for addressable locals, too *)

Definition Delta_update_inner_if : tycontext.
simplify_Delta_from
  (initialized _fragment
     (initialized _p
        (initialized _n
           (initialized _data (func_tycontext f_SHA256_Update Vprog Gtot))))).
Defined.

Lemma update_inner_if_then_proof:
 forall (Espec : OracleKind) (hashed : list int)
          (dd data : list Z) (c d: val) (sh: share) (len: nat) kv
          (hi lo: int) 
   (H : (Z.of_nat len <= Zlength data)%Z)
   (H7 : ((Zlength hashed * 4 + Zlength dd) * 8)%Z = hilo hi lo)
   (H3 : (Zlength dd < CBLOCKz)%Z)
   (H3' : Forall isbyteZ dd)
   (H4 : (LBLOCKz | Zlength hashed))
   (Hlen : (Z.of_nat len <= Int.max_unsigned)%Z)
   (c' : name _c) (data_ : name _data) (len' : name _len) 
   (data' : name _data) (p : name _p) (n : name _n)
   (fragment_ : name _fragment),
  let j := (40 + Zlength dd)%Z in
  let k := (64 - Zlength dd)%Z in
  forall (H0: (0 < k <= 64)%Z)
       (H1: (64 < Int.max_unsigned)%Z)
       (DBYTES: Forall isbyteZ data),
semax Delta_update_inner_if
  (PROP  ()
   LOCAL 
   (`(typed_true tint)
      (eval_expr
         (Ebinop Oge (Etempvar _len tuint) (Etempvar _fragment tuint) tint));
   `(eq (Vint (Int.repr k))) (eval_id _fragment);
   `(eq (offset_val (Int.repr 40) c)) (eval_id _p);
   `(eq (Vint (Int.repr (Zlength dd)))) (eval_id _n); `(eq c) (eval_id _c);
   `(eq d) (eval_id _data);
   `(eq (Vint (Int.repr (Z.of_nat len)))) (eval_id _len);
   `(eq kv) (eval_var _K256 (tarray tuint CBLOCKz)))
   SEP 
   (`(array_at tuint Tsh (tuints (hash_blocks init_registers hashed)) 0 8 c);
   `(sha256_length (hilo hi lo + Z.of_nat len * 8) c);
   `(array_at tuchar Tsh (ZnthV tuchar (map Vint (map Int.repr dd))) 0 64
       (offset_val (Int.repr 40) c));
   `(field_at Tsh t_struct_SHA256state_st [_num] (Vint (Int.repr (Zlength dd)))
       c); `(K_vector kv);
   `(array_at tuchar sh (tuchars (map Int.repr data)) 0 (Zlength data) d)))
  update_inner_if_then
  (overridePost (sha_update_inv sh hashed len c d dd data kv hi lo false)
     (function_body_ret_assert tvoid
        (EX  a' : s256abs,
         PROP  (update_abs (firstn len data) (S256abs hashed dd) a')
         LOCAL ()
         SEP  (`(K_vector kv); `(sha256state_ a' c); `(data_block sh data d))))).
Proof.
 intros.
 simplify_Delta; abbreviate_semax.
  unfold update_inner_if_then.
  apply (remember_value (eval_id _fragment)); intro fragment.
  forward_call (* memcpy (p+n,data,fragment); *)
   ((sh,Tsh), 
    offset_val (Int.repr (Zlength dd)) (offset_val (Int.repr 40) c),
    d, 
    Int.unsigned (force_int fragment),
    Basics.compose force_int (ZnthV tuchar (map Vint (map Int.repr data)))).
 fold j; fold k.
 entailer!.
 clear fragment H5.
 rewrite negb_true_iff in H6. 
 apply ltu_repr_false in H6; [ | repable_signed | omega].
 clear TC1.
 unfold j,k in *; clear j k.
rewrite cVint_force_int_ZnthV
 by (rewrite initial_world.Zlength_map; omega).
 rewrite memory_block_array_tuchar by omega.
 rewrite split_offset_array_at with (contents :=ZnthV tuchar (map Vint (map Int.repr dd))) (lo := Zlength dd); [| omega | simpl; omega | reflexivity].
 rewrite (split_array_at (64-Zlength dd) _ _ (tuchars (map Int.repr data)))
    by omega.

 replace (offset_val (Int.repr (40 + Zlength dd)) c)
          with (offset_val (Int.repr (sizeof tuchar * Zlength dd)) (offset_val (Int.repr 40) c))
  by (change (sizeof tuchar) with 1%Z; rewrite Z.mul_1_l; rewrite offset_offset_val, add_repr; auto).
 cancel.
 
 after_call.
 fold j k.
 rename H5 into H2'.
 gather_SEP 4%Z 1%Z.
 replace_SEP 0%Z (`(array_at tuchar Tsh (ZnthV tuchar (map Vint (map Int.repr (dd ++ data) ))) 0
        64 (offset_val (Int.repr 40) c))).
 entailer!.
 rewrite negb_true_iff in H8; 
 apply ltu_repr_false in H8; [ | omega..].
 unfold j,k in *.
 rename c' into c.
 rewrite cVint_force_int_ZnthV
 by (rewrite initial_world.Zlength_map; omega).
 replace (offset_val (Int.repr (40 + Zlength dd)) c)
          with (offset_val (Int.repr (sizeof tuchar * Zlength dd)) (offset_val (Int.repr 40) c))
  by (change (sizeof tuchar) with 1%Z; rewrite Z.mul_1_l; rewrite offset_offset_val, add_repr; auto).
 rewrite split_offset_array_at with (lo := Zlength dd) (contents := (ZnthV tuchar (map Vint (map Int.repr (dd ++ data))))); [| omega | simpl; omega | reflexivity].
  normalize.
 apply sepcon_derives; apply derives_refl'; apply equal_f; apply array_at_ext; intros.
 unfold ZnthV. repeat rewrite if_false by omega.
 repeat rewrite map_app.
 rewrite app_nth1; auto. repeat rewrite map_length. apply Nat2Z.inj_lt.
 rewrite Z2Nat.id by omega. rewrite <- Zlength_correct; omega.
 repeat rewrite map_app.
 unfold ZnthV. repeat rewrite if_false by omega.
 rewrite app_nth2; auto. f_equal.
 rewrite !map_length. rewrite Zlength_correct. 
 rewrite Z2Nat.inj_add by omega.
 rewrite Nat2Z.id. omega.
 rewrite map_length; auto.
 repeat rewrite map_length. apply Nat2Z.inj_ge.
 rewrite Z2Nat.id by omega. rewrite <- Zlength_correct; omega.

 forward_call (* sha256_block_data_order (c,p); *)
   (hashed, Zlist_to_intlist (dd++(firstn (Z.to_nat k) data)), c, (offset_val (Int.repr 40) c), Tsh, kv).
 entailer.
 unfold j,k in *|-.
 rewrite negb_true_iff in H9; apply ltu_repr_false in H9; [ | omega..].
 assert (length (dd ++ firstn (Z.to_nat k) data) = 64). {
  unfold k.
  rewrite app_length.
  rewrite firstn_length, min_l.
  apply Nat2Z.inj. rewrite Nat2Z.inj_add.
  rewrite Z2Nat.id.
  change (Z.of_nat 64) with 64%Z.
  rewrite <- Zlength_correct; omega.
  omega.
  apply Nat2Z.inj_le.  rewrite Z2Nat.id.  rewrite <- Zlength_correct; omega.
  omega.
}
 assert (length (Zlist_to_intlist (dd ++ firstn (Z.to_nat k) data)) = LBLOCK). {
  apply length_Zlist_to_intlist. assumption.
}
 apply andp_right; [apply prop_right |].
 rewrite Zlength_correct, H12. reflexivity.
 replace (data_block Tsh
      (intlist_to_Zlist (Zlist_to_intlist (dd ++ firstn (Z.to_nat k) data)))
      (offset_val (Int.repr 40) c))
    with (array_at tuchar Tsh (ZnthV tuchar (map Vint (map Int.repr (dd ++ data)))) 0
  64 (offset_val (Int.repr 40) c)).
 cancel.
 unfold data_block.
 rewrite prop_true_andp.
 replace (Zlength
     (intlist_to_Zlist (Zlist_to_intlist (dd ++ firstn (Z.to_nat k) data))))
  with 64%Z
 by (rewrite Zlength_correct;
      change 64%Z with (Z.of_nat 64); symmetry; f_equal;
       rewrite length_intlist_to_Zlist, H12; reflexivity).
  apply equal_f; apply array_at_ext; intros.
 unfold tuchars, ZnthV. repeat rewrite if_false by omega.
 rewrite Zlist_to_intlist_to_Zlist.
  repeat rewrite map_map. 
  repeat rewrite (@nth_map' Z val _ _ 0%Z).
  f_equal. f_equal.
 destruct (zlt i (Zlength dd)).
 assert (Z.to_nat i < length dd)
  by (apply Nat2Z.inj_lt; rewrite Z2Nat.id by omega; rewrite <- Zlength_correct; auto).
  repeat rewrite app_nth1 by auto; auto.
 assert (Z.to_nat i >= length dd)
  by (apply Nat2Z.inj_ge; rewrite Z2Nat.id by omega; rewrite <- Zlength_correct; auto).
  repeat rewrite app_nth2 by auto; auto.
  symmetry; apply nth_firstn_low.
  unfold k.
  split. apply Nat2Z.inj_lt. rewrite Nat2Z.inj_sub by omega. 
  repeat rewrite Z2Nat.id by omega. rewrite <- Zlength_correct;omega.
 apply Nat2Z.inj_ge.  
  repeat rewrite Z2Nat.id by omega. rewrite <- Zlength_correct;omega.
  rewrite app_length. rewrite firstn_length. rewrite min_l.
  unfold k; apply Nat2Z.inj_lt.
 rewrite Z2Nat.id by omega; rewrite Nat2Z.inj_add; 
 rewrite Z2Nat.id by omega; rewrite <- Zlength_correct.
 omega.
 unfold k.
 apply Nat2Z.inj_le; rewrite Z2Nat.id by omega.
  rewrite <- Zlength_correct; omega.
  apply Nat2Z.inj_lt; rewrite  Z2Nat.id by omega.
  rewrite app_length, Nat2Z.inj_add.
 repeat rewrite <- Zlength_correct.
  omega.
 rewrite H11; exists LBLOCK; reflexivity.
 rewrite Forall_app; split; auto.
 apply Forall_firstn; auto.
 apply isbyte_intlist_to_Zlist.
 after_call.
 forward. (* data  += fragment; *)
entailer!.
 forward. (* len -= fragment; *)
      normalize_postcondition.
 forward_call (* memset (p,0,SHA_CBLOCK); *)
    (Tsh, offset_val (Int.repr 40) c, 64%Z, Int.zero). {
 fold k. fold j.
 unfold data_block.
 entailer!.
 simpl.
 rewrite <- H12 in H8, H10; clear len'0 H12.
 simpl in H8.
 inversion H8; clear H8; subst len'.
 simpl in H10.
 rewrite memory_block_array_tuchar by omega.
 replace  (Zlength
     (intlist_to_Zlist (Zlist_to_intlist (dd ++ firstn (Z.to_nat k) data))))
    with 64%Z.
 cancel.
 rewrite Zlength_intlist_to_Zlist.
 rewrite Zlength_correct.
 change 64%Z with (4*16)%Z; f_equal.
 rewrite length_Zlist_to_intlist with (n:=16).
 reflexivity.
 simpl.
 rewrite app_length, firstn_length.
 rewrite min_l.
 unfold k in *. 
 apply Nat2Z.inj.
 rewrite Nat2Z.inj_add.
 rewrite Z2Nat.id by omega.
 rewrite <- Zlength_correct.
 change (Z.of_nat 64) with 64%Z; omega.
 unfold k in *.
 apply Nat2Z.inj_le; rewrite Z2Nat.id by omega.
 rewrite <- Zlength_correct.
 fold k in H10;  simpl in H10.
 unfold Int.ltu in H10; if_tac in H10; try inv H10.
 unfold k in H8; repeat rewrite Int.unsigned_repr in H8 by omega.
 omega.
}

 after_call.
 unfold sha_update_inv.
 entailer.
 rewrite negb_true_iff in H9.
 apply ltu_repr_false in H9; [ | omega..].
 clear TC0  TC1.
 apply exp_right with (Zlist_to_intlist (dd ++ firstn (Z.to_nat k) data)).
 assert (LL: length (dd ++ firstn (Z.to_nat k) data) = CBLOCK). {
 rewrite app_length. rewrite firstn_length. rewrite min_l.
 unfold k in *; 
 apply Nat2Z.inj. rewrite Nat2Z.inj_add.
 rewrite Z2Nat.id by omega.
 rewrite <- Zlength_correct. change (Z.of_nat (CBLOCK)) with 64%Z.
 omega.
 apply Nat2Z.inj_le;  rewrite Z2Nat.id by omega; rewrite <- Zlength_correct; omega.
}
assert (length (Zlist_to_intlist (dd ++ firstn (Z.to_nat k) data)) = LBLOCK). {
 apply length_Zlist_to_intlist. change (4*LBLOCK)%nat with CBLOCK.
 apply LL.
}
 assert (KK: k = Z.of_nat (LBLOCK * 4 - length dd)). {
 unfold k.
 rewrite Nat2Z.inj_sub. rewrite Zlength_correct; reflexivity.
 unfold k in H0. clear - H0.
 apply Nat2Z.inj_le.
 change (Z.of_nat (LBLOCK*4)) with 64%Z.
 rewrite <- Zlength_correct.
 omega.
}
 entailer!.
 *
  rewrite H6. 
  apply Nat2Z.inj_ge.
  rewrite Nat2Z.inj_sub.
  change (Z.of_nat (LBLOCK*4)) with 64%Z.
  rewrite <- Zlength_correct; omega.
  clear - H3. apply Nat2Z.inj_le. rewrite <- Zlength_correct.
  change (Z.of_nat (LBLOCK*4)%nat) with CBLOCKz; clear - H3; omega.
 * 
  apply Zlength_length in H6; auto.
  rewrite H6. exists 1%Z; reflexivity.
 *
  rewrite H6. rewrite Zlist_to_intlist_to_Zlist.
  f_equal. f_equal. clear - H0.
  rewrite Z2Nat.inj_sub by omega.
  rewrite Zlength_correct, Nat2Z.id.
  reflexivity.
  rewrite LL. exists 16; reflexivity.
  rewrite Forall_app; split; auto.
  apply Forall_firstn; auto.
 *
  rewrite H6. f_equal.
  f_equal.
  auto.
 *
  rewrite H6. do 2 f_equal.
  rewrite Nat2Z.inj_sub. f_equal; auto.
  apply Nat2Z.inj_le.
  rewrite <- KK. omega.
 *
  unfold data_block.
  rewrite prop_true_andp by auto. 
  rewrite cVint_force_int_ZnthV.
  rewrite <- split_array_at.
 auto.
 omega. rewrite initial_world.Zlength_map. omega.
Qed.
