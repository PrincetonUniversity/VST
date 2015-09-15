Require Import floyd.proofauto.
Import ListNotations.
Require sha.sha.
Require Import sha.SHA256.
Local Open Scope logic.

Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.HMAC_functional_prog.
Require Import sha.HMAC256_functional_prog.
Require Import sha.spec_hmacNK.
Require Import vst_lemmas.
Require Import hmac_pure_lemmas.
Require Import hmac_common_lemmas.

Require Import sha.hmac_NK.
Require Import sha.verif_hmacNK_init_part1.

Lemma isbyte_zeroExt8: forall x, isbyteZ x -> Int.repr x = (Int.zero_ext 8 (Int.repr x)).
Proof. intros. rewrite zero_ext_inrange. trivial.
  simpl.  unfold isbyteZ in H. rewrite Int.unsigned_repr. omega.
  split. omega. rewrite int_max_unsigned_eq. omega.
Qed. 

Lemma isbyte_zeroExt8': forall x, isbyteZ x -> x = Int.unsigned (Int.zero_ext 8 (Int.repr x)).
Proof. intros. rewrite <- isbyte_zeroExt8; trivial.
  rewrite Int.unsigned_repr; trivial. unfold isbyteZ in H. 
  split. omega. rewrite int_max_unsigned_eq. omega.
Qed. 

Lemma eval_cast_tuchar_of_isbyteZ q: isbyteZ q ->
      eval_cast tuchar tuchar (Vint (Int.repr q)) = Vint (Int.repr q). 
Proof. unfold eval_cast. simpl. intros. f_equal. apply zero_ext_inrange. simpl. 
  destruct H.
  rewrite Int.unsigned_repr. omega. rewrite int_max_unsigned_eq. omega.
Qed.

Lemma Znth_map_Vint_is_int_I8: forall l (i : Z) (F: Forall isbyteZ l),
       0 <= i < Zlength l -> 
is_int I8 Unsigned
  (Znth i (map Vint (map Int.repr l)) Vundef).
Proof. intros. unfold Znth.
if_tac; [omega | ].
assert (Z.to_nat i < length l)%nat.
destruct H.
rewrite Zlength_correct in H1.
apply Z2Nat.inj_lt in H1; try omega.
rewrite Nat2Z.id in H1. auto.
unfold is_int. simpl.
clear - H1 F.
revert l F H1; induction (Z.to_nat i); destruct l; intros; simpl in *.
omega. 
apply Forall_inv in F. specialize (isbyteZ_range _ F); intros R.
  rewrite Int.unsigned_repr. omega. split. omega.  
  assert ( Byte.max_unsigned <= Int.max_unsigned).
    unfold Byte.max_unsigned, Int.max_unsigned. 
    unfold Byte.modulus, Int.modulus, Byte.wordsize, Int.wordsize. simpl. omega.
   omega.
  omega.
 apply IHn; try omega. inversion F; trivial.
Qed.

Lemma Znth_map_Vint_is_int_I8': forall l (i : Z) ,
       0 <= i < Zlength l -> 
is_int I8 Unsigned
  (Znth i (map Vint (map Int.repr (map Byte.unsigned l))) Vundef).
Proof. intros. apply Znth_map_Vint_is_int_I8.
  apply isbyte_map_ByteUnsigned.
  rewrite Zlength_map; trivial.
Qed.

Definition FIRSTN {A} i (l:list A) := firstn (Z.to_nat i) l.

Lemma FIRSTN_precise {A} n (l:list A) (H: Zlength l = n): FIRSTN n l = l.
Proof. unfold FIRSTN.
       apply firstn_precise. subst n. apply Zlength_length; trivial. apply Zlength_nonneg.
Qed.

Lemma FIRSTN_zero {A} (l:list A): FIRSTN 0 l = []. Proof. reflexivity. Qed.

Definition SKIPN {A} i (l:list A) := skipn (Z.to_nat i) l.

Lemma SKIPn_short {A : Type} n (al : list A): (Zlength al <= n) -> SKIPN n al = [].
Proof. unfold SKIPN. intros. apply skipn_short. 
       rewrite Zlength_correct in H. rewrite <- (Nat2Z.id (length al)). 
       rewrite (Z2Nat.inj_le _ n) in H. omega. specialize (Zlength_nonneg al); rewrite Zlength_correct. trivial.
       specialize (Zlength_nonneg al); rewrite Zlength_correct. intros; omega. 
Qed.

Lemma UPD_IPAD: forall
  (key : list Z)
  (ZLI : Zlength
        (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad) =
      64)
  (i : Z)
  (I : 0 <= i < 64)
  (isbyteZQb : isbyteZ (nth (Z.to_nat i) (HMAC_SHA256.mkKey key) 0))
  (X : Znth i (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) Vundef =
      Vint (Int.repr (nth (Z.to_nat i) (HMAC_SHA256.mkKey key) 0))),
upd_reptype_array tuchar i
  (FIRSTN i
     (map Vint
        (map Int.repr
           (map Byte.unsigned
              (HMAC_SHA256.mkArg (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad)))))
  (force_val
     (sem_cast_i2i I8 Unsigned
        (Vint
           (Int.repr (Z.lxor (nth (Z.to_nat i) (HMAC_SHA256.mkKey key) 0) 54))))) =
FIRSTN (i + 1)
  (map Vint
     (map Int.repr
        (map Byte.unsigned
           (HMAC_SHA256.mkArg (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad)))).
Proof. intros.
           assert (ZLI': length (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad) = Z.to_nat 64).
              rewrite Zlength_correct in ZLI. rewrite <- ZLI. rewrite Nat2Z.id; trivial.
           unfold FIRSTN. unfold upd_reptype_array.
           rewrite skipn_short. Focus 2. rewrite firstn_length. unfold  HMAC_SHA256.mkArgZ in ZLI'.
                                         do 2 rewrite map_length. rewrite ZLI'.
                                         rewrite Min.min_l. unfold nat_of_Z. rewrite Z2Nat.inj_add. simpl. omega. apply I. omega.
                                apply Z2Nat.inj_le; omega.
           rewrite force_lengthn_id. Focus 2. rewrite firstn_length. unfold  HMAC_SHA256.mkArgZ in ZLI'.
                                         do 2 rewrite map_length. rewrite ZLI'.
                                         rewrite Min.min_l. reflexivity.
                                apply Z2Nat.inj_le; omega.
           rewrite Z2Nat.inj_add; try omega. rewrite <- firstn_app. f_equal.
          rewrite <- firstn_1_skipn with (d:=Vint (Int.repr (Byte.unsigned ((fun p : byte * byte => Byte.xor (fst p) (snd p)) (Byte.zero,Byte.zero))))).
          Focus 2. do 2 rewrite map_length. unfold  HMAC_SHA256.mkArgZ in ZLI'. rewrite ZLI'. apply Z2Nat.inj_lt; omega.
          f_equal. rewrite map_nth. rewrite map_nth. rewrite map_nth. unfold Znth in X. unfold HMAC_SHA256.mkArg.
                   rewrite (map_nth (fun p : byte * byte => Byte.xor (fst p) (snd p))
                                       (combine (map Byte.repr (HMAC_SHA256.mkKey key)) (HMAC_SHA256.sixtyfour Ipad)) 
                                       (Byte.zero, Byte.zero)
                                       (Z.to_nat i)).
                   rewrite combine_nth. 
                   Focus 2. rewrite map_length, length_SF, mkKey_length. reflexivity.
                   assert (BMU: Byte.max_unsigned = 255). reflexivity.
                   assert (isByte54: 0 <= 54 <= Byte.max_unsigned).
                      rewrite BMU; omega. 
                   destruct (isbyteZ_xor (nth (Z.to_nat i) (HMAC_SHA256.mkKey key) 0) 54 isbyteZQb) as [AA BB].
                     split; rewrite BMU in *; omega.                      
                   unfold force_val. rewrite sem_cast_i2i_correct_range.
                   destruct (zlt i 0); try omega. remember (HMAC_SHA256.sixtyfour Ipad).  simpl.
                   rewrite (map_nth Byte.repr (HMAC_SHA256.mkKey key) Z0).
                   unfold Byte.xor.
                   assert (NTH: nth (Z.to_nat i) l Byte.zero = Byte.repr 54).
                     subst l. apply nth_list_repeat'. apply (Z2Nat.inj_lt _ 64). apply I. omega. omega.
                   rewrite NTH, (Byte.unsigned_repr 54); trivial.
                   rewrite (Byte.unsigned_repr (nth (Z.to_nat i) (HMAC_SHA256.mkKey key) 0)).
                     Focus 2. destruct isbyteZQb. omega.
                   rewrite Byte.unsigned_repr. trivial.
                   rewrite BMU in *; split; omega. 
             simpl. rewrite Int.unsigned_repr. rewrite BMU in *; omega. 
               rewrite int_max_unsigned_eq. rewrite BMU in *; omega.
Qed.

Lemma UPD_OPAD: forall
  (key : list Z)
  (ZLI : Zlength (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad) = 64)
  (ZLO : Zlength (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Opad) = 64)
  (i : Z)
  (I : 0 <= i < 64)
  (isbyteZQb : isbyteZ (nth (Z.to_nat i) (HMAC_SHA256.mkKey key) 0))
  (X : Znth i (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) Vundef =
       Vint (Int.repr (nth (Z.to_nat i) (HMAC_SHA256.mkKey key) 0))),
upd_reptype_array tuchar i
  (FIRSTN i
     (map Vint
        (map Int.repr
           (map Byte.unsigned
              (HMAC_SHA256.mkArg (map Byte.repr (HMAC_SHA256.mkKey key)) Opad)))) ++
   SKIPN i
     (map Vint
        (map Int.repr
           (map Byte.unsigned
              (HMAC_SHA256.mkArg (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad)))))
  (Vint
     (Int.zero_ext 8
        (Int.xor (Int.repr 92)
           (Int.repr (nth (Z.to_nat i) (HMAC_SHA256.mkKey key) 0))))) =
FIRSTN (i + 1)
  (map Vint
     (map Int.repr
        (map Byte.unsigned
           (HMAC_SHA256.mkArg (map Byte.repr (HMAC_SHA256.mkKey key)) Opad)))) ++
SKIPN (i + 1)
  (map Vint
     (map Int.repr
        (map Byte.unsigned
           (HMAC_SHA256.mkArg (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad)))).
Proof. intros.
           assert (ZLI': length (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad) = Z.to_nat 64).
                 rewrite Zlength_correct in ZLI. rewrite <- ZLI. rewrite Nat2Z.id; trivial. 
           assert (ZLO': length (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Opad) = Z.to_nat 64).
              rewrite Zlength_correct in ZLO. rewrite <- ZLO. rewrite Nat2Z.id; trivial.
           unfold FIRSTN. unfold upd_reptype_array, nat_of_Z.
           rewrite force_lengthn_long.
           Focus 2. unfold SKIPN; rewrite app_length, firstn_length, skipn_length.
           unfold HMAC_SHA256.mkArgZ in ZLI', ZLO'. 
           do 2 rewrite map_length. rewrite ZLO'. 
           do 2 rewrite map_length. rewrite ZLI', Min.min_l. 2: apply Z2Nat.inj_le; omega.
              rewrite le_plus_minus_r; apply Z2Nat.inj_le; omega. 
           do 2 rewrite map_length. unfold HMAC_SHA256.mkArgZ in ZLI'; rewrite ZLI'. apply Z2Nat.inj_le; omega.
           rewrite firstn_app1.
           Focus 2. rewrite firstn_length, Min.min_l. omega.   
              do 2 rewrite map_length. unfold HMAC_SHA256.mkArgZ in ZLO'; rewrite ZLO'. apply Z2Nat.inj_le; omega.
           rewrite firstn_precise. 
           Focus 2. rewrite firstn_length, Min.min_l. omega.   
              do 2 rewrite map_length. unfold HMAC_SHA256.mkArgZ in ZLO'; rewrite ZLO'. apply Z2Nat.inj_le; omega.
           rewrite Z2Nat.inj_add; try omega. rewrite <- firstn_app. rewrite <- app_assoc.
           f_equal.
          rewrite <- firstn_1_skipn with (d:=Vint (Int.repr (Byte.unsigned ((fun p : byte * byte => Byte.xor (fst p) (snd p)) (Byte.zero,Byte.zero))))).
          Focus 2. do 2 rewrite map_length. unfold  HMAC_SHA256.mkArgZ in ZLO'. rewrite ZLO'. apply Z2Nat.inj_lt; omega.
          simpl. f_equal. rewrite map_nth. rewrite map_nth. rewrite map_nth. unfold Znth in X. unfold HMAC_SHA256.mkArg.
                   specialize (map_nth (fun p : byte * byte => Byte.xor (fst p) (snd p))
                                       (combine (map Byte.repr (HMAC_SHA256.mkKey key)) (HMAC_SHA256.sixtyfour Opad)) 
                                       (Byte.zero, Byte.zero)
                                       (Z.to_nat i)). simpl; intros. rewrite H; clear H.
                   rewrite combine_nth. 
                   Focus 2. rewrite map_length, length_SF, mkKey_length. reflexivity.
                   assert (BMU: Byte.max_unsigned = 255). reflexivity.
                   assert (isByte54: 0 <= 54 <= Byte.max_unsigned).
                      rewrite BMU; omega. 
                   destruct (isbyteZ_xor (nth (Z.to_nat i) (HMAC_SHA256.mkKey key) 0) 92 isbyteZQb) as [AA BB].
                     split; rewrite BMU in *; omega.
                   rewrite fst_unfold, snd_unfold, Int.xor_commut.
(*                   unfold force_val. rewrite sem_cast_i2i_correct_range.
                   destruct (zlt i 0); try omega.*) 
                   remember (HMAC_SHA256.sixtyfour Opad). 
                   rewrite (map_nth Byte.repr (HMAC_SHA256.mkKey key) Z0).
                   unfold Byte.xor.
                   assert (NTH: nth (Z.to_nat i) l Byte.zero = Byte.repr 92).
                     subst l. apply nth_list_repeat'. apply (Z2Nat.inj_lt _ 64). apply I. omega. omega.
                   rewrite NTH, (Byte.unsigned_repr 92); trivial.
                   rewrite (Byte.unsigned_repr (nth (Z.to_nat i) (HMAC_SHA256.mkKey key) 0)).
                     Focus 2. destruct isbyteZQb. omega.
                   rewrite Byte.unsigned_repr. unfold Int.xor.
                   rewrite Int.unsigned_repr.  
                   rewrite Int.unsigned_repr. 2: rewrite int_max_unsigned_eq; omega.
                   rewrite <- isbyte_zeroExt8; trivial.
                   rewrite BMU in *; split; omega.
                   destruct isbyteZQb. rewrite int_max_unsigned_eq; split; omega.
                   rewrite BMU in *; split; omega.
              rewrite <- skipn_skipn. 
              rewrite skipn_app2; rewrite firstn_length, Min.min_l.
              Focus 2. do 2 rewrite map_length. unfold HMAC_SHA256.mkArgZ in ZLO'; rewrite ZLO'.
                       apply Z2Nat.inj_le; omega.
              rewrite minus_diag. simpl. unfold SKIPN. rewrite Z2Nat.inj_add, <- skipn_skipn. reflexivity.
              omega. omega. omega.
              do 2 rewrite map_length. unfold HMAC_SHA256.mkArgZ in ZLO'; rewrite ZLO'.
                       apply Z2Nat.inj_le; omega.
Qed.

Definition postResetHMS (iS oS: s256state): hmacstate :=
  (emptySha, (iS, oS)).

Definition initPostResetConditional r (c:val) (k: val) h key iS oS: mpred:=
  match k with
    Vint z => if Int.eq z Int.zero
              then if zeq r Z0 then hmacstate_PreInitNull key h c else FF
              else FF
  | Vptr b ofs => if zeq r 0 then FF
                  else !!(Forall isbyteZ key) &&
                       ((data_at Tsh t_struct_hmac_ctx_st (postResetHMS iS oS) c) *
                        (data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key)) (Vptr b ofs)))
  | _ => FF
  end.

Lemma init_part2: forall
(Espec : OracleKind)
(c : val)
(k : val)
(l : Z)
(key : list Z)
(kv : val)
(h1 : hmacabs)
(KL1 : l = Zlength key)
(KL2 : 0 <= l <= Int.max_signed)
(KL3 : l * 8 < two_p 64)
(ctx' : name _ctx)
(key' : name _key)
(len' : name _len)
(Delta := initialized _reset 
       (func_tycontext f_HMAC_Init HmacVarSpecs HmacFunSpecs))
(cb : block)
(cofs : int)
(pad : val)
(r : Z)
(ckb : block)
(ckoff : int)
(*(HC : c = Vptr cb cofs)*)
(R : r = 0 \/ r = 1)
(PostResetBranch : environ -> mpred)
(HeqPostResetBranch : PostResetBranch = EX shaStates:_ ,
          PROP  (innerShaInit (map Byte.repr (HMAC_SHA256.mkKey key))
                           (fst shaStates) /\
                  s256_relate (fst shaStates) (fst (snd shaStates)) /\
                  outerShaInit (map Byte.repr (HMAC_SHA256.mkKey key))
                           (fst (snd (snd shaStates))) /\ 
                  s256_relate (fst (snd (snd shaStates))) (snd (snd (snd shaStates))))
          LOCAL  (lvar _pad (tarray tuchar 64) pad; 
                  lvar _ctx_key (tarray tuchar 64) (Vptr ckb ckoff); 
                  temp _ctx (Vptr cb cofs); temp _key k;
                  temp _len (Vint (Int.repr l));
                  gvar sha._K256 kv)
          SEP  (`(data_at_ Tsh (tarray tuchar 64) pad);
                `(data_at_ Tsh (Tarray tuchar 64 noattr) (Vptr ckb ckoff)); 
                `(initPostResetConditional r (Vptr cb cofs) k h1 key (fst (snd shaStates)) (snd (snd (snd shaStates))));
                `(K_vector kv)))
(*WAS:(HeqPostResetBranch : PostResetBranch =
                     EX  iSA : s256abs,
                     (EX  iS : s256state,
                      (EX  oSA : s256abs,
                       (EX  oS : s256state,
                        PROP 
                        (innerShaInit (map Byte.repr (HMAC_SHA256.mkKey key))
                           iSA /\
                         s256_relate iSA iS /\
                         outerShaInit (map Byte.repr (HMAC_SHA256.mkKey key))
                           oSA /\ s256_relate oSA oS)
                        LOCAL  (`(eq pad) (eval_var _pad (tarray tuchar 64));
                        `(eq (Vptr cb cofs)) (eval_id _ctx);
                        `(eq ctxkey) (eval_var _ctx_key (tarray tuchar 64));
                        `(eq k) (eval_id _key);
                        `(eq (Vint (Int.repr l))) (eval_id _len);
                        `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
                        SEP  (`(data_at_ Tsh (tarray tuchar 64) pad);
                        `(data_at_ Tsh (tarray tuchar 64) ctxkey);
                        `(initPostResetConditional r c k h1 key iS oS);
                        `(K_vector KV))))))*),
@semax Espec Delta
  (PROP  ()
   LOCAL  (temp _reset (Vint (Int.repr r));
   lvar _ctx_key (tarray tuchar 64) (Vptr ckb ckoff); lvar _pad (tarray tuchar 64) pad;
   temp _ctx (Vptr cb cofs); temp _key k; temp _len (Vint (Int.repr l));
   gvar sha._K256 kv)
   SEP  (`(data_at_ Tsh (tarray tuchar 64) pad);
   `(initPostKeyNullConditional r (Vptr cb cofs) k h1 key (Vptr ckb ckoff));
   `(K_vector kv)))
  (Sifthenelse (Etempvar _reset tint)
     (Ssequence
        (Sfor (Sset _i (Econst_int (Int.repr 0) tint))
           (Ebinop Olt (Etempvar _i tint) (Econst_int (Int.repr 64) tint)
              tint)
           (Ssequence
              (Sset _aux
                 (Ecast
                    (Ederef
                       (Ebinop Oadd (Evar _ctx_key (tarray tuchar 64))
                          (Etempvar _i tint) (tptr tuchar)) tuchar) tuchar))
              (Ssequence
                 (Sset _aux
                    (Ecast
                       (Ebinop Oxor (Econst_int (Int.repr 54) tint)
                          (Etempvar _aux tuchar) tint) tuchar))
                 (Sassign
                    (Ederef
                       (Ebinop Oadd (Evar _pad (tarray tuchar 64))
                          (Etempvar _i tint) (tptr tuchar)) tuchar)
                    (Etempvar _aux tuchar))))
           (Sset _i
              (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                 tint)))
        (Ssequence
           (Scall None
              (Evar _SHA256_Init
                 (Tfunction (Tcons (tptr t_struct_SHA256state_st) Tnil) tvoid
                    cc_default))
              [Eaddrof
                 (Efield
                    (Ederef (Etempvar _ctx (tptr t_struct_hmac_ctx_st))
                       t_struct_hmac_ctx_st) _i_ctx t_struct_SHA256state_st)
                 (tptr t_struct_SHA256state_st)])
           (Ssequence
              (Scall None
                 (Evar _SHA256_Update
                    (Tfunction
                       (Tcons (tptr t_struct_SHA256state_st)
                          (Tcons (tptr tvoid) (Tcons tuint Tnil))) tvoid
                       cc_default))
                 [Eaddrof
                    (Efield
                       (Ederef (Etempvar _ctx (tptr t_struct_hmac_ctx_st))
                          t_struct_hmac_ctx_st) _i_ctx
                       t_struct_SHA256state_st)
                    (tptr t_struct_SHA256state_st);
                 Evar _pad (tarray tuchar 64); Econst_int (Int.repr 64) tint])
              (Ssequence
                 (Sfor (Sset _i (Econst_int (Int.repr 0) tint))
                    (Ebinop Olt (Etempvar _i tint)
                       (Econst_int (Int.repr 64) tint) tint)
                    (Ssequence
                       (Sset _aux
                          (Ecast
                             (Ederef
                                (Ebinop Oadd
                                   (Evar _ctx_key (tarray tuchar 64))
                                   (Etempvar _i tint) (tptr tuchar)) tuchar)
                             tuchar))
                       (Sassign
                          (Ederef
                             (Ebinop Oadd (Evar _pad (tarray tuchar 64))
                                (Etempvar _i tint) (tptr tuchar)) tuchar)
                          (Ebinop Oxor (Econst_int (Int.repr 92) tint)
                             (Etempvar _aux tuchar) tint)))
                    (Sset _i
                       (Ebinop Oadd (Etempvar _i tint)
                          (Econst_int (Int.repr 1) tint) tint)))
                 (Ssequence
                    (Scall None
                       (Evar _SHA256_Init
                          (Tfunction
                             (Tcons (tptr t_struct_SHA256state_st) Tnil)
                             tvoid cc_default))
                       [Eaddrof
                          (Efield
                             (Ederef
                                (Etempvar _ctx (tptr t_struct_hmac_ctx_st))
                                t_struct_hmac_ctx_st) _o_ctx
                             t_struct_SHA256state_st)
                          (tptr t_struct_SHA256state_st)])
                    (Scall None
                       (Evar _SHA256_Update
                          (Tfunction
                             (Tcons (tptr t_struct_SHA256state_st)
                                (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                             tvoid cc_default))
                       [Eaddrof
                          (Efield
                             (Ederef
                                (Etempvar _ctx (tptr t_struct_hmac_ctx_st))
                                t_struct_hmac_ctx_st) _o_ctx
                             t_struct_SHA256state_st)
                          (tptr t_struct_SHA256state_st);
                       Evar _pad (tarray tuchar 64);
                       Econst_int (Int.repr 64) tint])))))) Sskip)
    (overridePost PostResetBranch
     (frame_ret_assert
        (function_body_ret_assert tvoid
           (EX  h : hmacabs,
            PROP  (hmacInit key h)
            LOCAL ()
            SEP  (`(hmacstate_ h c); `(initPostKey k key); `(K_vector kv))))
        (stackframe_of f_HMAC_Init))).
Proof. intros.
forward_if PostResetBranch. 
  { (* THEN*)
    rename H into r_true. 
    remember (map Vint (map Int.repr 
              (map Byte.unsigned (HMAC_SHA256.mkArg (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad)))) as IPADcont.
    remember (map Vint (map Int.repr 
              (map Byte.unsigned (HMAC_SHA256.mkArg (map Byte.repr (HMAC_SHA256.mkKey key)) Opad)))) as OPADcont.
    assert (ZLI: Zlength (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad) = 64).
            rewrite Zlength_mkArgZ.
            repeat rewrite map_length. rewrite mkKey_length.
            unfold SHA256.BlockSize; simpl. trivial. 
    assert (ZLO: Zlength (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Opad) = 64).
            rewrite Zlength_mkArgZ.
            repeat rewrite map_length. rewrite mkKey_length.
            unfold SHA256.BlockSize; simpl. trivial. 
    unfold data_at_, tarray.
    assert_PROP (isptr pad). entailer. apply isptrD in H; destruct H as [pb [pofs Hpad]]. subst pad. 
    apply semax_pre with (P':=PROP  (r<>0 /\ Forall isbyteZ key)
         LOCAL  (temp _reset (Vint (Int.repr r));
            lvar _ctx_key (Tarray tuchar 64 noattr) (Vptr ckb ckoff);
            lvar _pad (Tarray tuchar 64 noattr) (Vptr pb pofs);
            temp _ctx (Vptr cb cofs); temp _key k; temp _len (Vint (Int.repr l));
            gvar sha._K256 kv)
         SEP  (`(K_vector kv);
               `(data_at Tsh (Tarray tuchar 64 noattr)
                   (default_val (Tarray tuchar 64 noattr)) (Vptr pb pofs));
               `(data_at Tsh t_struct_hmac_ctx_st keyedHMS (Vptr cb cofs));
               `(data_at Tsh (tarray tuchar 64) (map Vint (map Int.repr (HMAC_SHA256.mkKey key)))
                  (Vptr ckb ckoff));
               `(data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key)) k))).
    { clear HeqPostResetBranch PostResetBranch.
      unfold initPostKeyNullConditional. entailer.
      destruct key'; try contradiction.
      (*integer, ie key==NULL*)
          simpl in TC0. subst i. simpl. if_tac. subst r. inversion r_true.
          apply andp_right. entailer. entailer.
      (*key == Vptr*)
       if_tac. subst r. inversion r_true.
          entailer. cancel.
    }
    normalize. destruct R; subst r. omega. clear H. rename H0 into isbyte_key.
    assert_PROP (isptr k). entailer. apply isptrD in H; destruct H as [kb [kofs HK]]. subst k.

    eapply semax_seq'. (*TODO: using forward_seq here introduces another Delta0 in goal2 - but it worked fine before I split this off into file XXX_part2.v *)
    instantiate (1:= 
  (PROP  ()
   LOCAL  (temp _reset (Vint (Int.repr 1));
      lvar _ctx_key (Tarray tuchar 64 noattr) (Vptr ckb ckoff);
      lvar _pad (Tarray tuchar 64 noattr) (Vptr pb pofs);
      temp _ctx (Vptr cb cofs); temp _key (Vptr kb kofs);
      temp _len (Vint (Int.repr l)); gvar sha._K256 kv)
   SEP  (`(K_vector kv);
     `(data_at Tsh (Tarray tuchar 64 noattr) IPADcont (Vptr pb pofs));
     `(data_at Tsh t_struct_hmac_ctx_st keyedHMS (Vptr cb cofs));
     `(data_at Tsh (tarray tuchar 64)
         (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) (Vptr ckb ckoff));
     `(data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key))
         (Vptr kb kofs))))).
    { (*ipad loop*)
      forward_for_simple_bound' 64 (EX i:Z, 
        (PROP  ()
         LOCAL  (temp _reset (Vint (Int.repr 1));
           lvar _ctx_key (Tarray tuchar 64 noattr) (Vptr ckb ckoff);
           lvar _pad (Tarray tuchar 64 noattr) (Vptr pb pofs);
           temp _ctx (Vptr cb cofs); temp _key (Vptr kb kofs);
           temp _len (Vint (Int.repr l)); gvar sha._K256 kv)
         SEP  (`(K_vector kv);
          `(data_at Tsh (Tarray tuchar 64 noattr) (FIRSTN i IPADcont) (Vptr pb pofs));
          `(data_at Tsh t_struct_hmac_ctx_st keyedHMS (Vptr cb cofs));
          `(data_at Tsh (tarray tuchar 64)
              (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) (Vptr ckb ckoff));
         `(data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key))
              (Vptr kb kofs))))).
      { (*precondition implies "invariant"*)
        clear HeqPostResetBranch. entailer. 
      } 
      { unfold normal_ret_assert. simpl. intros rho. entailer. cancel.
        rewrite FIRSTN_precise. cancel.
         do 2 rewrite Zlength_map. apply ZLI. 
      }
      { rename H into I. 
        subst PostResetBranch.
        assert (Xb: exists qb, nth (Z.to_nat i) (HMAC_SHA256.mkKey key) Z0 = qb /\ isbyteZ qb).
          { destruct (nth_mapIn (Z.to_nat i) (HMAC_SHA256.mkKey key) 0) as [? [? ?]].
             rewrite mkKey_length.
              split. apply (Z2Nat.inj_le 0); omega. apply (Z2Nat.inj_lt _ 64); omega.
            exists x; split; trivial. eapply Forall_forall. apply isbyteZ_mkKey. eassumption. eassumption.
          }
        destruct Xb as [qb [Qb isbyteZQb]].
        assert (X: Znth i (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) Vundef
                   = Vint (Int.repr qb)). (* (Int.zero_ext 8 q)).*)
          { unfold Znth. destruct (zlt i 0). omega.
            rewrite nth_indep with (d':=Vint (Int.repr 0)).
              Focus 2. repeat rewrite map_length. rewrite mkKey_length. unfold SHA256.BlockSize; simpl. apply (Z2Nat.inj_lt _ 64); omega. 
            repeat rewrite map_nth. rewrite Qb. trivial. 
          }
        forward. entailer.
        apply prop_right. rewrite X. simpl. rewrite <- isbyte_zeroExt8'; trivial.
               apply (isbyteZ_range _ isbyteZQb). 
        unfold force_val. rewrite sem_cast_i2i_correct_range.
            Focus 2. apply Znth_map_Vint_is_int_I8.
                     apply isbyteZ_mkKey. assumption.
                     rewrite Zlength_correct, mkKey_length. unfold SHA256.BlockSize; simpl; assumption.
        rewrite X.
        forward v. subst v.
        unfold Int.xor. 
        rewrite Int.unsigned_repr. 2: rewrite int_max_unsigned_eq; omega.
        rewrite Int.unsigned_repr. 2: destruct isbyteZQb; rewrite int_max_unsigned_eq; omega.
        exploit (isbyteZ_xor 54 qb); trivial. split; omega.
        intros isbyteXOR.
        rewrite <- isbyte_zeroExt8; trivial.
        rewrite Z.lxor_comm. remember (Vint (Int.repr (Z.lxor qb 54))) as xorval.
        forward. simpl. intros rho. entailer. cancel.
        rewrite Z.lxor_comm in isbyteXOR.
        rewrite UPD_IPAD; try assumption. cancel.
      }
    }

    (*continuation after ipad-loop*)   
    unfold_data_at 2%nat. normalize.
    rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx]). 
    (*extract field-address info before doing anything else*)
       assert_PROP (isptr (field_address t_struct_hmac_ctx_st [StructField _i_ctx]
          (Vptr cb cofs))). entailer.
       apply isptrD in H. destruct H as [cbI [cIoff COffI]]. rewrite COffI in *.
    unfold field_address in COffI.
    remember (field_compatible_dec t_struct_hmac_ctx_st [StructField _i_ctx]
              (Vptr cb cofs)) as s.
    destruct s; simpl in *; inversion COffI. simpl in *. subst cbI. rewrite COffI. clear COffI. 

    (*Call to _SHA256_Init*)
    forward_call' (Vptr cb cIoff).
(*       subst cIoff. 
       unfold nested_field_offset2; simpl. *)

    (*Call to _SHA256_Update*)
    Opaque firstn. 
    forward_call' (init_s256abs, 
            HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad,
            Vptr cb cIoff, Vptr pb pofs, Tsh, 64, kv) ipadSHAabs.
    { assert (FR: Frame = [
        (field_at Tsh t_struct_hmac_ctx_st [StructField _o_ctx] emptySha (Vptr cb cofs));
        (field_at Tsh t_struct_hmac_ctx_st [StructField _md_ctx] emptySha (Vptr cb cofs));
        (data_at Tsh (tarray tuchar 64) (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) (Vptr ckb ckoff));
        data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key)) (Vptr kb kofs) ]).
        subst Frame; reflexivity.
      rewrite FR; clear FR Frame. 
      entailer. cancel.
      unfold data_block. rewrite ZLI. entailer. 
      apply andp_right. 
        simpl. apply prop_right. apply isbyte_map_ByteUnsigned. cancel. 
    }
      { clear Frame HeqPostResetBranch HeqOPADcont; subst IPADcont.
        rewrite Zlength_mkArgZ. repeat rewrite map_length. rewrite mkKey_length. 
        unfold SHA256.BlockSize; simpl. rewrite int_max_unsigned_eq.
        unfold two_power_pos, shift_pos. simpl. omega.
      }
    rename H into ipadAbs_def.
    normalize.
    rewrite firstn_precise in ipadAbs_def.
    Focus 2. specialize (Zlength_mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad); intros. 
            apply coqlib3.Zlength_length in H. rewrite H. repeat rewrite map_length. rewrite mkKey_length. reflexivity.
            repeat rewrite map_length. rewrite mkKey_length. simpl. omega. 
    Transparent firstn. 

    (*essentially the same for opad*)
    eapply semax_seq'. (* TODO: using forward_seq here introduces another Delta0 in goal2 - but 
                          it worked fine before I split this off into file XXX_part2.v *)
     instantiate (1:= 
       (PROP  ()
        LOCAL  (temp _reset (Vint (Int.repr 1));
          lvar _ctx_key (Tarray tuchar 64 noattr) (Vptr ckb ckoff);
          lvar _pad (Tarray tuchar 64 noattr) (Vptr pb pofs);
          temp _ctx (Vptr cb cofs); temp _key (Vptr kb kofs);
          temp _len (Vint (Int.repr l)); gvar sha._K256 kv)
        SEP  (`(K_vector kv);
         `(sha256state_ ipadSHAabs (Vptr cb cIoff));
         `(data_at Tsh (Tarray tuchar 64 noattr) OPADcont (Vptr pb pofs));
         `(field_at Tsh t_struct_hmac_ctx_st [StructField _o_ctx] emptySha (Vptr cb cofs));
         `(field_at Tsh t_struct_hmac_ctx_st [StructField _md_ctx] emptySha (Vptr cb cofs));
         `(data_at Tsh (tarray tuchar 64)
            (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) (Vptr ckb ckoff));
         `(data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key))
            (Vptr kb kofs))))).

    { (*opad loop*) 
      forward_for_simple_bound' 64 (EX i:Z, 
        (PROP  ()
         LOCAL  (temp _reset (Vint (Int.repr 1));
            lvar _ctx_key (Tarray tuchar 64 noattr) (Vptr ckb ckoff);
            lvar _pad (Tarray tuchar 64 noattr) (Vptr pb pofs);
            temp _ctx (Vptr cb cofs); temp _key (Vptr kb kofs);
            temp _len (Vint (Int.repr l)); gvar sha._K256 kv)
         SEP  (`(K_vector kv); `(sha256state_ ipadSHAabs (Vptr cb cIoff));
          `(data_at Tsh (Tarray tuchar 64 noattr) ((FIRSTN i OPADcont)++(SKIPN i IPADcont)) (Vptr pb pofs));
         `(data_at Tsh (tarray tuchar 64)
              (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) (Vptr ckb ckoff));
         `(field_at Tsh t_struct_hmac_ctx_st [StructField _o_ctx] emptySha (Vptr cb cofs));
         `(field_at Tsh t_struct_hmac_ctx_st [StructField _md_ctx] emptySha (Vptr cb cofs));
        `(data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key)) (Vptr kb kofs))))).
      { (*precondition implies "invariant"*)
        clear HeqPostResetBranch.
        unfold data_block. entailer. cancel. 
        unfold SKIPN; simpl. rewrite ZLI; cancel.            
      }
      { unfold normal_ret_assert. simpl. intros rho. entailer. cancel.
        rewrite FIRSTN_precise.
         rewrite SKIPn_short. rewrite app_nil_r.
         cancel.
         do 2 rewrite Zlength_map. unfold HMAC_SHA256.mkArgZ in ZLI; rewrite ZLI. omega. 
         do 2 rewrite Zlength_map. unfold HMAC_SHA256.mkArgZ in ZLO; rewrite ZLO; trivial. 
      }
      { rename H into I. 
        assert (Xb: exists qb, nth (Z.to_nat i) (HMAC_SHA256.mkKey key) Z0 = qb /\ isbyteZ qb).
          { destruct (nth_mapIn (Z.to_nat i) (HMAC_SHA256.mkKey key) 0) as [? [? ?]].
             rewrite mkKey_length.
              split. apply (Z2Nat.inj_le 0); omega. apply (Z2Nat.inj_lt _ 64); omega.
            exists x; split; trivial. eapply Forall_forall. apply isbyteZ_mkKey. eassumption. eassumption.
          }
        destruct Xb as [qb [Qb isbyteZQb]].
        assert (X: Znth i (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) Vundef
                   = Vint (Int.repr qb)). (* (Int.zero_ext 8 q)).*)
          { unfold Znth. destruct (zlt i 0). omega.
            rewrite nth_indep with (d':=Vint (Int.repr 0)).
              Focus 2. repeat rewrite map_length. rewrite mkKey_length. unfold SHA256.BlockSize; simpl. apply (Z2Nat.inj_lt _ 64); omega. 
            repeat rewrite map_nth. rewrite Qb. trivial. 
          }
        forward.
        { entailer. 
          apply prop_right. rewrite X. simpl. rewrite <- isbyte_zeroExt8'; trivial.
                apply (isbyteZ_range _ isbyteZQb). 
        }
        unfold force_val. rewrite sem_cast_i2i_correct_range.
        Focus 2. apply Znth_map_Vint_is_int_I8.
                     apply isbyteZ_mkKey. assumption.
                     rewrite Zlength_correct, mkKey_length. unfold SHA256.BlockSize; simpl; assumption.
        rewrite X.
        forward.
        entailer. cancel. 
        rewrite UPD_OPAD; try assumption. cancel.
      }
    }
    (*continuation after opad-loop*)  
    rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _o_ctx]).
    assert_PROP (isptr (field_address t_struct_hmac_ctx_st [StructField _o_ctx] (Vptr cb cofs))).
    { entailer. }
    apply isptrD in H; destruct H as [cbO [cOoff COffO]]. rewrite COffO in *.
    unfold field_address in COffO.
    remember (field_compatible_dec t_struct_hmac_ctx_st [StructField _o_ctx]
              (Vptr cb cofs)) as s.
    destruct s; simpl in *; inversion COffO; clear COffO. simpl in *. subst cbO cOoff.
   
    (*Call to _SHA256_Init*)  
    (*TODO: one of the most recent changes in floyd (or elsewhere?) meant
    that I have to do the following unfold here t get forward_call' to apply*)
    unfold MORE_COMMANDS, abbreviate. 
    forward_call' (Vptr cb (Int.add cofs (Int.repr 216))).
    
    (* Call to sha_update*)
    (* TODO: investigate the need for the semax_seq_skip. *)
    rewrite -> semax_seq_skip.
    Opaque firstn. 
    forward_call' (init_s256abs, 
            HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Opad,
            Vptr cb (Int.add cofs (Int.repr 216)),
            Vptr pb pofs, Tsh, 64, kv)  opadSHAabs.
    { assert (FR: Frame = [(sha256state_ ipadSHAabs (Vptr cb cIoff));
         (field_at Tsh t_struct_hmac_ctx_st [StructField _md_ctx] emptySha (Vptr cb cofs));
         (data_at Tsh (tarray tuchar 64) (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) (Vptr ckb ckoff));
         (data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key)) (Vptr kb kofs))]).
        subst Frame; reflexivity.
      rewrite FR; clear FR Frame. 
      cancel. unfold data_block. rewrite ZLO.
      entailer. simpl; normalize.
      apply andp_right. 
        simpl. apply prop_right. apply isbyte_map_ByteUnsigned.
      cancel.
    }
    { clear Frame HeqPostResetBranch HeqIPADcont; subst OPADcont.
      rewrite Zlength_mkArgZ. repeat rewrite map_length. rewrite mkKey_length. 
      unfold SHA256.BlockSize; simpl. rewrite int_max_unsigned_eq.
      unfold two_power_pos, shift_pos. simpl. omega.
    } 
    rename H into opadAbs_def.
    normalize.
    rewrite firstn_precise in opadAbs_def.
    Focus 2. specialize (Zlength_mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Opad); intros. 
            apply coqlib3.Zlength_length in H. rewrite H. repeat rewrite map_length. rewrite mkKey_length. reflexivity.
            repeat rewrite map_length. rewrite mkKey_length. simpl. omega. 
    Transparent firstn. 

    subst PostResetBranch; entailer. unfold sha256state_; normalize. rename r into iUpd. rename x into oUpd.
        apply (exp_right (ipadSHAabs,(iUpd,(opadSHAabs,oUpd)))). entailer.
        unfold data_block, initPostResetConditional. simpl.
        rewrite ZLO. entailer. cancel.
        unfold_data_at 3%nat. cancel.
    rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx]).
    rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _o_ctx]).
    unfold field_address. rewrite <- Heqs, <- Heqs0. simpl. cancel.
  }
  { (*ELSE*) 
    forward. subst. unfold initPostKeyNullConditional. entailer. 
    destruct R; subst. 2: discriminate.
    simpl; clear H. destruct key'; try solve[entailer]. 
    unfold hmacstate_PreInitNull, hmac_relate_PreInitNull; simpl.
    destruct h1; entailer.
    destruct (Int.eq i Int.zero); entailer.
    apply (exp_right (iSha, (iCtx v, (oSha, oCtx v)))).
    entailer. cancel.
    unfold hmacstate_PreInitNull, hmac_relate_PreInitNull; simpl.
    apply (exp_right v). apply (exp_right x).
    entailer.
   } 
Qed.
