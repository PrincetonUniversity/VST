Require Import floyd.proofauto.
Import ListNotations.
Require sha.sha.
Require Import sha.SHA256.
Local Open Scope logic.

Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.HMAC_functional_prog.
Require Import sha.spec_hmacNK.
Require Import vst_lemmas.
Require Import hmac_pure_lemmas.
Require Import hmac_common_lemmas.

Require Import sha.hmac_NK.
Require Import sha.verif_hmacNK_init_part1.

(*From Katherine's HMAC_functional_prog_Z*)
Theorem xor_inrange : forall (x y : Z),
                        x = x mod Byte.modulus
                        -> y = y mod Byte.modulus
                        -> Z.lxor x y = (Z.lxor x y) mod Byte.modulus.
Proof.
  intros. symmetry. apply Byte.equal_same_bits. intros.
  assert (ZZ: Z.lxor x y mod Byte.modulus =
        Z.lxor x y mod two_p (Z.of_nat Byte.wordsize)).
        rewrite Byte.modulus_power. reflexivity.
  rewrite ZZ; clear ZZ.     
  rewrite Byte.Ztestbit_mod_two_p; trivial.
  destruct (zlt i (Z.of_nat Byte.wordsize)). trivial. 
  symmetry. rewrite Z.lxor_spec.
  assert (BB: Byte.modulus = two_p (Z.of_nat Byte.wordsize)).
    apply Byte.modulus_power. 
  rewrite BB in H, H0.

  rewrite H; clear H; rewrite H0; clear H0 BB.
   rewrite Byte.Ztestbit_mod_two_p; try omega.
   rewrite Byte.Ztestbit_mod_two_p; try omega.
   destruct (zlt i (Z.of_nat Byte.wordsize)); trivial. omega.
Qed.


Lemma isbyteZ_xor a b: isbyteZ a -> isbyteZ b -> isbyteZ (Z.lxor a b).
Proof. intros. rewrite xor_inrange.
        apply Z_mod_lt. omega.
        symmetry; apply Zmod_small. apply H.
        symmetry; apply Zmod_small. apply H0.
Qed.

Lemma unsigned_repr_isbyte x:
  isbyteZ x -> Int.unsigned (Int.repr x) = x.
Proof. intros; apply Int.unsigned_repr. 
  rewrite int_max_unsigned_eq. destruct H; omega. 
Qed.

Lemma isbyte_mkKey: forall l, Forall isbyteZ l -> Forall isbyteZ (HMAC_SHA256.mkKey l).
Proof. intros.
  unfold HMAC_SHA256.mkKey.
  remember (Zlength l >? Z.of_nat SHA256.BlockSize).
  destruct b.
    apply zeropad_isbyteZ. unfold SHA256.Hash. apply isbyte_sha.
    apply zeropad_isbyteZ; trivial.
Qed.

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

Lemma isbyteZ_range q: isbyteZ q -> 0 <= q <= Byte.max_unsigned. 
Proof. intros B; destruct B. unfold Byte.max_unsigned, Byte.modulus; simpl. omega. Qed.

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
  rewrite common_lemmas.Zlength_map; trivial.
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

Lemma nth_mapIn: forall i (l:list Z) d (Hi: (0 <= i < length l)%nat),
  exists n, nth i l d = n /\ In n l.
Proof. intros i. 
  induction i; simpl; intros.
    destruct l; simpl in *. omega. exists z. split; trivial. left; trivial.
    destruct l; simpl in *. omega.
      destruct (IHi l d) as [? [? ?]]. omega. rewrite H. exists x; split; trivial. right; trivial.
Qed.

Lemma force_lengthn_long {A}: forall n (l:list A) d, (n <= length l)%nat -> force_lengthn n l d = firstn n l.
Proof. induction n; simpl; intros. trivial.
  destruct l; simpl in H. omega.
  rewrite IHn; trivial. omega.
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
           rewrite common_lemmas.firstn_app1.
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
(*                        (array_at tuchar Tsh (tuchars (map Int.repr key)) 0 (Zlength key) (Vptr b ofs)))*)
  | _ => FF
  end.

Lemma init_part2: forall
(Espec : OracleKind)
(c : val)
(k : val)
(l : Z)
(key : list Z)
(KV : val)
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
(ctxkey : val)
(HC : c = Vptr cb cofs)
(R : r = 0 \/ r = 1)
(PostResetBranch : environ -> mpred)
(HeqPostResetBranch : PostResetBranch =
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
                        `(K_vector KV)))))),
@semax Espec Delta
  (PROP  ()
   LOCAL  (`(eq (Vint (Int.repr r))) (eval_id _reset);
   `(eq pad) (eval_var _pad (tarray tuchar 64));
   `(eq (Vptr cb cofs)) (eval_id _ctx); `(eq k) (eval_id _key);
   `(eq (Vint (Int.repr l))) (eval_id _len);
   `(eq ctxkey) (eval_var _ctx_key (tarray tuchar 64));
   `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
   SEP  (`(data_at_ Tsh (tarray tuchar 64) pad);
   `(initPostKeyNullConditional r (Vptr cb cofs) k h1 key ctxkey);
   `(K_vector KV)))
  (Sifthenelse (Etempvar _reset tint)
     (Ssequence
        (Ssequence (Sset _i (Econst_int (Int.repr 0) tint))
           (Sloop
              (Ssequence
                 (Sifthenelse
                    (Ebinop Olt (Etempvar _i tint)
                       (Econst_int (Int.repr 64) tint) tint) Sskip Sbreak)
                 (Ssequence
                    (Sset _aux
                       (Ecast
                          (Ederef
                             (Ebinop Oadd (Evar _ctx_key (tarray tuchar 64))
                                (Etempvar _i tint) (tptr tuchar)) tuchar)
                          tuchar))
                    (Ssequence
                       (Sset _aux
                          (Ecast
                             (Ebinop Oxor (Econst_int (Int.repr 54) tint)
                                (Etempvar _aux tuchar) tint) tuchar))
                       (Sassign
                          (Ederef
                             (Ebinop Oadd (Evar _pad (tarray tuchar 64))
                                (Etempvar _i tint) (tptr tuchar)) tuchar)
                          (Etempvar _aux tuchar)))))
              (Sset _i
                 (Ebinop Oadd (Etempvar _i tint)
                    (Econst_int (Int.repr 1) tint) tint))))
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
                 (Ssequence (Sset _i (Econst_int (Int.repr 0) tint))
                    (Sloop
                       (Ssequence
                          (Sifthenelse
                             (Ebinop Olt (Etempvar _i tint)
                                (Econst_int (Int.repr 64) tint) tint) Sskip
                             Sbreak)
                          (Ssequence
                             (Sset _aux
                                (Ecast
                                   (Ederef
                                      (Ebinop Oadd
                                         (Evar _ctx_key (tarray tuchar 64))
                                         (Etempvar _i tint) (tptr tuchar))
                                      tuchar) tuchar))
                             (Sassign
                                (Ederef
                                   (Ebinop Oadd
                                      (Evar _pad (tarray tuchar 64))
                                      (Etempvar _i tint) (tptr tuchar))
                                   tuchar)
                                (Ebinop Oxor (Econst_int (Int.repr 92) tint)
                                   (Etempvar _aux tuchar) tint))))
                       (Sset _i
                          (Ebinop Oadd (Etempvar _i tint)
                             (Econst_int (Int.repr 1) tint) tint))))
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
           `(EX  h : hmacabs,
             !!hmacInit key h && hmacstate_ h c * initPostKey k key *
             K_vector KV)) (stackframe_of f_HMAC_Init))).
Proof. intros.
forward_if PostResetBranch. 
  { (* THEN*)
    (*remember (cVint (force_int oo ZnthV tuchar (map Vint (map Int.repr 
              (map Byte.unsigned (HMAC_SHA256.mkArg (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad)))))) as IPADcont.
    remember (cVint (force_int oo ZnthV tuchar (map Vint (map Int.repr 
              (map Byte.unsigned (HMAC_SHA256.mkArg (map Byte.repr (HMAC_SHA256.mkKey key)) Opad)))))) as OPADcont.*)
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
    (*remember (ZnthV tuchar (default_val (Tarray tuchar 64 noattr))) as DEFAULTcont.*)
    unfold data_at_, (* tuchars, *) tarray.
    (*erewrite data_at_array_at; try reflexivity. 2: omega.
    rewrite array_at_isptr. *)
    rewrite data_at_isptr. normalize. apply isptrD in H. destruct H as [pb [pofs Hpad]]. subst pad.
    apply semax_pre with (P':=PROP  (r<>0 /\ Forall isbyteZ key)
         LOCAL  (tc_environ Delta;
            `(eq (Vint (Int.repr r))) (eval_id _reset);
            `(eq (Vptr pb pofs)) (eval_var _pad (Tarray tuchar 64 noattr));
            `(eq (Vptr cb cofs)) (eval_id _ctx); `(eq k) (eval_id _key);
            `(eq (Vint (Int.repr l))) (eval_id _len);
            `(eq ctxkey) (eval_var _ctx_key (Tarray tuchar 64 noattr));
            `(eq KV) (eval_var sha._K256 (Tarray tuint 64 noattr)))
         SEP  (`(K_vector KV);
               `(data_at Tsh (Tarray tuchar 64 noattr)
                   (default_val (Tarray tuchar 64 noattr)) (Vptr pb pofs));
(*               `(array_at tuchar Tsh (ZnthV tuchar (default_val (Tarray tuchar 64 noattr)))
                   0 64 (Vptr pb pofs));*)
               `(data_at Tsh t_struct_hmac_ctx_st keyedHMS (Vptr cb cofs));
               `(data_at Tsh (tarray tuchar 64) (map Vint (map Int.repr (HMAC_SHA256.mkKey key)))
                  ctxkey);
               `(data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key)) k))).
               (*`(array_at tuchar Tsh (tuchars (map Int.repr key)) 0 (Zlength key) k))).*)
    { clear HeqPostResetBranch PostResetBranch.
      unfold initPostKeyNullConditional. entailer.
      destruct key'; try contradiction.
      (*integer, ie key==NULL*)
          simpl in TC0. subst i. simpl. if_tac. subst r. inversion H0.
          apply andp_right. entailer. entailer.
      (*key == Vptr*)
       if_tac. subst r.
          unfold typed_true in H0. simpl in H0. inversion H0.
          entailer. cancel.
    }
    (*rewrite (array_at_isptr _ _ _ _ _ k). normalize.*)
    rewrite data_at_isptr with (p:=k). normalize.

    destruct R; subst r. omega. clear H. 
    rename H0 into isbyte_key.
    apply isptrD in H1; destruct H1 as [kb [kofs HK]]; rewrite HK in *.
(*    rewrite data_at_isptr with (p:=ctxkey). normalize.
    apply isptrD in H; destruct H as [ckb [ckofs HCK]]; rewrite HCK in *.*)

    eapply semax_seq'. (* USING forward_seq here introduces another Delta0 in goal2 - but it worked fine before I split this off into file XXX_part2.v *)
    instantiate (1:= 
  (PROP  ()
   LOCAL  ( `(eq (Vint (Int.repr 1))) (eval_id _reset);
   `(eq (Vptr pb pofs)) (eval_var _pad (Tarray tuchar 64 noattr));
   `(eq (Vptr cb cofs)) (eval_id _ctx); `(eq (Vptr kb kofs)) (eval_id _key);
   `(eq (Vint (Int.repr l))) (eval_id _len);
   `(eq ctxkey) (eval_var _ctx_key (Tarray tuchar 64 noattr));
   `(eq KV) (eval_var sha._K256 (Tarray tuint 64 noattr)))
   SEP  (`(K_vector KV);
   `(data_at Tsh (Tarray tuchar 64 noattr) IPADcont (Vptr pb pofs));
   `(data_at Tsh t_struct_hmac_ctx_st keyedHMS (Vptr cb cofs));
   `(data_at Tsh (tarray tuchar 64)
       (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) ctxkey);
   `(data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key))
       (Vptr kb kofs))))).
    { (*ipad loop*)
      forward_for_simple_bound' 64 (EX i:Z, 
        (PROP  ()
         LOCAL  (`(eq (Vint (Int.repr 1))) (eval_id _reset);
                 `(eq (Vptr pb pofs)) (eval_var _pad (tarray tuchar 64));
                 `(eq (Vptr cb cofs)) (eval_id _ctx);
                 `(eq (Vptr kb kofs)) (eval_id _key);
                 `(eq ctxkey) (eval_var _ctx_key (Tarray tuchar 64 noattr));
                 `(eq (Vint (Int.repr l))) (eval_id _len);
                 `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
         SEP  (`(K_vector KV);
          `(data_at Tsh (Tarray tuchar 64 noattr) (FIRSTN i IPADcont) (Vptr pb pofs));
(*          `(data_at Tsh (Tarray tuchar i noattr) IPADcont (Vptr pb pofs));
          `(data_at Tsh (Tarray tuchar (64 - i) noattr) (default_val (Tarray tuchar (64 - i) noattr))
             (offset_val (Int.repr i) (Vptr pb pofs)));*)
          `(data_at Tsh t_struct_hmac_ctx_st keyedHMS (Vptr cb cofs));
         `(data_at Tsh (tarray tuchar 64)
              (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) ctxkey);
        `(data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key))
           (Vptr kb kofs))))).
      { (*precondition implies "invariant"*)
        clear HeqPostResetBranch.
        entailer. (*cancel. 
        rewrite data_Tarray_array_at_emp. 
        specialize (Tarray_emp_field_compatible pb pofs); intros. entailer.*)
      } 
      { unfold normal_ret_assert. simpl. intros rho. entailer. cancel.
        rewrite FIRSTN_precise. cancel.
         do 2 rewrite common_lemmas.Zlength_map. apply ZLI. 
         (* data_Tarray_array_at_emp. entailer.*)
      }
      { (*unfold_data_at 3%nat. normalize. 
        rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _key]); try reflexivity.
        normalize.*)
        rename H into I. 
        (*unfold_data_at 1%nat. normalize.
        rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [_key]); try reflexivity.
        normalize. rename H0 into SCc. rename H1 into ACc.
        rewrite at_offset'_eq.
        2: simpl; rewrite Int.add_zero; reflexivity.*)
(*        eapply semax_pre0; [ apply now_later | ].
        eapply semax_post_flipped'.*)
        subst PostResetBranch.
        assert (Xb: exists qb, nth (Z.to_nat i) (HMAC_SHA256.mkKey key) Z0 = qb /\ isbyteZ qb).
          { destruct (nth_mapIn (Z.to_nat i) (HMAC_SHA256.mkKey key) 0) as [? [? ?]].
             rewrite mkKey_length.
              split. apply (Z2Nat.inj_le 0); omega. apply (Z2Nat.inj_lt _ 64); omega.
            exists x; split; trivial. eapply Forall_forall. apply isbyte_mkKey. eassumption. eassumption.
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
                     apply isbyte_mkKey. assumption.
                     rewrite Zlength_correct, mkKey_length. unfold SHA256.BlockSize; simpl; assumption.
        rewrite X.
        forward.
        normalize. subst x. unfold Int.xor. 
        rewrite Int.unsigned_repr. 2: rewrite int_max_unsigned_eq; omega.
        rewrite Int.unsigned_repr. 2: destruct isbyteZQb; rewrite int_max_unsigned_eq; omega.
        exploit (isbyteZ_xor 54 qb); trivial. split; omega.
        intros isbyteXOR.
        rewrite <- isbyte_zeroExt8; trivial.
        (*unfold_data_at 2%nat.
        erewrite field_at_Tarray. 2: reflexivity. 2: apply JMeq.JMeq_refl. 
        rewrite split2_array_at with (mid:=1). 2: omega.
        normalize.*)
        rewrite Z.lxor_comm. remember (Vint (Int.repr (Z.lxor qb 54))) as xorval.
        forward. simpl. intros rho. entailer. cancel.
        rewrite Z.lxor_comm in isbyteXOR.
        rewrite UPD_IPAD; try assumption. cancel. 
      }
    }

    (*continuation after ipad-loop*)   
    unfold_data_at 2%nat. normalize.
    rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx]).
    simpl. 
    rewrite data_at_isptr. normalize. 
    apply isptrD in H. destruct H as [cbI [cIoff COffI]]. rewrite COffI in *.
    unfold field_address in COffI.
    remember (field_compatible_dec t_struct_hmac_ctx_st [StructField _i_ctx]
              (Vptr cb cofs)) as s.
    destruct s; simpl in *; inversion COffI. simpl in *. subst cbI. rewrite COffI. clear COffI.
(*
    rewrite at_offset'_eq.
    2: simpl; rewrite Int.add_zero; reflexivity.*)
    eapply semax_seq'.
myframe_SEP'' [0].
(*    frame_SEP 0.*)
    forward_call (Vptr cb cIoff). (*(Int.add cofs (Int.repr 108))).*)
    { assert (FR: Frame = nil).
        subst Frame. reflexivity.
      rewrite FR. clear FR Frame.
      entailer.
      (*apply (exp_right emptySha). entailer. *)
    }
    after_call. simpl. normalize. 

    eapply semax_seq'.
(* myframe_SEP'' [0; 3; 6].*)
 myframe_SEP'' [0; 3; 4].
    remember (init_s256abs, 
            HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad,
            Vptr cb cIoff, (*(Int.add cofs (Int.repr 108)),*)
            Vptr pb pofs, Tsh, 64, KV) as WITNESS.
    forward_call WITNESS.
    { assert (FR: Frame = nil).
        subst Frame. reflexivity.
      rewrite FR. clear FR Frame. 
      subst WITNESS. entailer. rewrite <- H0. entailer. (*clear HeqPostResetBranch.*)
      unfold data_block. rewrite ZLI. cancel.
      entailer.
      apply andp_right. 
        simpl. apply prop_right. apply isbyte_map_ByteUnsigned. cancel. (*
      apply array_lemmas.array_at_ext'.
      unfold tuchars, cVint, ZnthV; simpl. intros. if_tac. omega. simpl. 
      destruct (nth_mapVintZ i 
           (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad)) as [n Hn].
        rewrite ZLI; assumption.
      rewrite Hn. unfold HMAC_SHA256.mkArgZ in Hn; rewrite Hn. trivial.*)
    }
    after_call. simpl. intros rho. subst WITNESS. rewrite firstn_precise. normalize.
      unfold HMAC_SHA256.mkArgZ, HMAC_SHA256.mkArg. repeat rewrite map_length.
      unfold HMAC_SHA256.sixtyfour. rewrite combine_length, map_length, length_list_repeat, mkKey_length.
      unfold SHA256.BlockSize; simpl. trivial.

    simpl.
    apply semax_pre with (P':=EX x : s256abs,
  (PROP  (update_abs
          (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad)
          init_s256abs x)
   LOCAL  (
      `(eq (Vint (Int.repr 1))) (eval_id _reset);
      `(eq (Vptr pb pofs)) (eval_var _pad (Tarray tuchar 64 noattr));
      `(eq (Vptr cb cofs)) (eval_id _ctx); `(eq (Vptr kb kofs)) (eval_id _key);
      `(eq (Vint (Int.repr l))) (eval_id _len);
      `(eq ctxkey) (eval_var _ctx_key (Tarray tuchar 64 noattr));
      `(eq KV) (eval_var sha._K256 (Tarray tuint 64 noattr)))
   SEP  (`(K_vector KV); `(sha256state_ x (Vptr cb cIoff));
         `(data_block Tsh
            (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad)
            (Vptr pb pofs));
        `(field_at Tsh t_struct_hmac_ctx_st [StructField _o_ctx] emptySha
            (Vptr cb cofs));
        `(field_at Tsh t_struct_hmac_ctx_st [StructField _md_ctx] emptySha
            (Vptr cb cofs));
        `(data_at Tsh (tarray tuchar 64)
            (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) ctxkey);
        `(data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key))
           (Vptr kb kofs))))).
    entailer. eapply (exp_right x). entailer.
    apply extract_exists_pre. intros ipadSHAabs.
(*    rename H into SCc.
    rename H0 into ACc.*)
    normalize. simpl. normalize. rename H into ipadAbs_def.
(*
    rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [_o_ctx]); try reflexivity.
    normalize.
    rewrite at_offset'_eq.
    2: simpl; rewrite Int.add_zero; reflexivity. unfold offset_val; simpl.
*)

    (*essentially the same for opad*)
    eapply semax_seq'. (* USING forward_seq here introduces another Delta0 in goal2 - but it worked fine before I split this off into file XXX_part2.v *)
    instantiate (1:= 
  (PROP  ()
   LOCAL  (`(eq (Vint (Int.repr 1))) (eval_id _reset);
   `(eq (Vptr pb pofs)) (eval_var _pad (Tarray tuchar 64 noattr));
   `(eq (Vptr cb cofs)) (eval_id _ctx); `(eq (Vptr kb kofs)) (eval_id _key);
   `(eq (Vint (Int.repr l))) (eval_id _len);
   `(eq ctxkey) (eval_var _ctx_key (Tarray tuchar 64 noattr));
   `(eq KV) (eval_var sha._K256 (Tarray tuint 64 noattr)))
   SEP  (`(K_vector KV);
   `(sha256state_ ipadSHAabs (Vptr cb cIoff));

   `(data_at Tsh (Tarray tuchar 64 noattr) OPADcont (Vptr pb pofs));

   `(field_at Tsh t_struct_hmac_ctx_st [StructField _o_ctx] emptySha (Vptr cb cofs));
(*   `(data_at Tsh (nested_field_type2 t_struct_hmac_ctx_st [StructField _o_ctx]) emptySha
       (Vptr cb
          (Int.add cofs
             (Int.repr (nested_field_offset2 t_struct_hmac_ctx_st [StructField _o_ctx])))));*)
   `(field_at Tsh t_struct_hmac_ctx_st [StructField _md_ctx] emptySha (Vptr cb cofs));
   `(data_at Tsh (tarray tuchar 64)
       (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) ctxkey);

   `(data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key))
       (Vptr kb kofs))))).

    { (*opad loop*) 
      forward_for_simple_bound' 64 (EX i:Z, 
        (PROP  ()
         LOCAL  (`(eq (Vint (Int.repr 1))) (eval_id _reset);
                 `(eq (Vptr pb pofs)) (eval_var _pad (tarray tuchar 64));
                 `(eq (Vptr cb cofs)) (eval_id _ctx);
                 `(eq (Vptr kb kofs)) (eval_id _key);
                 `(eq ctxkey) (eval_var _ctx_key (Tarray tuchar 64 noattr));
                 `(eq (Vint (Int.repr l))) (eval_id _len);
                 `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
         SEP  (`(K_vector KV); `(sha256state_ ipadSHAabs (Vptr cb cIoff));
          `(data_at Tsh (Tarray tuchar 64 noattr) ((FIRSTN i OPADcont)++(SKIPN i IPADcont)) (Vptr pb pofs));

         `(data_at Tsh (tarray tuchar 64)
              (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) ctxkey);

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
         do 2 rewrite common_lemmas.Zlength_map. unfold HMAC_SHA256.mkArgZ in ZLI; rewrite ZLI. omega. 
         do 2 rewrite common_lemmas.Zlength_map. unfold HMAC_SHA256.mkArgZ in ZLO; rewrite ZLO; trivial. 
      }
      { (*unfold_data_at 3%nat. normalize. 
        rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _key]); try reflexivity.
        normalize.*)
        rename H into I. 
        (*unfold_data_at 1%nat. normalize.
        rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [_key]); try reflexivity.
        normalize. rename H0 into SCc. rename H1 into ACc.
        rewrite at_offset'_eq.
        2: simpl; rewrite Int.add_zero; reflexivity.*)
(*        eapply semax_pre0; [ apply now_later | ].
        eapply semax_post_flipped'.*)
        assert (Xb: exists qb, nth (Z.to_nat i) (HMAC_SHA256.mkKey key) Z0 = qb /\ isbyteZ qb).
          { destruct (nth_mapIn (Z.to_nat i) (HMAC_SHA256.mkKey key) 0) as [? [? ?]].
             rewrite mkKey_length.
              split. apply (Z2Nat.inj_le 0); omega. apply (Z2Nat.inj_lt _ 64); omega.
            exists x; split; trivial. eapply Forall_forall. apply isbyte_mkKey. eassumption. eassumption.
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
                     apply isbyte_mkKey. assumption.
                     rewrite Zlength_correct, mkKey_length. unfold SHA256.BlockSize; simpl; assumption.
        rewrite X.
        forward.
        normalize. simpl. intros rho; entailer. cancel. (* 200MB memory consumption in this line!*)
        rewrite UPD_OPAD; try assumption. cancel.
      }
    }
    (*continuation after opad-loop*)   
    (*unfold_data_at 1%nat.*) (*normalize.*)
    rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _o_ctx]).
    simpl.
    (*Does not work ie normalize removes the ispointer again
    rewrite (data_at_isptr Tsh (nested_field_type2 t_struct_hmac_ctx_st [StructField _o_ctx])).
    normalize. *)
    apply semax_pre with (P':=
  (PROP  (isptr
         (field_address t_struct_hmac_ctx_st [StructField _o_ctx]
            (Vptr cb cofs)))
   LOCAL  (`(eq (Vint (Int.repr 1))) (eval_id _reset);
   `(eq (Vptr pb pofs)) (eval_var _pad (Tarray tuchar 64 noattr));
   `(eq (Vptr cb cofs)) (eval_id _ctx); `(eq (Vptr kb kofs)) (eval_id _key);
   `(eq (Vint (Int.repr l))) (eval_id _len);
   `(eq ctxkey) (eval_var _ctx_key (Tarray tuchar 64 noattr));
   `(eq KV) (eval_var sha._K256 (Tarray tuint 64 noattr)))
   SEP  (`(K_vector KV); `(sha256state_ ipadSHAabs (Vptr cb cIoff));
   `(data_at Tsh (Tarray tuchar 64 noattr) OPADcont (Vptr pb pofs));
   `(data_at Tsh
       (nested_field_type2 t_struct_hmac_ctx_st [StructField _o_ctx])
       emptySha
       (field_address t_struct_hmac_ctx_st [StructField _o_ctx]
          (Vptr cb cofs)));
   `(field_at Tsh t_struct_hmac_ctx_st [StructField _md_ctx] emptySha
       (Vptr cb cofs));
   `(data_at Tsh (tarray tuchar 64)
       (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) ctxkey);
   `(data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key))
       (Vptr kb kofs))))).
    { entailer. }

    remember (isptr
      (field_address t_struct_hmac_ctx_st [StructField _o_ctx] (Vptr cb cofs))) as PR. normalize.
    subst PR.
    apply isptrD in H. destruct H as [cbO [cOoff COffO]]. rewrite COffO in *.
    unfold field_address in COffO.
    remember (field_compatible_dec t_struct_hmac_ctx_st [StructField _o_ctx]
              (Vptr cb cofs)) as s.
    destruct s; simpl in *; inversion COffO. simpl in *. subst cbO. rewrite COffO. clear COffO.
(*
    rewrite at_offset'_eq.
    2: simpl; rewrite Int.add_zero; reflexivity.*)
    eapply semax_seq'.
 myframe_SEP'' [3].
    forward_call (Vptr cb cOoff). (*(Int.add cofs (Int.repr 216))).*)
    { assert (FR: Frame = nil).
        subst Frame. reflexivity.
      rewrite FR. clear FR Frame. 
      entailer. (*apply (exp_right emptySha). entailer. *)
    }
    after_call. simpl. normalize.

    (*unfold MORE_COMMANDS, abbreviate. WHY IS THIS NOW DONE AUTOMATICALLY?*)
(*    make_sequential.
    frame_SEP 0 1 3.*)
    remember (init_s256abs, 
            HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Opad,
            Vptr cb cOoff,
            Vptr pb pofs, Tsh, 64, KV) as WITNESS.
    forward_call WITNESS.
    { assert (FR: Frame = [`(sha256state_ ipadSHAabs (Vptr cb cIoff));
        `(field_at Tsh t_struct_hmac_ctx_st [StructField _md_ctx] emptySha (Vptr cb cofs));
       `(data_at Tsh (tarray tuchar 64) (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) ctxkey);
       `(data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key)) (Vptr kb kofs))]).
(*         `(sha256state_ ipadSHAabs (Vptr cb (Int.add cofs (Int.repr 108))));
         `(field_at Tsh t_struct_hmac_ctx_st [_md_ctx] emptySha (Vptr cb cofs));
         `(data_at Tsh (tarray tuchar 64)
            (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) (Vptr ckb ckofs));
         `(array_at tuchar Tsh (tuchars (map Int.repr key)) 0 (Zlength key)
              (Vptr kb kofs))]). *)
        subst Frame. reflexivity.
      rewrite FR. clear FR Frame. 
      subst WITNESS. entailer.
      apply andp_right. apply prop_right. rewrite <- H0; trivial.
      cancel. unfold data_block. rewrite ZLO.
      entailer.
      apply andp_right. 
        simpl. apply prop_right. apply isbyte_map_ByteUnsigned.
      cancel.
    }
    after_call. simpl. intros rho. subst WITNESS PostResetBranch.
        rewrite firstn_precise. entailer.
        rename x into opadSHAabs.
        unfold sha256state_; normalize. rename r into iUpd. rename x into oUpd.
        apply exp_right with (x:=ipadSHAabs). entailer.
        apply exp_right with (x:=iUpd). entailer.
        apply exp_right with (x:=opadSHAabs). entailer.
        apply exp_right with (x:=oUpd). entailer.
        unfold data_block, initPostResetConditional. simpl.
        rewrite ZLO. entailer. cancel.
        unfold_data_at 3%nat. cancel.
    rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx]).
    rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _o_ctx]).
    unfold field_address. rewrite <- Heqs, <- Heqs0. simpl. cancel.

    rewrite <- ZLO. rewrite Zlength_correct. symmetry; apply Nat2Z.id.
  }
  { (*ELSE*) 
    forward. unfold overridePost. simpl. intros rho. apply andp_right. apply prop_right. trivial.
    subst. unfold initPostKeyNullConditional; simpl. entailer.
    rewrite <- H1 in *; simpl in *. unfold typed_false in H0. simpl in H0.
        inversion H0; clear H0. apply negb_false_iff in H6.
        apply eq_sym in H6; apply binop_lemmas.int_eq_true in H6.
    destruct R; subst. simpl.
      remember (eval_id _key rho) as k. destruct k; entailer. 
      remember (Int.eq i Int.zero) as d. destruct d. 2: entailer.
      unfold hmacstate_PreInitNull, hmac_relate_PreInitNull; simpl.
      destruct h1; entailer.
       apply exp_right with (x:= iSha). 
       apply exp_right with (x:= (iCtx r)).
       apply exp_right with (x:= oSha).
       apply exp_right with (x:= (oCtx r)).
       entailer. rewrite <- Heqd. cancel.
       unfold hmacstate_PreInitNull, hmac_relate_PreInitNull; simpl.
(*       apply sepcon_derives. unfold tarray. rewrite data_at__array_at_. cancel. omega. reflexivity.        *)
       apply exp_right with (x:= r). apply exp_right with (x:=v).
       entailer. 
     simpl. apply Int.one_not_zero in H6. contradiction.
   } 
Qed.
