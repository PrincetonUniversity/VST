Require Import floyd.proofauto.

Import ListNotations.
Local Open Scope logic.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha_lemmas.
Require Import sha.HMAC_functional_prog.

Lemma skipn_app2:
 forall A n (al bl: list A),
  (n >= length al)%nat ->
  skipn n (al++bl) = skipn (n-length al) bl.
Proof.
intros. revert al H;
induction n; destruct al; intros; simpl in *; try omega; auto.
apply IHn; omega.
Qed. 

Lemma firstn_app1: forall {A} n (p l: list A),
  (n <= Datatypes.length p)%nat ->
   firstn n (p ++ l) = firstn n p.
Proof. intros A n.
induction n; simpl; intros. trivial.
  destruct p; simpl in H. omega.
  apply le_S_n in H. simpl. f_equal. auto. 
Qed.  

Lemma firstn_app2: forall {A} n (p l: list A),
  (n > Datatypes.length p)%nat ->
   firstn n (p ++ l) = p ++ (firstn (n-Datatypes.length p) l).
Proof. intros A n.
induction n; simpl; intros. 
  destruct p; simpl in *. trivial. omega.
  destruct p; simpl in *. trivial.
  rewrite IHn. trivial. omega. 
Qed.  

Lemma firstn_map {A B} (f:A -> B): forall n l, 
      firstn n (map f l) = map f (firstn n l).
Proof. intros n.
induction n; simpl; intros. trivial.
  destruct l; simpl. trivial.
  rewrite IHn. trivial.
Qed.

Lemma firstn_combine {A}: forall n (l k: list A), 
      firstn n (combine l k) = combine (firstn n l) (firstn n k).
Proof. intros n.
induction n; simpl; intros. trivial.
  destruct l; simpl. trivial.
  destruct k; simpl. trivial.
  rewrite IHn. trivial.
Qed.

Lemma firstn_precise {A}: forall n (l:list A), length l = n -> 
      firstn n l = l.
Proof. intros n. 
  induction n; intros; destruct l; simpl in *; trivial.
    inversion H.
    rewrite IHn; trivial. inversion H; trivial.
Qed. 

Lemma first64_sixtyfour {A} (a:A): 
      firstn 64 (HMAC_SHA256.sixtyfour a) = HMAC_SHA256.sixtyfour a.
Proof. apply firstn_precise. simpl. reflexivity. Qed. 

Lemma length_Nlist {A} (i:A): forall n, length (HMAC_SHA256.Nlist i n) = n.
Proof. induction n; simpl; auto. Qed.

Lemma length_SF {A} (x:A): length (HMAC_SHA256.sixtyfour x) = 64%nat.
Proof. unfold HMAC_SHA256.sixtyfour. rewrite length_Nlist; trivial. Qed.

Lemma str_to_Z_length: forall k, 
      String.length k = length (str_to_Z k).
Proof. intros. induction k; simpl; auto. Qed.
  
Lemma Zlength_mkArgZ k pad: Zlength (HMAC_SHA256.mkArgZ k pad) = Z.of_nat (min (length k) 64).
Proof. intros. repeat rewrite Zlength_correct.
   unfold HMAC_SHA256.mkArgZ, HMAC_SHA256.mkArg, HMAC_SHA256.sixtyfour.
   repeat rewrite map_length. 
   rewrite combine_length, length_Nlist. trivial.
Qed. 

Lemma In_Nlist {A:Type}: forall (n:A) l x, In x (HMAC_SHA256.Nlist n l) -> x=n.
Proof. intros n l.
  induction l; simpl; intros. contradiction.
  destruct H; eauto.
Qed.
Lemma zeropad_isbyteZ: forall l, Forall isbyteZ l -> Forall isbyteZ (HMAC_SHA256.zeroPad l).
Proof. unfold isbyteZ, HMAC_SHA256.zeroPad; intros.
  rewrite Forall_forall in *. intros.
  apply in_app_or in H0.
  destruct H0. apply (H _ H0).
  apply In_Nlist in H0. subst; omega.
Qed.
Lemma mapnth': forall {A B : Type} (f : A -> B) (l : list A) (d : A) (n : nat) fd,
      fd = f d -> nth n (map f l) fd = f (nth n l d).
Proof. intros; subst. apply map_nth. Qed.

Lemma unsigned_Brepr_isbyte z: isbyteZ z -> Byte.unsigned (Byte.repr z) = z.
Proof. intros. 
      unfold isbyteZ in H. apply Byte.unsigned_repr.
      unfold Byte.max_unsigned, Byte.modulus. simpl. omega.
Qed.  

Lemma map_unsigned_Brepr_isbyte: forall l, Forall isbyteZ l ->
      map Byte.unsigned (map Byte.repr l) = l.
Proof. intros. induction l; simpl in *. trivial.
   rewrite IHl. rewrite Forall_forall in H. 
   assert (In a (a::l)). left. trivial. 
   specialize (H _ H0); clear H0.
   rewrite unsigned_Brepr_isbyte; trivial.
   rewrite Forall_forall in *. intros. apply H. right; trivial.
Qed.

Lemma Ztest_Bytetest:
 forall a, Z.testbit (Byte.unsigned a) = Byte.testbit a.
Proof. reflexivity. Qed.
Hint Rewrite Ztest_Bytetest : testbit.

Lemma nthD_1 {A B}: forall (f: A ->B) n l d fx dd, (n < length l)%nat ->
      nth n (map f l) d = fx -> 
      exists x, In x l /\ nth n l dd = x /\ f x = fx.
Proof. intros f n.
  induction n; simpl; intros.
    destruct l; simpl in *. omega.
      exists a; split. left; trivial. split; trivial.
    destruct l; simpl in *. omega. 
    destruct (IHn l d fx dd) as [? [? [? ?]]]. omega. trivial.
    exists x; eauto.
Qed.

Lemma sepcon_fold: forall Frame P rho, 
Frame = cons `(P) nil ->
P |-- fold_right
      (fun (P Q : environ -> mpred) (rho0 : environ) => P rho0 * Q rho0) 
      `emp Frame rho.
Proof. intros. subst. simpl. entailer. Qed.

Lemma nth_mapVint: forall i (l:list Z) (Hi: (0 <= i < length l)%nat),
  exists n, nth i (map Vint (map Int.repr l)) Vundef = Vint n.
Proof. intros i. 
  induction i; simpl; intros.
    destruct l; simpl in *. omega. eexists; reflexivity.
    destruct l; simpl in *. omega.
      destruct (IHi l). omega. rewrite H. eexists; reflexivity.
Qed.

Lemma nth_mapVint' {z}: forall i (l:list Z)
  (Hi: (0 <= i < length l)%nat),
  nth i (map Vint (map Int.repr l)) Vundef = 
  Vint (Int.repr (nth i l z)).
Proof. intros i. 
  induction i; simpl; intros.
    destruct l; simpl in *. omega. trivial.
    destruct l; simpl in *. omega.
      rewrite (IHi l). trivial. omega.
Qed.

Lemma nth_mapVintZ: forall i (l:list Z) (Hi: 0 <= i < Zlength l),
  exists n, nth (Z.to_nat i) (map Vint (map Int.repr l)) Vundef = Vint n.
Proof. intros.
  eapply nth_mapVint. rewrite Zlength_correct in Hi.
  destruct Hi; split.   omega. 
unfold Z.of_nat in H0. unfold Z.to_nat.
destruct l; simpl in *. omega.
destruct i; try omega.
rewrite <- SuccNat2Pos.id_succ.
apply Pos2Nat.inj_lt.
apply H0.
Qed.

Lemma nth_Nlist {A}: forall (a d:A) k i (Hik: (i <k)%nat),
      nth i (HMAC_SHA256.Nlist a k) d = a.
Proof. intros a d k.
  induction k; simpl. 
    intros. omega.
  intros. destruct i; simpl. trivial. 
   apply IHk. omega.
Qed. 

Lemma map_Nlist: forall {A B} a (f:A -> B) n,
                 map f (HMAC_SHA256.Nlist a n) = HMAC_SHA256.Nlist (f a) n.
Proof. intros. induction n; simpl; trivial. rewrite IHn. trivial. Qed.

Lemma minus_lt_compat_r: forall n m p : nat,
      (n < m)%nat -> (p <= n)%nat -> (n - p < m - p)%nat.
Proof. intros. unfold lt in *. omega. Qed.

  Lemma map_nth_error_inv {A B}: forall n (l:list A) (f: A -> B) fd,
    nth_error (map f l) n = Some fd -> exists d, nth_error l n = Some d /\ fd = f d.
  Proof. intros n.
    induction n; intros l.
     destruct l; simpl; intros. inversion H.
       inversion H. exists a. split; trivial.
     destruct l; simpl; intros. inversion H.
       eapply IHn. apply H.
  Qed.
  Lemma nth_error_app {A}: forall n (l:list A) d,
    nth_error l n = Some d -> forall ll, nth_error (l ++ ll) n = Some d.
  Proof. intros n.
    induction n; intros l.
     destruct l; simpl; intros. inversion H. trivial.
     destruct l; simpl; intros. inversion H.
       eapply IHn. apply H.
  Qed.

Lemma isByte_ByteUnsigned b: isbyteZ (Byte.unsigned b).
Proof.
  unfold Byte.unsigned, Byte.intval. destruct b.
  unfold Byte.modulus, Byte.wordsize, Wordsize_8.wordsize in intrange.
  rewrite two_power_nat_correct in intrange.
  unfold Zpower_nat in intrange. simpl in intrange. unfold isbyteZ. omega.
Qed.

Lemma nth_zeropad_left {d d'}: forall l i (I: 0<= i < Zlength l),
      nth (Z.to_nat i) (HMAC_SHA256.zeroPad l) d = nth (Z.to_nat i) l d'.
Proof. unfold HMAC_SHA256.zeroPad. intros.
  destruct I.
  apply Z2Nat.inj_lt in H0; try omega.
  rewrite Zlength_correct, Nat2Z.id in H0.
  rewrite app_nth1; trivial.
  apply nth_indep; trivial. 
Qed.

Lemma mkKey_left {d d'}: forall l (L: false = (Zlength l >? 64)) 
        i (I: 0<= i < Zlength l),
      nth (Z.to_nat i) (HMAC_SHA256.mkKey l) d = nth (Z.to_nat i) l d'.
Proof.
  unfold HMAC_SHA256.mkKey. intros. simpl. rewrite <- L.
  apply nth_zeropad_left; trivial.
Qed.
Lemma nth_zeropad_right {d}: forall l i (I: Zlength l <= i < 64),
      nth (Z.to_nat i) (HMAC_SHA256.zeroPad l) d = Z0.
Proof. unfold HMAC_SHA256.zeroPad. intros.
  rewrite app_nth2. rewrite nth_Nlist. trivial.
  apply minus_lt_compat_r. destruct I. apply Z2Nat.inj_lt in H0. apply H0.
  specialize (initial_world.zlength_nonneg _ l). omega.
  omega.
  destruct I. apply Z2Nat.inj_le in H. rewrite Zlength_correct, Nat2Z.id in H. apply H.
  apply(initial_world.zlength_nonneg _ l).
  specialize (initial_world.zlength_nonneg _ l). omega. 
  destruct I. apply Z2Nat.inj_le in H. rewrite Zlength_correct, Nat2Z.id in H. apply H.
  apply(initial_world.zlength_nonneg _ l). 
  specialize (initial_world.zlength_nonneg _ l). omega.  
Qed.
Lemma mkKey_right {d}: forall l (L: false = (Zlength l >? 64)) 
        i (I: Zlength l <= i < 64),
      nth (Z.to_nat i) (HMAC_SHA256.mkKey l) d = Z0.
Proof.
  unfold HMAC_SHA256.mkKey. intros. simpl. rewrite <- L.
  apply nth_zeropad_right; trivial.
Qed.

Lemma Forall_app {A} p (l1 l2: list A): Forall p (l1 ++ l2) <-> (Forall p l1 /\ Forall p l2).
Proof. intros. repeat  rewrite Forall_forall. 
  split; intros.
    split; intros; apply H; apply in_or_app. left; trivial. right; trivial.
  apply in_app_or in H0. destruct H. destruct H0; eauto.
Qed. 

Lemma isbyte_map_ByteUnsigned l: Forall isbyteZ (map Byte.unsigned l).
Proof. 
  rewrite Forall_forall. intros. 
  apply list_in_map_inv in H. destruct H as [b [B1 _]]. subst x.
  apply isByte_ByteUnsigned.
Qed.

(*Same proof as semax_loadstore_array*)
Lemma NEWsemax_loadstore_array:
  forall {Espec: OracleKind},
 forall n k vi lo hi t1 (contents: Z -> reptype t1) v1 v2 (Delta: tycontext) e1 ei e2 sh P Q R, 
  (*H0*) reptype t1 = val -> 
  (*H1*) type_is_by_value t1 ->
  (*H2*) legal_alignas_type t1 = true ->
  (*H3*) typeof e1 = tarray t1 k->
  (*H4*) typeof ei = tint ->
  (*H8*) PROPx P (LOCALx Q (SEPx R)) |--  rel_expr e1 v1 && rel_expr ei (Vint (Int.repr vi))
           && rel_expr (Ecast e2 t1) v2 ->
  (*H7*) nth_error R n = Some (`(array_at t1 sh contents lo hi v1)) ->
  (*H *) writable_share sh ->
  (*H5*) tc_val t1 v2 ->
  (*H6*) in_range lo hi vi ->
   @semax Espec Delta (|> PROPx P (LOCALx Q (SEPx R))) (Sassign (Ederef (Ebinop Oadd e1 ei (tptr t1)) t1) e2) 
          (normal_ret_assert 
           (PROPx P (LOCALx Q (SEPx 
            (replace_nth n R `(array_at t1 sh (upd contents vi (valinject _ v2)) lo hi v1)))))).
Proof. 
intros until R.
intros H0 H1 H2 H3 H4 H8 H7 H H5 H6.
eapply semax_post_flipped'.
apply semax_loadstore_array'; eauto.
apply derives_trans with (!! isptr v1 && PROPx P (LOCALx Q (SEPx R))).
rewrite (SEP_nth_isolate _ _ _ H7).
repeat rewrite <- insert_SEP.
rewrite array_at_isptr. normalize.
normalize.
destruct v1; try contradiction.
instantiate (2:=v1).
simpl eval_binop. rewrite mul_repr.
apply andp_right; auto.
eapply derives_trans; [ apply H8 |].
intro rho. simpl.
repeat apply andp_right.
apply rel_lvalue_deref.
eapply rel_expr_binop.
repeat apply andp_left1. apply derives_refl.
apply andp_left1. apply andp_left2. apply derives_refl.
intro; rewrite H4; simpl. rewrite H3; simpl. 
  unfold Cop.sem_add; simpl. rewrite mul_repr. auto.
 apply andp_left2. auto.
rewrite (SEP_nth_isolate _ _ _ H7).
repeat rewrite <- insert_SEP.
apply derives_refl.
rewrite (SEP_replace_nth_isolate _ _ _ `(array_at t1 sh (upd contents vi (valinject t1 v2)) lo hi v1) H7).
rewrite insert_SEP.
auto.
Qed.

Lemma array_at_local_facts':
  forall (t : type) (sh : Share.t) (f : Z -> reptype t) (lo hi : Z) (v : val),
  array_at t sh f lo hi v |-- array_at t sh f lo hi v && !!isptr v && !!offset_in_range (sizeof t * lo) v &&
!!offset_in_range (sizeof t * hi) v && !!align_compatible t v.
Proof. intros. unfold array_at. entailer. Qed.


Lemma split_offset_array_at_: forall (ty : type) (sh : Share.t) 
         (z lo hi : Z) (v : val),
       z <= lo <= hi ->
       sizeof ty > 0 ->
       legal_alignas_type ty = true ->
       array_at_ ty sh z hi v =
       !! offset_in_range (sizeof ty * z) v &&
       !! offset_in_range (sizeof ty * hi) v &&
       array_at_ ty sh z lo v * 
       array_at_ ty sh 0 (hi - lo) 
       (offset_val (Int.repr (sizeof ty * lo)) v).
Proof.
  intros. unfold array_at_.
  rewrite <- split_offset_array_at; trivial.
Qed.
Lemma offset_val_array_at0:
 forall t sh f lo hi v,
  sizeof t > 0 -> hi >= 0 ->
  legal_alignas_type t = true ->
  array_at t sh (fun i => f (i-lo)%Z) lo (lo + hi) v 
  |--
  array_at t sh f 0 hi (offset_val (Int.repr (sizeof t * lo)) v).
Proof.
  intros.
  rewrite (split_offset_array_at t _ _ lo lo); trivial.
  rewrite array_at_emp.
  entailer. rewrite Zplus_comm. rewrite Z.add_simpl_r.
  apply array_lemmas.array_at_ext'. intros. rewrite Z.add_simpl_r. trivial.
  omega.
Qed.

Lemma offset_val_array_at1:
 forall t sh f g k lo hi ofs v,
    sizeof t > 0 -> hi >= 0 ->
    legal_alignas_type t = true ->
    k = lo + hi ->
    g = (fun i => f (i-lo)%Z) ->
    ofs = Int.repr (sizeof t * lo) ->
  array_at t sh g lo k v |--
  array_at t sh f 0 hi ((offset_val ofs) v).
Proof.
  intros. subst. apply offset_val_array_at0; trivial.
Qed.

Lemma split_memory_block p hi v sh:
      0 <= p <= hi -> isptr v ->
      memory_block sh (Int.repr hi) v =
      !!offset_in_range (sizeof tuchar * 0) v &&
      !!offset_in_range (sizeof tuchar * hi) v &&
      memory_block sh (Int.repr p) v * memory_block sh (Int.repr (hi-p)) (offset_val (Int.repr p) v).
Proof. intros.
rewrite memory_block_array_tuchar'; try omega; trivial. 
rewrite memory_block_array_tuchar'; try omega; trivial. 
rewrite memory_block_array_tuchar'; try omega.   
rewrite (split_offset_array_at_ _ _ _ p).
   assert (K: (sizeof tuchar * p = p)%Z).
      assert (sizeof tuchar =1 ). reflexivity.
  rewrite H1. omega.
  rewrite K; trivial.
 assumption. simpl; omega. reflexivity. apply isptr_offset_val'; trivial.
Qed.

Lemma zeroPad_BlockSize: forall k, (length k <= SHA256.BlockSize)%nat ->
  length (HMAC_SHA256.zeroPad k) = SHA256.BlockSize%nat.
Proof. unfold HMAC_SHA256.zeroPad. intros. rewrite app_length, length_Nlist. omega. 
Qed. 

Lemma length_SHA256': forall l, 
  length (functional_prog.SHA_256' l) = SHA256.DigestLength.
Proof. intros. unfold functional_prog.SHA_256'. simpl.
  rewrite length_intlist_to_Zlist, functional_prog.length_process_msg. reflexivity.
Qed.
 
Lemma mkKey_length l: length (HMAC_SHA256.mkKey l) = SHA256.BlockSize.
Proof. intros. unfold HMAC_SHA256.mkKey.
  remember (Zlength l >? Z.of_nat SHA256.BlockSize) as z. 
  destruct z. apply zeroPad_BlockSize.
    rewrite length_SHA256'.  
    apply Nat2Z.inj_le. simpl. omega. 
  apply zeroPad_BlockSize.
    rewrite Zlength_correct in Heqz. 
    apply Nat2Z.inj_le. 
    specialize (Zgt_cases (Z.of_nat (Datatypes.length l)) (Z.of_nat SHA256.BlockSize)). rewrite <- Heqz. trivial.
Qed.

Lemma mkKey_atBlockSize s: length s = SHA256.BlockSize%nat ->
      HMAC_SHA256.mkKey s = s.
Proof. unfold HMAC_SHA256.mkKey. rewrite Zlength_correct.
  intros. rewrite H.
  simpl. unfold HMAC_SHA256.zeroPad. rewrite H. simpl.
  apply app_nil_r.  
Qed.

Lemma isptrD v: isptr v -> exists b ofs, v = Vptr b ofs.
Proof. intros. destruct v; try contradiction. exists b, i; trivial. Qed.


Lemma isbyte_sha x: Forall isbyteZ (functional_prog.SHA_256' x).
Proof. apply isbyte_intlist_to_Zlist. Qed.


Lemma updAbs_len: forall L s t, update_abs L s t -> s256a_len t = s256a_len s + Zlength L * 8.
Proof. intros. inversion H; clear H.
  unfold s256a_len. simpl.
  rewrite Zlength_app. subst. 
  repeat rewrite Z.mul_add_distr_r.
  repeat rewrite <- Z.add_assoc.
  assert (Zlength blocks * WORD * 8 + Zlength newfrag * 8 =
          Zlength oldfrag * 8 + Zlength L * 8).
    assert (Zlength (oldfrag ++ L) = Zlength (SHA256.intlist_to_Zlist blocks ++ newfrag)).
      rewrite H4; trivial.
    clear H4. rewrite Zlength_app in H.
              rewrite <- (Z.mul_add_distr_r (Zlength oldfrag)), H. clear H.
              rewrite Zlength_app, Zlength_intlist_to_Zlist.
              rewrite (Z.mul_comm WORD). rewrite Z.mul_add_distr_r. trivial. 
  rewrite H; trivial.
Qed.

Lemma Zlength_max_zero: forall {A:Type} (l:list A), Z.max 0 (Zlength l) = Zlength l.
Proof. intros.
       rewrite Z.max_r. trivial.  
       apply (initial_world.zlength_nonneg _ l).
Qed.

Lemma HMAC_length d k: length (HMAC256 d k) = 32%nat.
Proof.
  unfold HMAC_SHA256.HMAC, HMAC_SHA256.OUTER.
  apply length_SHA256'.
Qed.
Lemma HMAC_Zlength d k: Zlength (HMAC256 d k) = 32.
Proof.
  rewrite Zlength_correct, HMAC_length. reflexivity.
Qed.
