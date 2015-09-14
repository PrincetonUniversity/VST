Require Import Recdef.
Require Import floyd.proofauto.
Local Open Scope logic.
Require Import List. Import ListNotations.
Require Import general_lemmas.

Require Import split_array_lemmas.
Require Import fragments.
Require Import ZArith. 
Require Import tweetNaclBase.
Require Import Salsa20.
Require Import verif_salsa_base.
Require Import tweetnaclVerifiableC.
Require Import spec_salsa. Opaque Snuffle.Snuffle. Opaque fcore_result.

Opaque core_spec. Opaque ld32_spec. Opaque L32_spec. Opaque st32_spec.
Opaque crypto_core_salsa20_spec. Opaque crypto_core_hsalsa20_spec.

Fixpoint upd_upto (x: SixteenByte * SixteenByte * (SixteenByte * SixteenByte)) i (l:list val):list val :=
  match i with
    O => l
  | S n => 
     match x with (Nonce, C, (Key1, Key2)) =>
     ((upd_reptype_array tuint (11 + (Z.of_nat n))
     (upd_reptype_array tuint (6 + (Z.of_nat n))
        (upd_reptype_array tuint (1 + (Z.of_nat n))
           (upd_reptype_array tuint (5 * (Z.of_nat n)) (upd_upto x n l)
              (Vint (littleendian (Select16Q C (Z.of_nat n)))))
           (Vint (littleendian (Select16Q Key1 (Z.of_nat n)))))
        (Vint (littleendian (Select16Q Nonce (Z.of_nat n)))))
     (Vint (littleendian (Select16Q Key2 (Z.of_nat n))))))
     end
  end.

Lemma upd_upto_Sn Nonce C Key1 Key2 n l: upd_upto (Nonce, C, (Key1, Key2)) (S n) l =
     ((upd_reptype_array tuint (11 + (Z.of_nat n))
     (upd_reptype_array tuint (6 + (Z.of_nat n))
        (upd_reptype_array tuint (1 + (Z.of_nat n))
           (upd_reptype_array tuint (5 * (Z.of_nat n)) (upd_upto (Nonce, C, (Key1, Key2))  n l)
              (Vint (littleendian (Select16Q C (Z.of_nat n)))))
           (Vint (littleendian (Select16Q Key1 (Z.of_nat n)))))
        (Vint (littleendian (Select16Q Nonce (Z.of_nat n)))))
     (Vint (littleendian (Select16Q Key2 (Z.of_nat n)))))).
 reflexivity. Qed.

Lemma upd_upto_length data l (H: length l = 16%nat): forall (i:nat) (I:(0<=i<=4)%nat), 
      length (upd_upto data i l) = 16%nat.
  Proof. destruct l; simpl in H. intros; omega.
    destruct l; simpl in H. intros; omega. destruct l; simpl in H. intros; omega. 
    destruct l; simpl in H. intros; omega. destruct l; simpl in H. intros; omega. 
    destruct l; simpl in H. intros; omega. destruct l; simpl in H. intros; omega. 
    destruct l; simpl in H. intros; omega. destruct l; simpl in H. intros; omega. 
    destruct l; simpl in H. intros; omega. destruct l; simpl in H. intros; omega. 
    destruct l; simpl in H. intros; omega. destruct l; simpl in H. intros; omega. 
    destruct l; simpl in H. intros; omega. destruct l; simpl in H. intros; omega. 
    destruct l; simpl in H. intros; omega. destruct l; simpl in H. 2: intros; omega. clear H.
    induction i; destruct data as [[N C] [K1 K2]]. reflexivity.
    rewrite upd_upto_Sn. remember (11 + Z.of_nat i) as z1. remember (6 + Z.of_nat i) as z2.
    remember (1 + Z.of_nat i) as z3. remember (5 * Z.of_nat i)%Z as z4.
    remember (Vint (littleendian (Select16Q C (Z.of_nat i)))) as u4.
    remember (Vint (littleendian (Select16Q K1 (Z.of_nat i)))) as u3.
    remember (Vint (littleendian (Select16Q N (Z.of_nat i)))) as u2.
    remember (Vint (littleendian (Select16Q K2 (Z.of_nat i)))) as u1.
    specialize (upd_reptype_array_length tuint); intros X; simpl in X. intros.
    erewrite <- X in IHi.
    erewrite <- X in IHi.
    erewrite <- X in IHi.
    erewrite <- X in IHi. apply IHi. omega. omega. 
    rewrite IHi. subst z1. rewrite Z2Nat.inj_add, Nat2Z.id. simpl; omega. omega. omega. omega. omega.
    rewrite IHi. subst z2. rewrite Z2Nat.inj_add, Nat2Z.id. simpl; omega. omega. omega. omega. omega. 
    rewrite IHi. subst z3. rewrite Z2Nat.inj_add, Nat2Z.id. simpl; omega. omega. omega. omega. omega.
    rewrite IHi. subst z4. rewrite Z2Nat.inj_mul, Nat2Z.id. simpl; omega. omega. omega. omega.
Qed.

Lemma upd_upto_Vint data: forall n, (0<=n<16)%nat -> 
      forall d, exists i, nth n (upd_upto data 4 (list_repeat 16 Vundef)) d = Vint i.
  Proof. unfold upd_upto; intros. destruct data as [[N C] [K1 K2]].
   specialize (upd_reptype_array_lookup' 16 tuint); intros X; simpl in X.
   rewrite X; trivial. 2: simpl; omega. 
   rewrite X; trivial. 2: simpl; omega. 
   rewrite X; trivial. 2: simpl; omega. 
   rewrite X; trivial. 2: simpl; omega. 
   rewrite X; trivial. 2: simpl; omega. 
   rewrite X; trivial. 2: simpl; omega. 
   rewrite X; trivial. 2: simpl; omega. 
   rewrite X; trivial. 2: simpl; omega. 
   rewrite X; trivial. 2: simpl; omega. 
   rewrite X; trivial. 2: simpl; omega. 
   rewrite X; trivial. 2: simpl; omega. 
   rewrite X; trivial. 2: simpl; omega. 
   rewrite X; trivial. 2: simpl; omega. 
   rewrite X; trivial. 2: simpl; omega. 
   rewrite X; trivial. 2: simpl; omega. 
   rewrite X; trivial. 2: simpl; omega. 
   repeat rewrite Z2Nat.inj_add; try omega. simpl.
   repeat rewrite Z2Nat.inj_mul; try omega. simpl.
   repeat rewrite plus_assoc. simpl. Transparent plus mult. simpl.
   clear -H.
   destruct n; simpl in *. eexists; reflexivity.
   destruct n; simpl in *. eexists; reflexivity.
   destruct n; simpl in *. eexists; reflexivity.
   destruct n; simpl in *. eexists; reflexivity.
   destruct n; simpl in *. eexists; reflexivity.
   destruct n; simpl in *. eexists; reflexivity.
   destruct n; simpl in *. eexists; reflexivity.
   destruct n; simpl in *. eexists; reflexivity.
   destruct n; simpl in *. eexists; reflexivity.
   destruct n; simpl in *. eexists; reflexivity.
   destruct n; simpl in *. eexists; reflexivity.
   destruct n; simpl in *. eexists; reflexivity.
   destruct n; simpl in *. eexists; reflexivity.
   destruct n; simpl in *. eexists; reflexivity.
   destruct n; simpl in *. eexists; reflexivity.
   destruct n; simpl in *. eexists; reflexivity. omega.
Qed.

(*cf xsalsa-paper, beginning of Section 2*)
Lemma upd_upto_char data l: length l = 16%nat ->
      upd_upto data 4 l = match data with ((Nonce, C), (Key1, Key2)) =>
          match Nonce with (N1, N2, N3, N4) =>
          match C with (C1, C2, C3, C4) =>
          match Key1 with (K1, K2, K3, K4) =>
          match Key2 with (L1, L2, L3, L4) =>
      map Vint (map littleendian [C1; K1; K2; K3; 
                                  K4; C2; N1; N2;
                                  N3; N4; C3; L1;
                                  L2; L3; L4; C4]) end end end end end. 
Proof. intros. destruct data as [[Nonce C] [Key1 Key2]].
   destruct Nonce as [[[N1 N2] N3] N4].
   destruct C as [[[C1 C2] C3] C4].
   destruct Key1 as [[[K1 K2] K3] K4].
   destruct Key2 as [[[L1 L2] L3] L4]. 
   destruct l; simpl in H. omega.
   destruct l; simpl in H. omega.
   destruct l; simpl in H. omega.
   destruct l; simpl in H. omega.
   destruct l; simpl in H. omega.
   destruct l; simpl in H. omega.
   destruct l; simpl in H. omega.
   destruct l; simpl in H. omega.
   destruct l; simpl in H. omega.
   destruct l; simpl in H. omega.
   destruct l; simpl in H. omega.
   destruct l; simpl in H. omega.
   destruct l; simpl in H. omega.
   destruct l; simpl in H. omega.
   destruct l; simpl in H. omega.
   destruct l; simpl in H. omega.
   destruct l; simpl in H. 2: omega. clear H. reflexivity.
Qed.

Definition X_content (x: SixteenByte * SixteenByte * (SixteenByte * SixteenByte))
                     (i:Z) (l:list val) : Prop :=
    exists n, i = Z.of_nat n /\ l = upd_upto x n (list_repeat 16 Vundef).

Lemma XcontUpdate Nonce C Key1 Key2 i l
      (I: 0 <= i < 4)
      (L: X_content (Nonce, C, (Key1, Key2)) i l):
X_content (Nonce, C, (Key1, Key2)) (i + 1)
  (upd_reptype_array tuint (11 + i)
     (upd_reptype_array tuint (6 + i)
        (upd_reptype_array tuint (1 + i)
           (upd_reptype_array tuint (5 * i) l
              (Vint (littleendian (Select16Q C i))))
           (Vint (littleendian (Select16Q Key1 i))))
        (Vint (littleendian (Select16Q Nonce i))))
     (Vint (littleendian (Select16Q Key2 i)))).
Proof. unfold X_content in *. destruct L as [n [? ?]].
  exists (S n); subst.
  split. rewrite Nat2Z.inj_succ; omega.
  reflexivity.
Qed.

Lemma f_core_loop1: forall (Espec : OracleKind)
c k h nonce out OUT 
(data : SixteenByte * SixteenByte * (SixteenByte * SixteenByte))
(OUTlen : length OUT = 64%nat)
(Delta := func_tycontext f_core SalsaVarSpecs SalsaFunSpecs) (*abbreviate : tycontext*)
(*POSTCONDITION := abbreviate : ret_assert
MORE_COMMANDS := abbreviate : statement
Struct_env := abbreviate : type_id_env*)
(out' : name _out)
(in' : name _in)
(k' : name _k)
(c' : name _c)
(h' : name _h)
(aux' : name _aux)
w x y t,
@semax Espec Delta
  (PROP  ()
   LOCAL  (lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
   lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w; temp _in nonce;
   temp _out out; temp _c c; temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(data_at_ Tsh (tarray tuint 16) y);
   `(data_at_ Tsh (tarray tuint 4) t); `(data_at_ Tsh (tarray tuint 16) x);
   `(data_at_ Tsh (tarray tuint 16) w); `(CoreInSEP data (nonce, c, k));
   `(data_at Tsh (tarray tuchar 64) OUT out)))
  (Sfor (Sset _i (Econst_int (Int.repr 0) tint))
     (Ebinop Olt (Etempvar _i tint) (Econst_int (Int.repr 4) tint) tint)
     (Ssequence
        (Ssequence
           (Scall (Some _aux')
              (Evar _ld32
                 (Tfunction (Tcons (tptr tuchar) Tnil) tuint cc_default))
              [Ebinop Oadd (Etempvar _c (tptr tuchar))
                 (Ebinop Omul (Econst_int (Int.repr 4) tint)
                    (Etempvar _i tint) tint) (tptr tuchar)])
           (Sset _aux (Etempvar _aux' tuint)))
        (Ssequence
           (Sassign
              (Ederef
                 (Ebinop Oadd (Evar _x (tarray tuint 16))
                    (Ebinop Omul (Econst_int (Int.repr 5) tint)
                       (Etempvar _i tint) tint) (tptr tuint)) tuint)
              (Etempvar _aux tuint))
           (Ssequence
              (Ssequence
                 (Scall (Some _aux'1)
                    (Evar _ld32
                       (Tfunction (Tcons (tptr tuchar) Tnil) tuint cc_default))
                    [Ebinop Oadd (Etempvar _k (tptr tuchar))
                       (Ebinop Omul (Econst_int (Int.repr 4) tint)
                          (Etempvar _i tint) tint) (tptr tuchar)])
                 (Sset _aux (Etempvar _aux'1 tuint)))
              (Ssequence
                 (Sassign
                    (Ederef
                       (Ebinop Oadd (Evar _x (tarray tuint 16))
                          (Ebinop Oadd (Econst_int (Int.repr 1) tint)
                             (Etempvar _i tint) tint) (tptr tuint)) tuint)
                    (Etempvar _aux tuint))
                 (Ssequence
                    (Ssequence
                       (Scall (Some _aux'2)
                          (Evar _ld32
                             (Tfunction (Tcons (tptr tuchar) Tnil) tuint
                                cc_default))
                          [Ebinop Oadd (Etempvar _in (tptr tuchar))
                             (Ebinop Omul (Econst_int (Int.repr 4) tint)
                                (Etempvar _i tint) tint) (tptr tuchar)])
                       (Sset _aux (Etempvar _aux'2 tuint)))
                    (Ssequence
                       (Sassign
                          (Ederef
                             (Ebinop Oadd (Evar _x (tarray tuint 16))
                                (Ebinop Oadd (Econst_int (Int.repr 6) tint)
                                   (Etempvar _i tint) tint) (tptr tuint))
                             tuint) (Etempvar _aux tuint))
                       (Ssequence
                          (Ssequence
                             (Scall (Some _aux'3)
                                (Evar _ld32
                                   (Tfunction (Tcons (tptr tuchar) Tnil)
                                      tuint cc_default))
                                [Ebinop Oadd
                                   (Ebinop Oadd (Etempvar _k (tptr tuchar))
                                      (Econst_int (Int.repr 16) tint)
                                      (tptr tuchar))
                                   (Ebinop Omul
                                      (Econst_int (Int.repr 4) tint)
                                      (Etempvar _i tint) tint) (tptr tuchar)])
                             (Sset _aux (Etempvar _aux'3 tuint)))
                          (Sassign
                             (Ederef
                                (Ebinop Oadd (Evar _x (tarray tuint 16))
                                   (Ebinop Oadd
                                      (Econst_int (Int.repr 11) tint)
                                      (Etempvar _i tint) tint) (tptr tuint))
                                tuint) (Etempvar _aux tuint)))))))))
     (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint)))
  (normal_ret_assert (
PROP  ()
   LOCAL  (temp _i (Vint (Int.repr 4)); lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(data_at_ Tsh (tarray tuint 16) y);
   `(data_at_ Tsh (tarray tuint 4) t);
   `(EX  l : list val,
     !!X_content data 4 l && data_at Tsh (tarray tuint 16) l x);
   `(data_at_ Tsh (tarray tuint 16) w); `(CoreInSEP data (nonce, c, k));
   `(data_at Tsh (tarray tuchar 64) OUT out)))).
Proof. intros.
forward_for_simple_bound 4 (EX i:Z, 
   PROP  ()
   LOCAL  ( 
   lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
   lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w; temp _in nonce;
   temp _out out; temp _c c; temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(data_at_ Tsh (tarray tuint 16) y);
   `(data_at_ Tsh (tarray tuint 4) t);
   `(EX l:_, !!(X_content data i l) && data_at Tsh (tarray tuint 16) l x);
   `(data_at_ Tsh (tarray tuint 16) w); `(CoreInSEP data (nonce, c, k));
   `(data_at Tsh (tarray tuchar 64) OUT out) (*data_block Tsh OUT out)*))).
{ entailer. apply (exp_right (list_repeat 16 Vundef)). entailer.
  apply prop_right. unfold X_content. exists O. split; trivial. }
{ destruct data as ((Nonce, C), Key). unfold CoreInSEP.
Opaque Zplus. Opaque Z.mul. Opaque mult. Opaque plus.
   Opaque firstn. Opaque skipn. Opaque Z.sub. simpl.
  unfold SByte at 2. normalize. intros X0; normalize. rename H0 into X0cont.
  assert_PROP (offset_in_range (sizeof tuchar * 0) c /\
               offset_in_range (sizeof tuchar * 16) c).
  { unfold data_at at 1. simpl. intros rho. normalize.
    apply prop_right.
    unfold size_compatible in H11. unfold offset_in_range.
    destruct c; simpl; split; trivial.
    rewrite Zplus_0_r. specialize (Int.unsigned_range i0); intros; omega.
    simpl in H11. rewrite Zmult_1_l in H11. split; trivial.
    specialize (Int.unsigned_range i0); intros; omega. }
  rename H0 into OffsetC.
  assert (C16:= SixteenByte2ValList_Zlength C).
  remember (SplitSelect16Q C i) as FB; destruct FB as (Front, BACK).
    rewrite (Select_SplitSelect16Q C i _ _ HeqFB) in *. 
    erewrite Select_Unselect_Tarray_at; try reflexivity; try assumption. normalize.
  unfold Select_at. simpl. rewrite app_nil_r.

Transparent core_spec. Transparent ld32_spec. Transparent L32_spec. Transparent st32_spec.
Transparent crypto_core_salsa20_spec. Transparent crypto_core_hsalsa20_spec.
  forward_call (offset_val (Int.repr (4 * i)) c, 
                 Select16Q C i).
Opaque core_spec. Opaque ld32_spec. Opaque L32_spec. Opaque st32_spec.
Opaque crypto_core_salsa20_spec. Opaque crypto_core_hsalsa20_spec.
  { entailer. 
    rewrite <- QuadByteValList_ZLength, QuadChunk2ValList_ZLength,
              (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFB H).
    cancel. }
  (*using forward_call' ...v leaves two side conditions.
    { rewrite <- QuadByteValList_ZLength. rewrite Z.mul_1_l.  simpl.
    rewrite  QuadChunk2ValList_ZLength. rewrite (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFB H).
    cancel. }
  { instantiate (1:= [lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
      lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w; temp _in nonce;
      temp _out out; temp _c c; temp _k k; temp _h (Vint (Int.repr h))]).
      admit. (*OK - is in comment - but should replace forward_call by forward_call' *) } 
  { admit. (*OK - is in comment - but should replace forward_call by forward_call'*) }
  *)
  { repeat constructor. }
  after_call. clear aux'0.
  normalize.
  apply semax_pre with (P':=
  (PROP  ()
   LOCAL  ((*temp _aux v; *)
   temp _aux (Vint (littleendian (Select16Q C i)));
   temp _i (Vint (Int.repr i));
   lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
   lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w; temp _in nonce;
   temp _out out; temp _c c; temp _k k; temp _h (Vint (Int.repr h)))
   SEP 
   (`(data_at Tsh (Tarray tuchar 16 noattr) (SixteenByte2ValList C) c);
   `(SByte Nonce nonce);
   `(ThirtyTwoByte Key k);
   `(data_at_ Tsh (tarray tuint 16) y); `(data_at_ Tsh (tarray tuint 4) t);
   `(data_at Tsh (tarray tuint 16) X0 x);
   `(data_at_ Tsh (tarray tuint 16) w); 
   `(data_at Tsh (tarray tuchar 64) OUT out)))). 
  { entailer. cancel.   
    (*Apart from the unfold QByte, the next 9 lines are exactly as above, inside the function call*)
    rewrite (Select_SplitSelect16Q C i _ _ HeqFB) in *.
    erewrite Select_Unselect_Tarray_at; try reflexivity; try assumption. 
    unfold QByte, Select_at. simpl. rewrite app_nil_r. cancel.
    rewrite <- QuadByteValList_ZLength. rewrite Z.mul_1_l. simpl.
    rewrite  QuadChunk2ValList_ZLength.
    rewrite (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFB H). cancel. }

  (*Store into x[...]*)
  Transparent firstn. (*subst v; simpl.*)
  forward. simpl.

  erewrite ThirtyTwoByte_split16. unfold SByte at 2; destruct Key as [Key1 Key2]; normalize.
  rename H0 into OffsetK.
  assert (K1_16:= SixteenByte2ValList_Zlength Key1).
  remember (SplitSelect16Q Key1 i) as FB_K1; destruct FB_K1 as (Front_K1, BACK_K1).
    rewrite (Select_SplitSelect16Q Key1 i _ _ HeqFB_K1) in *. 
    erewrite Select_Unselect_Tarray_at; try reflexivity; try assumption. normalize.
  unfold Select_at. simpl. rewrite app_nil_r.
Transparent core_spec. Transparent ld32_spec. Transparent L32_spec. Transparent st32_spec.
Transparent crypto_core_salsa20_spec. Transparent crypto_core_hsalsa20_spec.
  (*forward_call' (offset_val (Int.repr (4 * i)) k, 
                 Select16Q Key1 i) v. 
  { rewrite <- QuadByteValList_ZLength. rewrite Z.mul_1_l.  simpl.
    rewrite  QuadChunk2ValList_ZLength. rewrite (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFB_K1 H).
    cancel. }
  { instantiate (1:= [lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
      lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w; temp _in nonce;
      temp _out out; temp _c c; temp _k k; temp _h (Vint (Int.repr h))]).
      admit. (* OK - is in comment; again seems due to failure in forward_call' *) } 
  { admit. (* OK - is in comment; again seems due to failure in forward_call' *) }*)
  forward_call (offset_val (Int.repr (4 * i)) k, 
                 Select16Q Key1 i) (*v*). 
Opaque core_spec. Opaque ld32_spec. Opaque L32_spec. Opaque st32_spec.
Opaque crypto_core_salsa20_spec. Opaque crypto_core_hsalsa20_spec.
  { entailer. 
    rewrite <- QuadByteValList_ZLength,  QuadChunk2ValList_ZLength,
           (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFB_K1 H).
    cancel. }
  { repeat constructor. }
  after_call.

  normalize. subst aux'0.
  apply semax_pre with (P':=
  (PROP  ()
   LOCAL  ((*temp _aux v;*) temp _aux (Vint (littleendian (Select16Q Key1 i)));
   temp _i (Vint (Int.repr i));
   lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
   lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w; temp _in nonce;
   temp _out out; temp _c c; temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(ThirtyTwoByte (Key1,Key2) k);
   `(data_at Tsh (Tarray tuchar 16 noattr) (SixteenByte2ValList C) c);
   `(SByte Nonce nonce); `(data_at_ Tsh (tarray tuint 16) y);
   `(data_at_ Tsh (tarray tuint 4) t);
   `(data_at Tsh (tarray tuint 16)
       (upd_reptype_array tuint (5 * i) X0
          (Vint (littleendian (Select16Q C i)))) x);
   `(data_at_ Tsh (tarray tuint 16) w);
   `(data_at Tsh (tarray tuchar 64) OUT out)))). 
  { erewrite ThirtyTwoByte_split16. (*unfold SByte at 1.*)
    entailer. cancel. 
   
    (*Apart from the unfold QByte, the next 9 lines are exactly as above, inside the function call*)
    unfold SByte. rewrite (Select_SplitSelect16Q _ i _ _ HeqFB_K1) in *.
    erewrite Select_Unselect_Tarray_at; try reflexivity; try assumption. 
    unfold QByte, Select_at. simpl. repeat rewrite app_nil_r. cancel.
    rewrite <- QuadByteValList_ZLength. rewrite Z.mul_1_l. simpl.
    rewrite  QuadChunk2ValList_ZLength.
    rewrite (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFB_K1 H). cancel. }

  (*Store into x[...]*)
(*  subst v; simpl.*)
  forward. simpl.

  (*Load nonce*)
  unfold SByte at 1. normalize.
  assert_PROP (offset_in_range (sizeof tuchar * 0) nonce /\
               offset_in_range (sizeof tuchar * 16) nonce).
  { unfold data_at at 3. simpl. intros rho. normalize.
    apply prop_right.
    unfold size_compatible in H12. unfold offset_in_range.
    destruct nonce; simpl; split; trivial.
    rewrite Zplus_0_r. specialize (Int.unsigned_range i0); intros; omega.
    simpl in H12. rewrite Zmult_1_l in H12. split; trivial.
    specialize (Int.unsigned_range i0); intros; omega. }
  rename H0 into OffsetNonce.
  assert (N16:= SixteenByte2ValList_Zlength Nonce).
  remember (SplitSelect16Q Nonce i) as FB_N; destruct FB_N as (Front_N, BACK_N).
    rewrite (Select_SplitSelect16Q _ i _ _ HeqFB_N) in *. 
    erewrite Select_Unselect_Tarray_at with (d:=nonce); try reflexivity; try assumption. normalize.
  unfold Select_at. simpl. rewrite app_nil_r.
Transparent core_spec. Transparent ld32_spec. Transparent L32_spec. Transparent st32_spec.
Transparent crypto_core_salsa20_spec. Transparent crypto_core_hsalsa20_spec.
  (*forward_call' (offset_val (Int.repr (4 * i)) nonce, 
                 Select16Q Nonce i) v. 
  { rewrite <- QuadByteValList_ZLength. rewrite Z.mul_1_l.  simpl.
    rewrite  QuadChunk2ValList_ZLength.
    rewrite (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFB_N H).
    cancel. }
  { instantiate (1:= [lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
      lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w; temp _in nonce;
      temp _out out; temp _c c; temp _k k; temp _h (Vint (Int.repr h))]).
      admit. (* OK - is in comment; again seems due to failure in forward_call' *) } 
  { admit. (* OK - is in comment; again seems due to failure in forward_call' *) }*)
  forward_call (offset_val (Int.repr (4 * i)) nonce, 
                 Select16Q Nonce i). 
Opaque core_spec. Opaque ld32_spec. Opaque L32_spec. Opaque st32_spec.
Opaque crypto_core_salsa20_spec. Opaque crypto_core_hsalsa20_spec.
  { entailer. 
    rewrite <- QuadByteValList_ZLength, QuadChunk2ValList_ZLength,
            (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFB_N H).
    cancel. }
  { repeat constructor. }
  after_call.
  
  normalize. subst aux'0.
  apply semax_pre with (P':=
  (PROP  ()
   LOCAL  ((*temp _aux v; *)
   temp _aux (Vint (littleendian (Select16Q Nonce i)));
   temp _i (Vint (Int.repr i));
   lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
   lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w; temp _in nonce;
   temp _out out; temp _c c; temp _k k; temp _h (Vint (Int.repr h)))
   SEP 
   (`(data_at Tsh (Tarray tuchar 16 noattr) (SixteenByte2ValList C) c);
   `(SByte Nonce nonce);
   `(ThirtyTwoByte (Key1,Key2) k);
   `(data_at_ Tsh (tarray tuint 16) y); `(data_at_ Tsh (tarray tuint 4) t);
   `(data_at Tsh (tarray tuint 16)
       (upd_reptype_array tuint (1 + i)
          (upd_reptype_array tuint (5 * i) X0
             (Vint (littleendian (Select16Q C i))))
          (Vint (littleendian (Select16Q Key1 i)))) x);
   `(data_at_ Tsh (tarray tuint 16) w);
   `(data_at Tsh (tarray tuchar 64) OUT out) (*`(data_block Tsh OUT out)*)))). 
  { entailer. cancel. 
   
    (*Apart from the unfold QByte, the next 9 lines are exactly as above, inside the function call*)
    unfold SByte. rewrite (Select_SplitSelect16Q _ i _ _ HeqFB_N) in *.
    erewrite Select_Unselect_Tarray_at; try reflexivity; try assumption. 
    unfold QByte, Select_at. simpl. rewrite app_nil_r. cancel.
    rewrite <- QuadByteValList_ZLength. rewrite Z.mul_1_l. simpl.
    rewrite  QuadChunk2ValList_ZLength.
    rewrite (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFB_N H). cancel. }

  (*Store into x[...]*)
(*  subst v.*)
  forward.

  (*Load Key2*)
  rewrite ThirtyTwoByte_split16. normalize.
  unfold SByte at 2.
  assert (K2_16:= SixteenByte2ValList_Zlength Key2).
  remember (SplitSelect16Q Key2 i) as FB_K2; destruct FB_K2 as (Front_K2, BACK_K2).
    rewrite (Select_SplitSelect16Q _ i _ _ HeqFB_K2) in *. 
    erewrite Select_Unselect_Tarray_at with (d:=offset_val (Int.repr 16) k); try reflexivity; try assumption. normalize.
  unfold Select_at. simpl. rewrite app_nil_r.

Transparent core_spec. Transparent ld32_spec. Transparent L32_spec. Transparent st32_spec.
Transparent crypto_core_salsa20_spec. Transparent crypto_core_hsalsa20_spec.
  forward_call (offset_val (Int.repr (16 + 4 * i)) k, 
                 Select16Q Key2 i). 
Opaque core_spec. Opaque ld32_spec. Opaque L32_spec. Opaque st32_spec.
Opaque crypto_core_salsa20_spec. Opaque crypto_core_hsalsa20_spec.
  { entailer. repeat rewrite <- QuadByteValList_ZLength. simpl.
    rewrite  QuadChunk2ValList_ZLength. rewrite (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFB_K2 H).
    cancel. }
  { repeat constructor. }
  after_call.

  (*again forward_call' doesn't quite work
  (*we seem to need the following for forward_call' to work properly here*)
  rewrite data_at_isptr. normalize. Require Import vst_lemmas. apply isptrD in H0. destruct H0 as [kb [koff HK]]. rewrite HK in *.

  forward_call' (offset_val (Int.repr (16 + 4 * i)) (Vptr kb koff), 
                 Select16Q Key2 i) v. 
  { repeat rewrite <- QuadByteValList_ZLength. simpl.
    rewrite  QuadChunk2ValList_ZLength. rewrite (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFB_K2 H).
    cancel. }
  { instantiate (1:= [lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
      lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w; temp _in nonce;
      temp _out out; temp _c c; temp _k k; temp _h (Vint (Int.repr h))]).
      admit. (*OK in comment *) } 
  { admit. (*OK in comment*) }*)

  normalize. subst aux'0. (*v*)
  apply semax_pre with (P':=
  (PROP  ()
   LOCAL  ((*temp _aux v;*)
   temp _aux (Vint (littleendian (Select16Q Key2 i)));
   temp _i (Vint (Int.repr i));
   lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
   lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w; temp _in nonce;
   temp _out out; temp _c c; temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(ThirtyTwoByte (Key1,Key2) k);
   `(data_at Tsh (Tarray tuchar 16 noattr) (SixteenByte2ValList C) c);
   `(SByte Nonce nonce); `(data_at_ Tsh (tarray tuint 16) y);
   `(data_at_ Tsh (tarray tuint 4) t);
   `(data_at Tsh (tarray tuint 16)
       (upd_reptype_array tuint (6 + i)
          (upd_reptype_array tuint (1 + i)
             (upd_reptype_array tuint (5 * i) X0
                (Vint (littleendian (Select16Q C i))))
             (Vint (littleendian (Select16Q Key1 i))))
          (Vint (littleendian (Select16Q Nonce i)))) x);
   `(data_at_ Tsh (tarray tuint 16) w); 
   `(data_at Tsh (tarray tuchar 64) OUT out) (*`(data_block Tsh OUT out)*)))). 
  { erewrite ThirtyTwoByte_split16.
    entailer. cancel. 
   
    (*Apart from the unfold QByte, the next 9 lines are exactly as above, inside the function call*)
    unfold SByte. rewrite (Select_SplitSelect16Q _ i _ _ HeqFB_K2) in *.
    erewrite Select_Unselect_Tarray_at; try reflexivity; try assumption. 
    unfold QByte, Select_at. simpl. repeat rewrite app_nil_r. cancel.
    rewrite <- QuadByteValList_ZLength. rewrite Z.mul_1_l. simpl.
    rewrite  QuadChunk2ValList_ZLength.
    rewrite (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFB_K2 H).
    rewrite offset_offset_val, add_repr. (* int_add_assoc1.*) cancel. }

  (*Store into x[...]*)
(*  subst v.*)
  forward.

  entailer. 
  apply (exp_right (upd_reptype_array tuint (11 + i)
     (upd_reptype_array tuint (6 + i)
        (upd_reptype_array tuint (1 + i)
           (upd_reptype_array tuint (5 * i) X0
              (Vint (littleendian (Select16Q C i))))
           (Vint (littleendian (Select16Q Key1 i))))
        (Vint (littleendian (Select16Q Nonce i))))
     (Vint (littleendian (Select16Q Key2 i))))).
  entailer.
  apply andp_right. 2: cancel.
  apply prop_right. clear - X0cont H. apply XcontUpdate; trivial. }
apply derives_refl. 
Qed.

Lemma XX data l: X_content data 4 l -> 
  l = match data with ((Nonce, C), (Key1, Key2)) =>
          match Nonce with (N1, N2, N3, N4) =>
          match C with (C1, C2, C3, C4) =>
          match Key1 with (K1, K2, K3, K4) =>
          match Key2 with (L1, L2, L3, L4) =>
      map Vint (map littleendian [C1; K1; K2; K3; 
                                  K4; C2; N1; N2;
                                  N3; N4; C3; L1;
                                  L2; L3; L4; C4]) 
      end end end end end.
Proof.
intros. destruct H as [? [? ?]].
assert (Z.to_nat 4 = Z.to_nat (Z.of_nat x)). rewrite H; trivial. 
rewrite Nat2Z.id in H1. subst x l. clear H.
apply upd_upto_char. reflexivity.
Qed.
