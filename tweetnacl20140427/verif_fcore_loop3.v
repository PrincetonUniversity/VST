Require Import Recdef.
Require Import floyd.proofauto.
Local Open Scope logic.
Require Import List. Import ListNotations.
Require Import general_lemmas.

Require Import split_array_lemmas.
(*Require Import fragments.*)
Require Import ZArith. 
Require Import tweetNaclBase.
Require Import Salsa20.
Require Import verif_salsa_base.
Require Import tweetnaclVerifiableC.
Require Import Snuffle.
Require Import spec_salsa.  

Require Import verif_fcore_jbody. 
Opaque Snuffle.Snuffle. Opaque core_spec. Opaque fcore_result.
Opaque crypto_core_salsa20_spec. Opaque crypto_core_hsalsa20_spec.

Fixpoint WcontI (xs: list int) (j:nat) (l:list int):Prop :=
   match j with O => Zlength l = 16 /\l=xs
   | (S n) => Zlength l = 16 /\
              exists t0 t1 t2 t3,
              Znth ((5 * (Z.of_nat n) + 4 * 0) mod 16) (map Vint xs) Vundef = Vint t0 /\
              Znth ((5 * (Z.of_nat n) + 4 * 1) mod 16) (map Vint xs) Vundef = Vint t1 /\
              Znth ((5 * (Z.of_nat n) + 4 * 2) mod 16) (map Vint xs) Vundef = Vint t2 /\
              Znth ((5 * (Z.of_nat n) + 4 * 3) mod 16) (map Vint xs) Vundef = Vint t3 /\
              exists wl, WcontI xs n wl /\
                match Wcopyspec t0 t1 t2 t3 with
                 (s0,s1,s2,s3) => wlistJ' wl (Z.of_nat n) s0 s1 s2 s3 l
                end
  end.

Lemma WcontI_length xs: forall j l, WcontI xs j l -> Zlength xs=16 /\ Zlength l=16.
Proof. induction j; simpl; intros; subst. destruct H; subst. split; trivial.
destruct H as [L [to [t1 [t2 [t3 [_ [_ [_ [_ [wl [WCL _]]]]]]]]]]].
destruct (IHj _ WCL).
split; trivial.
Qed.

Lemma WWI r wlist (W: WcontI r 4 wlist): snuffleRound r = Some wlist.
Proof.
destruct (WcontI_length _ _ _ W) as [H WL].
destruct r. rewrite Zlength_nil in H; omega. rename i into x0. rewrite Zlength_cons' in H.
destruct r. rewrite Zlength_nil in H; omega. rename i into x1. rewrite Zlength_cons' in H.
destruct r. rewrite Zlength_nil in H; omega. rename i into x2. rewrite Zlength_cons' in H.
destruct r. rewrite Zlength_nil in H; omega. rename i into x3. rewrite Zlength_cons' in H.
destruct r. rewrite Zlength_nil in H; omega. rename i into x4. rewrite Zlength_cons' in H.
destruct r. rewrite Zlength_nil in H; omega. rename i into x5. rewrite Zlength_cons' in H.
destruct r. rewrite Zlength_nil in H; omega. rename i into x6. rewrite Zlength_cons' in H.
destruct r. rewrite Zlength_nil in H; omega. rename i into x7. rewrite Zlength_cons' in H.
destruct r. rewrite Zlength_nil in H; omega. rename i into x8. rewrite Zlength_cons' in H.
destruct r. rewrite Zlength_nil in H; omega. rename i into x9. rewrite Zlength_cons' in H.
destruct r. rewrite Zlength_nil in H; omega. rename i into x10. rewrite Zlength_cons' in H.
destruct r. rewrite Zlength_nil in H; omega. rename i into x11. rewrite Zlength_cons' in H.
destruct r. rewrite Zlength_nil in H; omega. rename i into x12. rewrite Zlength_cons' in H.
destruct r. rewrite Zlength_nil in H; omega. rename i into x13. rewrite Zlength_cons' in H.
destruct r. rewrite Zlength_nil in H; omega. rename i into x14. rewrite Zlength_cons' in H.
destruct r. rewrite Zlength_nil in H; omega. rename i into x15. rewrite Zlength_cons' in H.
destruct r. Focus 2. rewrite Zlength_cons' in H. specialize (Zlength_nonneg r); intros. omega. clear H.
destruct W as [HW H1]; simpl in *. unfold Znth in H1. simpl in H1.
destruct H1 as [t0 [t1 [t2 [t3 [T0 [T1 [T2 [T3 [w1 [[_ H1] W1]]]]]]]]]]. 
destruct H1 as [t4 [t5 [t6 [t7 [T4 [T5 [T6 [T7 [w2 [[_ H1] W2]]]]]]]]]].
destruct H1 as [t8 [t9 [t10 [t11 [T8 [T9 [T10 [T11 [w3 [[_ H1] W3]]]]]]]]]].
destruct H1 as [t12 [t13 [t14 [t15 [T12 [T13 [T14 [T15 [w4 [[_ H4] [_ W4]]]]]]]]]]]. subst w4.
symmetry in T0; inv T0. symmetry in T1; inv T1. symmetry in T2; inv T2. symmetry in T3; inv T3.
symmetry in T4; inv T4. symmetry in T5; inv T5. symmetry in T6; inv T6. symmetry in T7; inv T7.
symmetry in T8; inv T8. symmetry in T9; inv T9. symmetry in T10; inv T10. symmetry in T11; inv T11.
symmetry in T12; inv T12. symmetry in T13; inv T13. symmetry in T14; inv T14. symmetry in T15; inv T15.
remember (Int.xor x4(Int.rol (Int.add x0 x12) (Int.repr 7))) as z1.
remember (Int.xor x8 (Int.rol (Int.add z1 x0) (Int.repr 9))) as z2.
remember (Int.xor x12 (Int.rol (Int.add z2 z1) (Int.repr 13))) as z3.
destruct W3 as [_ W3]; simpl in W3. 
 rewrite Zmod_small in W3. 2: omega.
 rewrite Zmod_small in W3. 2: omega.
 rewrite Zmod_small in W3. 2: omega.
 rewrite Zmod_small in W3. 2: omega.
 unfold upd_Znth_in_list at 8 in W3. rewrite Zlength_correct in W3;  unfold sublist in W3; simpl in W3. 
 unfold upd_Znth_in_list at 7 in W3. rewrite Zlength_correct in W3;  unfold sublist in W3; simpl in W3. 
 unfold upd_Znth_in_list at 6 in W3. rewrite Zlength_correct in W3;  unfold sublist in W3; simpl in W3. 
 unfold upd_Znth_in_list at 5 in W3. rewrite Zlength_correct in W3;  unfold sublist in W3; simpl in W3. 
 unfold upd_Znth_in_list at 4 in W3. rewrite Zlength_correct in W3;  unfold sublist in W3; simpl in W3. 
 unfold upd_Znth_in_list at 3 in W3. rewrite Zlength_correct in W3;  unfold sublist in W3; simpl in W3. 
 unfold upd_Znth_in_list at 2 in W3. rewrite Zlength_correct in W3;  unfold sublist in W3; simpl in W3. 
 unfold upd_Znth_in_list at 1 in W3. rewrite Zlength_correct in W3;  unfold sublist in W3; simpl in W3. 
remember (Int.xor x0 (Int.rol (Int.add z3 z2) (Int.repr 18))) as z0.
remember (Int.xor x9 (Int.rol (Int.add x5 x1) (Int.repr 7))) as z6.
remember (Int.xor x13 (Int.rol (Int.add z6 x5) (Int.repr 9))) as z7.
remember (Int.xor x1 (Int.rol (Int.add z7 z6) (Int.repr 13))) as z4.
remember (Int.xor x5 (Int.rol (Int.add z4 z7) (Int.repr 18))) as z5. subst w2.
destruct W2 as [_ W2]; simpl in W2. 
 unfold upd_Znth_in_list at 4 in W2. rewrite Zlength_correct in W2;  unfold sublist in W2; simpl in W2. 
 unfold upd_Znth_in_list at 3 in W2. rewrite Zlength_correct in W2;  unfold sublist in W2; simpl in W2. 
 unfold upd_Znth_in_list at 2 in W2. rewrite Zlength_correct in W2;  unfold sublist in W2; simpl in W2. 
 unfold upd_Znth_in_list at 1 in W2. rewrite Zlength_correct in W2;  unfold sublist in W2; simpl in W2. 
remember (Int.xor x14 (Int.rol (Int.add x10 x6) (Int.repr 7))) as z11.
remember (Int.xor x2 (Int.rol (Int.add z11 x10) (Int.repr 9))) as z8.
remember (Int.xor x6 (Int.rol (Int.add z8 z11) (Int.repr 13))) as z9.
remember (Int.xor x10 (Int.rol (Int.add z9 z8) (Int.repr 18))) as z10. subst w1.
destruct W1 as [_ W1]; simpl in W1.
 unfold upd_Znth_in_list at 4 in W1. rewrite Zlength_correct in W1;  unfold sublist in W1; simpl in W1. 
 unfold upd_Znth_in_list at 3 in W1. rewrite Zlength_correct in W1;  unfold sublist in W1; simpl in W1. 
 unfold upd_Znth_in_list at 2 in W1. rewrite Zlength_correct in W1;  unfold sublist in W1; simpl in W1. 
 unfold upd_Znth_in_list at 1 in W1. rewrite Zlength_correct in W1;  unfold sublist in W1; simpl in W1. 
remember (Int.xor x3 (Int.rol (Int.add x15 x11) (Int.repr 7))) as z12.
remember (Int.xor x7 (Int.rol (Int.add z12 x15) (Int.repr 9))) as z13.
remember (Int.xor x11 (Int.rol (Int.add z13 z12) (Int.repr 13))) as z14.
remember (Int.xor x15 (Int.rol (Int.add z14 z13) (Int.repr 18))) as z15.
subst wlist; simpl. unfold snuffleRound. simpl.
(*rewrite Int.xor_commut in Heqz0, Heqz1, Heqz2, Heqz3, Heqz4, Heqz5, Heqz6,
  Heqz7, Heqz8, Heqz9, Heqz10, Heqz11, Heqz12, Heqz13, Heqz14, Heqz15.*)
rewrite Int.add_commut in Heqz0, Heqz2, Heqz3, Heqz4, Heqz5, Heqz7, Heqz8,
  Heqz9, Heqz10, Heqz13, Heqz14, Heqz15.
subst z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15. reflexivity.
Qed.

Lemma f_core_loop3: forall (Espec : OracleKind)
c k h nonce out w x y t OUT (xI:list int)
(data : SixteenByte * SixteenByte * (SixteenByte * SixteenByte))
(*(OUTlen : length OUT = 64%nat)*)
(out' : name _out)
(in' : name _in)
(k' : name _k)
(c' : name _c)
(h' : name _h)
(aux' : name _aux)
(XIZ: Zlength xI = 16),
@semax CompSpecs Espec
  (initialized_list [_i] (func_tycontext f_core SalsaVarSpecs SalsaFunSpecs))
  (PROP  ()
   LOCAL  (temp _i (Vint (Int.repr 16)); lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(data_at Tsh (tarray tuint 16) (map Vint xI) y);
   `(data_at Tsh (tarray tuint 16) (map Vint xI) x);
   `(data_at_ Tsh (tarray tuint 4) t); `(data_at_ Tsh (tarray tuint 16) w);
   `(CoreInSEP data (nonce, c, k));
   `(data_at Tsh (tarray tuchar 64) OUT out)))
  (Sfor (Sset _i (Econst_int (Int.repr 0) tint))
     (Ebinop Olt (Etempvar _i tint) (Econst_int (Int.repr 20) tint) tint)
     (Ssequence
        (Sfor (Sset _j (Econst_int (Int.repr 0) tint))
           (Ebinop Olt (Etempvar _j tint) (Econst_int (Int.repr 4) tint) tint)
           (Ssequence
              (Sfor (Sset _m (Econst_int (Int.repr 0) tint))
                 (Ebinop Olt (Etempvar _m tint)
                    (Econst_int (Int.repr 4) tint) tint)
                 (Ssequence
                    (Sset _index
                       (Ebinop Omod
                          (Ebinop Oadd
                             (Ebinop Omul (Econst_int (Int.repr 5) tint)
                                (Etempvar _j tint) tint)
                             (Ebinop Omul (Econst_int (Int.repr 4) tint)
                                (Etempvar _m tint) tint) tint)
                          (Econst_int (Int.repr 16) tint) tint))
                    (Ssequence
                       (Sset _aux
                          (Ederef
                             (Ebinop Oadd (Evar _x (tarray tuint 16))
                                (Etempvar _index tint) (tptr tuint)) tuint))
                       (Sassign
                          (Ederef
                             (Ebinop Oadd (Evar _t (tarray tuint 4))
                                (Etempvar _m tint) (tptr tuint)) tuint)
                          (Etempvar _aux tuint))))
                 (Sset _m
                    (Ebinop Oadd (Etempvar _m tint)
                       (Econst_int (Int.repr 1) tint) tint)))
              (Ssequence
                 (Ssequence
                    (Sset _aux
                       (Ederef
                          (Ebinop Oadd (Evar _t (tarray tuint 4))
                             (Econst_int (Int.repr 0) tint) (tptr tuint))
                          tuint))
                    (Ssequence
                       (Sset _aux1
                          (Ederef
                             (Ebinop Oadd (Evar _t (tarray tuint 4))
                                (Econst_int (Int.repr 3) tint) (tptr tuint))
                             tuint))
                       (Ssequence
                          (Sset _aux
                             (Ebinop Oadd (Etempvar _aux tuint)
                                (Etempvar _aux1 tuint) tuint))
                          (Ssequence
                             (Ssequence
                                (Scall (Some 181%positive)
                                   (Evar _L32
                                      (Tfunction
                                         (Tcons tuint (Tcons tint Tnil))
                                         tuint cc_default))
                                   [Etempvar _aux tuint;
                                   Econst_int (Int.repr 7) tint])
                                (Sset _aux (Etempvar 181%positive tuint)))
                             (Ssequence
                                (Sset _aux1
                                   (Ederef
                                      (Ebinop Oadd (Evar _t (tarray tuint 4))
                                         (Econst_int (Int.repr 1) tint)
                                         (tptr tuint)) tuint))
                                (Ssequence
                                   (Sset _aux1
                                      (Ebinop Oxor (Etempvar _aux1 tuint)
                                         (Etempvar _aux tuint) tuint))
                                   (Sassign
                                      (Ederef
                                         (Ebinop Oadd
                                            (Evar _t (tarray tuint 4))
                                            (Econst_int (Int.repr 1) tint)
                                            (tptr tuint)) tuint)
                                      (Etempvar _aux1 tuint))))))))
                 (Ssequence
                    (Ssequence
                       (Sset _aux
                          (Ederef
                             (Ebinop Oadd (Evar _t (tarray tuint 4))
                                (Econst_int (Int.repr 1) tint) (tptr tuint))
                             tuint))
                       (Ssequence
                          (Sset _aux1
                             (Ederef
                                (Ebinop Oadd (Evar _t (tarray tuint 4))
                                   (Econst_int (Int.repr 0) tint)
                                   (tptr tuint)) tuint))
                          (Ssequence
                             (Sset _aux
                                (Ebinop Oadd (Etempvar _aux tuint)
                                   (Etempvar _aux1 tuint) tuint))
                             (Ssequence
                                (Ssequence
                                   (Scall (Some 182%positive)
                                      (Evar _L32
                                         (Tfunction
                                            (Tcons tuint (Tcons tint Tnil))
                                            tuint cc_default))
                                      [Etempvar _aux tuint;
                                      Econst_int (Int.repr 9) tint])
                                   (Sset _aux (Etempvar 182%positive tuint)))
                                (Ssequence
                                   (Sset _aux1
                                      (Ederef
                                         (Ebinop Oadd
                                            (Evar _t (tarray tuint 4))
                                            (Econst_int (Int.repr 2) tint)
                                            (tptr tuint)) tuint))
                                   (Ssequence
                                      (Sset _aux1
                                         (Ebinop Oxor (Etempvar _aux1 tuint)
                                            (Etempvar _aux tuint) tuint))
                                      (Sassign
                                         (Ederef
                                            (Ebinop Oadd
                                               (Evar _t (tarray tuint 4))
                                               (Econst_int (Int.repr 2) tint)
                                               (tptr tuint)) tuint)
                                         (Etempvar _aux1 tuint))))))))
                    (Ssequence
                       (Ssequence
                          (Sset _aux
                             (Ederef
                                (Ebinop Oadd (Evar _t (tarray tuint 4))
                                   (Econst_int (Int.repr 2) tint)
                                   (tptr tuint)) tuint))
                          (Ssequence
                             (Sset _aux1
                                (Ederef
                                   (Ebinop Oadd (Evar _t (tarray tuint 4))
                                      (Econst_int (Int.repr 1) tint)
                                      (tptr tuint)) tuint))
                             (Ssequence
                                (Sset _aux
                                   (Ebinop Oadd (Etempvar _aux tuint)
                                      (Etempvar _aux1 tuint) tuint))
                                (Ssequence
                                   (Ssequence
                                      (Scall (Some 183%positive)
                                         (Evar _L32
                                            (Tfunction
                                               (Tcons tuint (Tcons tint Tnil))
                                               tuint cc_default))
                                         [Etempvar _aux tuint;
                                         Econst_int (Int.repr 13) tint])
                                      (Sset _aux
                                         (Etempvar 183%positive tuint)))
                                   (Ssequence
                                      (Sset _aux1
                                         (Ederef
                                            (Ebinop Oadd
                                               (Evar _t (tarray tuint 4))
                                               (Econst_int (Int.repr 3) tint)
                                               (tptr tuint)) tuint))
                                      (Ssequence
                                         (Sset _aux1
                                            (Ebinop Oxor
                                               (Etempvar _aux1 tuint)
                                               (Etempvar _aux tuint) tuint))
                                         (Sassign
                                            (Ederef
                                               (Ebinop Oadd
                                                  (Evar _t (tarray tuint 4))
                                                  (Econst_int (Int.repr 3)
                                                     tint) (tptr tuint))
                                               tuint) (Etempvar _aux1 tuint))))))))
                       (Ssequence
                          (Ssequence
                             (Sset _aux
                                (Ederef
                                   (Ebinop Oadd (Evar _t (tarray tuint 4))
                                      (Econst_int (Int.repr 3) tint)
                                      (tptr tuint)) tuint))
                             (Ssequence
                                (Sset _aux1
                                   (Ederef
                                      (Ebinop Oadd (Evar _t (tarray tuint 4))
                                         (Econst_int (Int.repr 2) tint)
                                         (tptr tuint)) tuint))
                                (Ssequence
                                   (Sset _aux
                                      (Ebinop Oadd (Etempvar _aux tuint)
                                         (Etempvar _aux1 tuint) tuint))
                                   (Ssequence
                                      (Ssequence
                                         (Scall (Some 184%positive)
                                            (Evar _L32
                                               (Tfunction
                                                  (Tcons tuint
                                                     (Tcons tint Tnil)) tuint
                                                  cc_default))
                                            [Etempvar _aux tuint;
                                            Econst_int (Int.repr 18) tint])
                                         (Sset _aux
                                            (Etempvar 184%positive tuint)))
                                      (Ssequence
                                         (Sset _aux1
                                            (Ederef
                                               (Ebinop Oadd
                                                  (Evar _t (tarray tuint 4))
                                                  (Econst_int (Int.repr 0)
                                                     tint) (tptr tuint))
                                               tuint))
                                         (Ssequence
                                            (Sset _aux1
                                               (Ebinop Oxor
                                                  (Etempvar _aux1 tuint)
                                                  (Etempvar _aux tuint) tuint))
                                            (Sassign
                                               (Ederef
                                                  (Ebinop Oadd
                                                     (Evar _t
                                                        (tarray tuint 4))
                                                     (Econst_int (Int.repr 0)
                                                        tint) (tptr tuint))
                                                  tuint)
                                               (Etempvar _aux1 tuint))))))))
                          (Sfor (Sset _m (Econst_int (Int.repr 0) tint))
                             (Ebinop Olt (Etempvar _m tint)
                                (Econst_int (Int.repr 4) tint) tint)
                             (Ssequence
                                (Sset _aux
                                   (Ederef
                                      (Ebinop Oadd (Evar _t (tarray tuint 4))
                                         (Etempvar _m tint) (tptr tuint))
                                      tuint))
                                (Ssequence
                                   (Sset _aux1
                                      (Ebinop Oadd
                                         (Ebinop Omul
                                            (Econst_int (Int.repr 4) tint)
                                            (Etempvar _j tint) tint)
                                         (Ebinop Omod
                                            (Ebinop Oadd (Etempvar _j tint)
                                               (Etempvar _m tint) tint)
                                            (Econst_int (Int.repr 4) tint)
                                            tint) tint))
                                   (Sassign
                                      (Ederef
                                         (Ebinop Oadd
                                            (Evar _w (tarray tuint 16))
                                            (Etempvar _aux1 tuint)
                                            (tptr tuint)) tuint)
                                      (Etempvar _aux tuint))))
                             (Sset _m
                                (Ebinop Oadd (Etempvar _m tint)
                                   (Econst_int (Int.repr 1) tint) tint))))))))
           (Sset _j
              (Ebinop Oadd (Etempvar _j tint) (Econst_int (Int.repr 1) tint)
                 tint)))
        (Sfor (Sset _m (Econst_int (Int.repr 0) tint))
           (Ebinop Olt (Etempvar _m tint) (Econst_int (Int.repr 16) tint)
              tint)
           (Ssequence
              (Sset _aux
                 (Ederef
                    (Ebinop Oadd (Evar _w (tarray tuint 16))
                       (Etempvar _m tint) (tptr tuint)) tuint))
              (Sassign
                 (Ederef
                    (Ebinop Oadd (Evar _x (tarray tuint 16))
                       (Etempvar _m tint) (tptr tuint)) tuint)
                 (Etempvar _aux tuint)))
           (Sset _m
              (Ebinop Oadd (Etempvar _m tint) (Econst_int (Int.repr 1) tint)
                 tint))))
     (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint)))
  (normal_ret_assert
  (PROP  ()
   LOCAL  (temp _i (Vint (Int.repr 20)); lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
   lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w; temp _in nonce;
   temp _out out; temp _c c; temp _k k; temp _h (Vint (Int.repr h)))
   SEP 
   (`(EX r:_, !!(Snuffle 20 xI = Some r) && data_at Tsh (tarray tuint 16) (map Vint r) x);
   `(data_at Tsh (tarray tuint 16) (map Vint xI) y);
   `(data_at_ Tsh (tarray tuint 4) t); `(data_at_ Tsh (tarray tuint 16) w);
   `(CoreInSEP data (nonce, c, k)); 
   `(data_at Tsh (tarray tuchar 64) OUT out)))).
Proof. intros. abbreviate_semax.
Opaque Zplus. Opaque Z.mul. Opaque mult. Opaque plus.
 (*  Opaque firstn. Opaque skipn.*) Opaque Z.sub. Opaque Snuffle.
drop_LOCAL 0%nat. 
LENBforward_for_simple_bound 20 (EX i:Z, 
  (PROP  ()
   LOCAL  (lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(data_at Tsh (tarray tuint 16) (map Vint xI) y);
   `(EX r:_, !!(Snuffle (Z.to_nat i) xI = Some r) && data_at Tsh (tarray tuint 16) (map Vint r) x);
   `(data_at_ Tsh (tarray tuint 4) t); `(data_at_ Tsh (tarray tuint 16) w);
   `(CoreInSEP data (nonce, c, k)); `(data_at Tsh (tarray tuchar 64) OUT out)))).
{ entailer. apply (exp_right xI). entailer. }

(*Issue: why doesn't this work if we move it to the end of the proof of this lemma, 
  after the other subgoal has been proven?*)
Focus 2. entailer. apply (exp_right r). entailer. cancel. 

{ rename H into I.
  normalize. intros r; normalize. rename H into R. 
  assert (XI: length xI = 16%nat). eapply (Zlength_length _ _ 16). omega. trivial.
  assert (RL:= Snuffle_length _ _ _ R XI).
  assert (RZL: Zlength r = 16). rewrite Zlength_correct, RL; reflexivity.
            
  LENBforward_for_simple_bound 4 (EX j:Z,
  (PROP  ()
   LOCAL  (temp _i (Vint (Int.repr i)); lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(data_at Tsh (tarray tuint 16) (map Vint r) x);
   `(data_at Tsh (tarray tuint 16) (map Vint xI) y);
   `(data_at_ Tsh (tarray tuint 4) t); 
   `(EX l:_, !!(WcontI r (Z.to_nat j) l) && data_at Tsh (tarray tuint 16) (map Vint l) w);
   `(CoreInSEP data (nonce, c, k));
   `(data_at Tsh (tarray tuchar 64) OUT out)))).
  { entailer. apply (exp_right r). entailer. cancel. admit. (* TODO: WAS data_at_ length: should be ok once we have data_at_ tarray enforcing correct length*) }
  { rename H into J. rename i0 into j.
    normalize. intros wlist. normalize. rename H into WCONT.
    destruct (WcontI_length _ _ _ WCONT) as [_ WL].
    destruct (Znth_mapVint r ((5 * j + 4 * 0) mod 16) Vundef) as [t0 T0].
      rewrite RZL; apply Z_mod_lt; omega.
    destruct (Znth_mapVint r ((5 * j + 4 * 1) mod 16) Vundef) as [t1 T1].
      rewrite RZL; apply Z_mod_lt; omega.
    destruct (Znth_mapVint r ((5 * j + 4 * 2) mod 16) Vundef) as [t2 T2].
      rewrite RZL; apply Z_mod_lt; omega.
    destruct (Znth_mapVint r ((5 * j + 4 * 3) mod 16) Vundef) as [t3 T3].
      rewrite RZL; apply Z_mod_lt; omega.
    eapply semax_post'. 2: apply Jbody; trivial; try eassumption.
    entailer. apply (exp_right W); entailer. 
    apply andp_right. 2: cancel.
    apply prop_right.
    rewrite Z.add_comm, Z2Nat.inj_add; try omega.
    assert (X: (Z.to_nat 1 + Z.to_nat j = S (Z.to_nat j))%nat) by reflexivity.
    rewrite X. simpl. split. rewrite Zlength_map in H19; assumption. 
    exists t0, t1, t2, t3. rewrite Z2Nat.id, T0, T1, T2, T3.
    split. trivial. split. trivial. split. trivial. split. trivial.
    exists wlist. split; trivial. omega. }

  normalize. intros wlist. normalize. rename H into WLIST.
  assert (WL: Zlength wlist = 16) by apply WLIST.
  eapply semax_post'.
  Focus 2. apply array_copy3; trivial. (*TODO: change definition of array3 so that at least the first side conditions is about Zlength*)
            rewrite map_length. apply Zlength_length in WL. apply WL. omega. 
            rewrite map_length. eapply Snuffle_length. eassumption.
            assumption.
            intros. apply Znth_mapVint. omega. 
  entailer.
  apply (exp_right wlist). entailer.
  apply andp_right. 2: cancel.
  apply prop_right.
  rewrite Z.add_comm, Z2Nat.inj_add; try omega.
  Transparent Snuffle. Transparent plus. simpl. rewrite R.
  simpl. apply WWI; assumption. }
Qed.

