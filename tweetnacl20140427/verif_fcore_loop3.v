Require Import VST.floyd.proofauto.
Local Open Scope logic.
Require Import List. Import ListNotations.
Require Import ZArith.
Require Import tweetnacl20140427.tweetNaclBase.
Require Import tweetnacl20140427.Salsa20.
Require Import tweetnacl20140427.verif_salsa_base.
Require Import tweetnacl20140427.tweetnaclVerifiableC.
Require Import tweetnacl20140427.Snuffle.
Require Import tweetnacl20140427.spec_salsa.

Require Import tweetnacl20140427.verif_fcore_jbody.

Opaque Snuffle.Snuffle.

Lemma SnuffleS i l: Snuffle (S i) l = bind (Snuffle i l) (Snuffle 1). reflexivity. Qed.

Fixpoint WcontI (xs: list int) (j:nat) (l:list val):Prop :=
   match j with O => Zlength l = 16
   | (S n) => Zlength l = 16 /\
              exists t0 t1 t2 t3,
              Znth ((5 * (Z.of_nat n) + 4 * 0) mod 16) (map Vint xs) = Vint t0 /\
              Znth ((5 * (Z.of_nat n) + 4 * 1) mod 16) (map Vint xs) = Vint t1 /\
              Znth ((5 * (Z.of_nat n) + 4 * 2) mod 16) (map Vint xs) = Vint t2 /\
              Znth ((5 * (Z.of_nat n) + 4 * 3) mod 16) (map Vint xs) = Vint t3 /\
              exists wl, WcontI xs n wl /\
                match Wcopyspec t0 t1 t2 t3 with
                 (s0,s1,s2,s3) => wlistJ' wl (Z.of_nat n) s0 s1 s2 s3 l
                end
  end.

Lemma WcontI_Zlength xs j l: WcontI xs j l -> Zlength l=16.
Proof. intros. destruct j; eapply H. Qed.

Lemma WWI r w (W: WcontI r 4 w) (R:Zlength r = 16):
      exists wi, w=map Vint wi /\ snuffleRound r = Some wi.
Proof.
apply listD16 in R.
destruct R as [x0 [x1 [x2 [x3 [x4 [x5 [x6 [x7
              [x8 [x9 [x10 [x11 [x12 [x13 [x14 [x15 XX]]]]]]]]]]]]]]]]. subst r.
destruct W as [HW H1].
destruct H1 as [t0 [t1 [t2 [t3 [T0 [T1 [T2 [T3 [w1 [[_ H1] W1]]]]]]]]]]. simpl in T0, T1, T2, T3.
rewrite Z.mod_small in T0. 2: omega.
rewrite Zmod_eq in T1. 2: omega.
rewrite Zmod_eq in T2. 2: omega.
rewrite Zmod_eq in T3. 2: omega. simpl in T0, T1, T2, T3.
destruct H1 as [t4 [t5 [t6 [t7 [T4 [T5 [T6 [T7 [w2 [[_ H1] W2]]]]]]]]]]. simpl in T4, T5, T6, T7.
rewrite Zmod_eq in T4. 2: omega.
rewrite Zmod_eq in T5. 2: omega.
rewrite Zmod_eq in T6. 2: omega.
rewrite Zmod_eq in T7. 2: omega. simpl in T4, T5, T6, T7.
destruct H1 as [t8 [t9 [t10 [t11 [T8 [T9 [T10 [T11 [w3 [[_ H1] W3]]]]]]]]]]. simpl in T8, T9, T10, T11.
rewrite Z.mod_small in T8. 2: omega.
rewrite Z.mod_small in T9. 2: omega.
rewrite Zmod_eq in T10. 2: omega.
rewrite Zmod_eq in T11. 2: omega. simpl in T8, T9, T10, T11.
destruct H1 as [t12 [t13 [t14 [t15 [T12 [T13 [T14 [T15 [w4 [L4 W4]]]]]]]]]]. simpl in T12, T13, T14, T15.
rewrite Z.mod_small in T12. 2: omega.
rewrite Z.mod_small in T13. 2: omega.
rewrite Z.mod_small in T14. 2: omega.
rewrite Z.mod_small in T15. 2: omega.
unfold Znth in *. simpl in  T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15.
symmetry in T0; inv T0. symmetry in T1; inv T1. symmetry in T2; inv T2. symmetry in T3; inv T3.
symmetry in T4; inv T4. symmetry in T5; inv T5. symmetry in T6; inv T6. symmetry in T7; inv T7.
symmetry in T8; inv T8. symmetry in T9; inv T9. symmetry in T10; inv T10. symmetry in T11; inv T11.
symmetry in T12; inv T12. symmetry in T13; inv T13. symmetry in T14; inv T14. symmetry in T15; inv T15.
red in L4.
simpl in W4.
remember (Int.xor x4 (Int.rol (Int.add x0 x12) (Int.repr 7))) as z1.
remember (Int.xor x8 (Int.rol (Int.add z1 x0) (Int.repr 9))) as z2.
remember (Int.xor x12 (Int.rol (Int.add z2 z1) (Int.repr 13))) as z3.
remember (Int.xor x0 (Int.rol (Int.add z3 z2) (Int.repr 18))) as z0.
apply listD16 in L4.
destruct L4 as [y0 [y1 [y2 [y3 [y4 [y5 [y6 [y7
               [y8 [y9 [y10 [y11 [y12 [y13 [y14 [y15 XX]]]]]]]]]]]]]]]]. subst w4.
destruct W4 as [_ W4]; simpl in W4.
(*rewrite Z.mod_small in W4. 2: omega.
rewrite Z.mod_small in W4. 2: omega.
rewrite Z.mod_small in W4. 2: omega.
rewrite Z.mod_small in W4. 2: omega.*)
unfold upd_Znth, sublist in W4; simpl in W4. subst w3.
simpl in W3.
remember (Int.xor x9 (Int.rol (Int.add x5 x1) (Int.repr 7))) as z6.
remember (Int.xor x13 (Int.rol (Int.add z6 x5) (Int.repr 9))) as z7.
remember (Int.xor x1 (Int.rol (Int.add z7 z6) (Int.repr 13))) as z4.
remember (Int.xor x5 (Int.rol (Int.add z4 z7) (Int.repr 18))) as z5.
destruct W3 as [_ W3]; simpl in W3.
unfold upd_Znth, sublist in W3; simpl in W3. subst w2.
destruct W2 as [_ W2]. simpl in W2.
remember (Int.xor x14 (Int.rol (Int.add x10 x6) (Int.repr 7))) as z11.
remember (Int.xor x2 (Int.rol (Int.add z11 x10) (Int.repr 9))) as z8.
remember (Int.xor x6 (Int.rol (Int.add z8 z11) (Int.repr 13))) as z9.
remember (Int.xor x10 (Int.rol (Int.add z9 z8) (Int.repr 18))) as z10.
unfold upd_Znth, sublist in W2; simpl in W2. subst w1.
destruct W1 as [_ W1]; simpl in W1.
remember (Int.xor x3 (Int.rol (Int.add x15 x11) (Int.repr 7))) as z12.
remember (Int.xor x7 (Int.rol (Int.add z12 x15) (Int.repr 9))) as z13.
remember (Int.xor x11 (Int.rol (Int.add z13 z12) (Int.repr 13))) as z14.
remember (Int.xor x15 (Int.rol (Int.add z14 z13) (Int.repr 18))) as z15.
unfold upd_Znth, sublist in W1; simpl in W1. subst w. clear HW.
exists [z0; z1; z2; z3; z4; z5; z6; z7;
        z8; z9; z10; z11; z12; z13; z14; z15].
split. reflexivity.
rewrite Int.add_commut in Heqz0, Heqz2, Heqz3, Heqz4, Heqz5, Heqz7, Heqz8,
  Heqz9, Heqz10, Heqz13, Heqz14, Heqz15.
subst z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15. reflexivity.
Qed.

Definition array_copy3_statement:=
Sfor (Sset _m (Econst_int (Int.repr 0) tint))
     (Ebinop Olt (Etempvar _m tint) (Econst_int (Int.repr 16) tint) tint)
     (Ssequence
        (Sset _t'19
           (Ederef
              (Ebinop Oadd (Evar _w (tarray tuint 16)) (Etempvar _m tint)
                 (tptr tuint)) tuint))
        (Sassign
           (Ederef
              (Ebinop Oadd (Evar _x (tarray tuint 16)) (Etempvar _m tint)
                 (tptr tuint)) tuint) (Etempvar _t'19 tuint)))
     (Sset _m
        (Ebinop Oadd (Etempvar _m tint) (Econst_int (Int.repr 1) tint) tint)).

Lemma array_copy3 Espec:
forall FR c k h nonce out
       i w x y t (xlist wlist:list val)
       (WZ: forall m, 0<=m<16 -> exists mval, Znth m wlist =Vint mval),
@semax CompSpecs Espec
  (func_tycontext f_core SalsaVarSpecs SalsaFunSpecs nil)
  (PROP  ()
   LOCAL  (temp _j (Vint (Int.repr 4)); temp _i (Vint (Int.repr i)); lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (FR; data_at Tsh (tarray tuint 16) wlist w;
         data_at Tsh (tarray tuint 16) xlist x)) 
 array_copy3_statement
  (normal_ret_assert
  (PROP  ()
   LOCAL  (temp _j (Vint (Int.repr 4)); temp _i (Vint (Int.repr i)); lvar _t (tarray tuint 4) t;
      lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
      lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
      temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (FR; data_at Tsh (tarray tuint 16) wlist w;
         data_at Tsh (tarray tuint 16) wlist x))).
Proof. intros. abbreviate_semax.
Time assert_PROP (Zlength wlist = 16 /\ Zlength xlist = 16) as WXL by entailer!. (*1.4 versus 5.4*)
destruct WXL as [WL XL].
unfold array_copy3_statement.
Time forward_for_simple_bound 16 (EX m:Z,
  (PROP  ()
   LOCAL  (temp _j (Vint (Int.repr 4)); temp _i (Vint (Int.repr i)); lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (FR; data_at Tsh (tarray tuint 16) wlist w;
         EX mlist:_, !!(forall mm, 0<=mm<m -> Znth mm mlist = Znth mm wlist)
                && data_at Tsh (tarray tuint 16) mlist x))).
  (*1.2 versus 2.7*)
{ Exists xlist. Time entailer!. (*2.6 versus 6.7*) intros; omega. }
{ Intros mlist. rename H into M. rename i0 into m. rename H0 into HM.
  destruct (WZ _ M) as [mval MVAL].
  freeze [0;2] FR1.
  Time forward; change (@Znth val Vundef) with (@Znth val _); rewrite MVAL. (*3.5 versus 8.7*)
  Time solve[entailer!]. (*0.9 versus 3.3*)
  thaw FR1.
  Time assert_PROP (Zlength mlist = 16) as ML by entailer!. (*1.2 versus 3.5*)
  Time forward. (*3.2 versus 9*)
   { Exists (upd_Znth m mlist (Vint mval)).
     Time entailer!. (*2.8 versus 5.6*)
     intros mm ?.
     destruct (zeq mm m); subst.
     + rewrite MVAL, upd_Znth_same; trivial. omega.
     + rewrite <- HM. 2: omega.
       apply upd_Znth_diff; trivial; omega. }
}
{ Time entailer!. (*1.8 versus 4.3*)
  Intros mlist.
  assert_PROP (Zlength mlist = 16) as ML by entailer.
  apply derives_refl'. f_equal.
  eapply Znth_extensional. omega.
  intros kk K. apply H2. omega. }
Time Qed. (*June 4th, 2017 (laptop): 1s*)

Definition f_core_loop3_statement :=
Sfor (Sset _i (Econst_int (Int.repr 0) tint))
     (Ebinop Olt (Etempvar _i tint) (Econst_int (Int.repr 20) tint) tint)
     (Ssequence
        (Sfor (Sset _j (Econst_int (Int.repr 0) tint))
           (Ebinop Olt (Etempvar _j tint) (Econst_int (Int.repr 4) tint) tint)
           (Ssequence
              (Sfor (Sset _m (Econst_int (Int.repr 0) tint))
                 (Ebinop Olt (Etempvar _m tint)
                    (Econst_int (Int.repr 4) tint) tint)
                 (Ssequence
                    (Sset _t'33
                       (Ederef
                          (Ebinop Oadd (Evar _x (tarray tuint 16))
                             (Ebinop Omod
                                (Ebinop Oadd
                                   (Ebinop Omul
                                      (Econst_int (Int.repr 5) tint)
                                      (Etempvar _j tint) tint)
                                   (Ebinop Omul
                                      (Econst_int (Int.repr 4) tint)
                                      (Etempvar _m tint) tint) tint)
                                (Econst_int (Int.repr 16) tint) tint)
                             (tptr tuint)) tuint))
                    (Sassign
                       (Ederef
                          (Ebinop Oadd (Evar _t (tarray tuint 4))
                             (Etempvar _m tint) (tptr tuint)) tuint)
                       (Etempvar _t'33 tuint)))
                 (Sset _m
                    (Ebinop Oadd (Etempvar _m tint)
                       (Econst_int (Int.repr 1) tint) tint)))
              (Ssequence
                 (Ssequence
                    (Ssequence
                       (Sset _t'31
                          (Ederef
                             (Ebinop Oadd (Evar _t (tarray tuint 4))
                                (Econst_int (Int.repr 0) tint) (tptr tuint))
                             tuint))
                       (Ssequence
                          (Sset _t'32
                             (Ederef
                                (Ebinop Oadd (Evar _t (tarray tuint 4))
                                   (Econst_int (Int.repr 3) tint)
                                   (tptr tuint)) tuint))
                          (Scall (Some _t'5)
                             (Evar _L32
                                (Tfunction (Tcons tuint (Tcons tint Tnil))
                                   tuint cc_default))
                             [Ebinop Oadd (Etempvar _t'31 tuint)
                                (Etempvar _t'32 tuint) tuint;
                             Econst_int (Int.repr 7) tint])))
                    (Ssequence
                       (Sset _t'30
                          (Ederef
                             (Ebinop Oadd (Evar _t (tarray tuint 4))
                                (Econst_int (Int.repr 1) tint) (tptr tuint))
                             tuint))
                       (Sassign
                          (Ederef
                             (Ebinop Oadd (Evar _t (tarray tuint 4))
                                (Econst_int (Int.repr 1) tint) (tptr tuint))
                             tuint)
                          (Ebinop Oxor (Etempvar _t'30 tuint)
                             (Etempvar _t'5 tuint) tuint))))
                 (Ssequence
                    (Ssequence
                       (Ssequence
                          (Sset _t'28
                             (Ederef
                                (Ebinop Oadd (Evar _t (tarray tuint 4))
                                   (Econst_int (Int.repr 1) tint)
                                   (tptr tuint)) tuint))
                          (Ssequence
                             (Sset _t'29
                                (Ederef
                                   (Ebinop Oadd (Evar _t (tarray tuint 4))
                                      (Econst_int (Int.repr 0) tint)
                                      (tptr tuint)) tuint))
                             (Scall (Some _t'6)
                                (Evar _L32
                                   (Tfunction (Tcons tuint (Tcons tint Tnil))
                                      tuint cc_default))
                                [Ebinop Oadd (Etempvar _t'28 tuint)
                                   (Etempvar _t'29 tuint) tuint;
                                Econst_int (Int.repr 9) tint])))
                       (Ssequence
                          (Sset _t'27
                             (Ederef
                                (Ebinop Oadd (Evar _t (tarray tuint 4))
                                   (Econst_int (Int.repr 2) tint)
                                   (tptr tuint)) tuint))
                          (Sassign
                             (Ederef
                                (Ebinop Oadd (Evar _t (tarray tuint 4))
                                   (Econst_int (Int.repr 2) tint)
                                   (tptr tuint)) tuint)
                             (Ebinop Oxor (Etempvar _t'27 tuint)
                                (Etempvar _t'6 tuint) tuint))))
                    (Ssequence
                       (Ssequence
                          (Ssequence
                             (Sset _t'25
                                (Ederef
                                   (Ebinop Oadd (Evar _t (tarray tuint 4))
                                      (Econst_int (Int.repr 2) tint)
                                      (tptr tuint)) tuint))
                             (Ssequence
                                (Sset _t'26
                                   (Ederef
                                      (Ebinop Oadd (Evar _t (tarray tuint 4))
                                         (Econst_int (Int.repr 1) tint)
                                         (tptr tuint)) tuint))
                                (Scall (Some _t'7)
                                   (Evar _L32
                                      (Tfunction
                                         (Tcons tuint (Tcons tint Tnil))
                                         tuint cc_default))
                                   [Ebinop Oadd (Etempvar _t'25 tuint)
                                      (Etempvar _t'26 tuint) tuint;
                                   Econst_int (Int.repr 13) tint])))
                          (Ssequence
                             (Sset _t'24
                                (Ederef
                                   (Ebinop Oadd (Evar _t (tarray tuint 4))
                                      (Econst_int (Int.repr 3) tint)
                                      (tptr tuint)) tuint))
                             (Sassign
                                (Ederef
                                   (Ebinop Oadd (Evar _t (tarray tuint 4))
                                      (Econst_int (Int.repr 3) tint)
                                      (tptr tuint)) tuint)
                                (Ebinop Oxor (Etempvar _t'24 tuint)
                                   (Etempvar _t'7 tuint) tuint))))
                       (Ssequence
                          (Ssequence
                             (Ssequence
                                (Sset _t'22
                                   (Ederef
                                      (Ebinop Oadd (Evar _t (tarray tuint 4))
                                         (Econst_int (Int.repr 3) tint)
                                         (tptr tuint)) tuint))
                                (Ssequence
                                   (Sset _t'23
                                      (Ederef
                                         (Ebinop Oadd
                                            (Evar _t (tarray tuint 4))
                                            (Econst_int (Int.repr 2) tint)
                                            (tptr tuint)) tuint))
                                   (Scall (Some _t'8)
                                      (Evar _L32
                                         (Tfunction
                                            (Tcons tuint (Tcons tint Tnil))
                                            tuint cc_default))
                                      [Ebinop Oadd (Etempvar _t'22 tuint)
                                         (Etempvar _t'23 tuint) tuint;
                                      Econst_int (Int.repr 18) tint])))
                             (Ssequence
                                (Sset _t'21
                                   (Ederef
                                      (Ebinop Oadd (Evar _t (tarray tuint 4))
                                         (Econst_int (Int.repr 0) tint)
                                         (tptr tuint)) tuint))
                                (Sassign
                                   (Ederef
                                      (Ebinop Oadd (Evar _t (tarray tuint 4))
                                         (Econst_int (Int.repr 0) tint)
                                         (tptr tuint)) tuint)
                                   (Ebinop Oxor (Etempvar _t'21 tuint)
                                      (Etempvar _t'8 tuint) tuint))))
                          (Sfor (Sset _m (Econst_int (Int.repr 0) tint))
                             (Ebinop Olt (Etempvar _m tint)
                                (Econst_int (Int.repr 4) tint) tint)
                             (Ssequence
                                (Sset _t'20
                                   (Ederef
                                      (Ebinop Oadd (Evar _t (tarray tuint 4))
                                         (Etempvar _m tint) (tptr tuint))
                                      tuint))
                                (Sassign
                                   (Ederef
                                      (Ebinop Oadd
                                         (Evar _w (tarray tuint 16))
                                         (Ebinop Oadd
                                            (Ebinop Omul
                                               (Econst_int (Int.repr 4) tint)
                                               (Etempvar _j tint) tint)
                                            (Ebinop Omod
                                               (Ebinop Oadd
                                                  (Etempvar _j tint)
                                                  (Etempvar _m tint) tint)
                                               (Econst_int (Int.repr 4) tint)
                                               tint) tint) (tptr tuint))
                                      tuint) (Etempvar _t'20 tuint)))
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
              (Sset _t'19
                 (Ederef
                    (Ebinop Oadd (Evar _w (tarray tuint 16))
                       (Etempvar _m tint) (tptr tuint)) tuint))
              (Sassign
                 (Ederef
                    (Ebinop Oadd (Evar _x (tarray tuint 16))
                       (Etempvar _m tint) (tptr tuint)) tuint)
                 (Etempvar _t'19 tuint)))
           (Sset _m
              (Ebinop Oadd (Etempvar _m tint) (Econst_int (Int.repr 1) tint)
                 tint))))
     (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint)).

Lemma f_core_loop3: forall (Espec : OracleKind) FR
c k h nonce out w x y t (xI:list int),
@semax CompSpecs Espec
  (func_tycontext f_core SalsaVarSpecs SalsaFunSpecs nil)
  (PROP  ()
   LOCAL  (temp _i (Vint (Int.repr 16)); lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (FR; data_at_ Tsh (tarray tuint 4) t;
         data_at_ Tsh (tarray tuint 16) w;
         data_at Tsh (tarray tuint 16) (map Vint xI) x))
 f_core_loop3_statement
  (normal_ret_assert
  (PROP  ()
   LOCAL  (temp _i (Vint (Int.repr 20)); lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
       lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w; temp _in nonce;
       temp _out out; temp _c c; temp _k k; temp _h (Vint (Int.repr h)))
   SEP (FR; data_at_ Tsh (tarray tuint 4) t; data_at_ Tsh (tarray tuint 16) w;
        EX r:_, !!(Snuffle 20 xI = Some r) &&
           data_at Tsh (tarray tuint 16) (map Vint r) x))).
Proof. intros. abbreviate_semax.
unfold f_core_loop3_statement.
freeze [0;1;2] FR1.
Time assert_PROP (Zlength (map Vint xI) = 16) as XIZ by entailer!. (*0.9*)
thaw FR1.
rewrite Zlength_map in XIZ.
drop_LOCAL 0%nat.
Time forward_for_simple_bound 20 (EX i:Z,
  (PROP  ()
   LOCAL  (lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (FR; data_at_ Tsh (tarray tuint 4) t; data_at_ Tsh (tarray tuint 16) w;
         EX r:_, !!(Snuffle (Z.to_nat i) xI = Some r) &&
             data_at Tsh (tarray tuint 16) (map Vint r) x))). (*0.9*)
{ Exists xI. Time entailer!. (*2.6*) }

{ rename H into I. Intros r. rename H into R.
  assert (XI: length xI = 16%nat). eapply (Zlength_length _ _ 16). omega. trivial.
  assert (RL:= Snuffle_length _ _ _ R XI).
  assert (RZL: Zlength r = 16). rewrite Zlength_correct, RL; reflexivity.

  Time forward_for_simple_bound 4 (EX j:Z,
  (PROP  ()
   LOCAL  (temp _i (Vint (Int.repr i)); lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (FR; data_at_ Tsh (tarray tuint 4) t;
      EX l:_, !!(WcontI r (Z.to_nat j) l) && data_at Tsh (tarray tuint 16) l w;
      data_at Tsh (tarray tuint 16) (map Vint r) x))). (*1.5*)
  { Time entailer!. (*2.5*) Exists (list_repeat 16 Vundef). Time entailer!. (*0.1*) }
  { rename H into J. rename i0 into j.
    Intros wlist. rename H into WCONT.
    destruct (Znth_mapVint r ((5 * j + 4 * 0) mod 16)) as [t0 T0].
      rewrite RZL; apply Z_mod_lt; omega.
    destruct (Znth_mapVint r ((5 * j + 4 * 1) mod 16)) as [t1 T1].
      rewrite RZL; apply Z_mod_lt; omega.
    destruct (Znth_mapVint r ((5 * j + 4 * 2) mod 16)) as [t2 T2].
      rewrite RZL; apply Z_mod_lt; omega.
    destruct (Znth_mapVint r ((5 * j + 4 * 3) mod 16)) as [t3 T3].
      rewrite RZL; apply Z_mod_lt; omega. 
    eapply semax_post_flipped'.
    apply (Jbody _ FR c k h nonce out w x y t i j r I J wlist _ _ _ _ T0 T1 T2 T3).
    Intros W. Exists W.
    Time entailer!. (*6.1*) (*TODO: eliminate old_go_lower*)
    rewrite Z.add_comm, Z2Nat.inj_add; try omega.
    assert (X: (Z.to_nat 1 + Z.to_nat j = S (Z.to_nat j))%nat) by reflexivity.
    rewrite X. simpl. split. assumption.
    exists t0, t1, t2, t3. simpl in T0, T1, T2, T3. rewrite Z2Nat.id, T0, T1, T2, T3.
    repeat split; trivial.
    exists wlist. split; trivial. omega. }

  Intros wlist. rename H into HW.
  destruct (WWI _ _ HW RZL) as [wints [WI SNUFF]]. subst wlist.
  freeze [0;1] FR2.
  eapply semax_post_flipped'.
  apply (array_copy3 _ (FRZL FR2) c k h nonce out
                  i w x y t (map Vint r) (map Vint wints)); trivial.
           intros. apply Znth_mapVint.
              destruct (snuffleRound_length _ _ SNUFF) as [WL _].
              rewrite Zlength_correct, WL; simpl; omega.
  Exists wints. rewrite Z.add_comm, Z2Nat.inj_add; try omega.
  Time entailer!. (*4.3*)(*TODO: eliminate old_go_lower*)
  rewrite SnuffleS, R; trivial.
  thaw FR2; cancel. }
 apply ENTAIL_refl.
Time Qed. (*June4th, 2017 (laptop): Finished transaction in 1.781 secs (1.072u,0.028s) (successful)*)