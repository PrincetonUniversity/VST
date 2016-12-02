Require Import Recdef.
Require Import floyd.proofauto.
Local Open Scope logic.
Require Import List. Import ListNotations.
Require Import sha.general_lemmas.

Require Import tweetnacl20140427.split_array_lemmas.
Require Import ZArith. 
Require Import tweetnacl20140427.tweetNaclBase.
Require Import tweetnacl20140427.Salsa20.
Require Import tweetnacl20140427.verif_salsa_base.
Require Import tweetnacl20140427.tweetnaclVerifiableC.
Require Import tweetnacl20140427.spec_salsa. Opaque Snuffle.Snuffle.
Require Import floyd.library.
Opaque littleendian.
    Opaque littleendian_invert. Opaque Snuffle20. Opaque prepare_data. 
    Opaque QuadByte2ValList. Opaque fcore_result.

Definition wlistJ' (wlist:list val) (j: Z) (t0 t1 t2 t3:int) (l: list val): Prop :=
  Zlength l = 16 /\ 
  l = upd_Znth (4 * j + (j + 3) mod 4)
       (upd_Znth (4 * j + (j + 2) mod 4)
         (upd_Znth (4 * j + (j + 1) mod 4)
          (upd_Znth (4 * j + (j + 0) mod 4) wlist (Vint t0))
          (Vint t1)) (Vint t2)) (Vint t3).

Fixpoint WLIST' (wlist : list val) (tlist: list int) (j:Z) m l :=
  match m with 
    O => l=wlist
  | S m' => exists l' tm, 
            Zlength l = Zlength wlist /\
            WLIST' wlist tlist j m' l' /\
            Znth (Z.of_nat m') (map Vint tlist) Vundef = Vint tm /\
            l = upd_Znth (4*j+ ((j+Z.of_nat m') mod 4)) l' (Vint tm)
  end.

Lemma WLIST'_length wlist tlist j : forall m l, WLIST' wlist tlist j m l -> Zlength l=Zlength wlist.
Proof. induction m; simpl; intros; subst; trivial.
  destruct H as [l' [tm [ L [W [ZZ LL]]]]]. subst. apply IHm in W; trivial.
Qed.

Definition Wcopyspec (t0 t1 t2 t3: int):=
(Int.xor t0
        (Int.rol
           (Int.add
              (Int.xor t3
                 (Int.rol
                    (Int.add
                       (Int.xor t2
                          (Int.rol
                             (Int.add
                                (Int.xor t1
                                   (Int.rol (Int.add t0 t3) (Int.repr 7))) t0)
                             (Int.repr 9)))
                       (Int.xor t1 (Int.rol (Int.add t0 t3) (Int.repr 7))))
                    (Int.repr 13)))
              (Int.xor t2
                 (Int.rol
                    (Int.add
                       (Int.xor t1 (Int.rol (Int.add t0 t3) (Int.repr 7))) t0)
                    (Int.repr 9)))) (Int.repr 18)),
  Int.xor t1 (Int.rol (Int.add t0 t3) (Int.repr 7)),
  Int.xor t2
       (Int.rol
          (Int.add (Int.xor t1 (Int.rol (Int.add t0 t3) (Int.repr 7))) t0)
          (Int.repr 9)),
  Int.xor t3
       (Int.rol
          (Int.add
             (Int.xor t2
                (Int.rol
                   (Int.add
                      (Int.xor t1 (Int.rol (Int.add t0 t3) (Int.repr 7))) t0)
                   (Int.repr 9)))
             (Int.xor t1 (Int.rol (Int.add t0 t3) (Int.repr 7))))
          (Int.repr 13))). 

Lemma SixteenWR_Znth_int' s i:
  0 <= i < 16 -> exists ii : int, Znth i (SixteenWordRep s) Vundef = Vint ii.
Proof. apply SixteenWR_Znth_int. Qed.

Definition array_copy1_statement :=
     (Sfor (Sset _m (Econst_int (Int.repr 0) tint))
        (Ebinop Olt (Etempvar _m tint) (Econst_int (Int.repr 4) tint) tint)
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
           (Ebinop Oadd (Etempvar _m tint) (Econst_int (Int.repr 1) tint)
              tint))).

Lemma array_copy1: forall (Espec: OracleKind) j t x (xs:list int) 
  (J:0<=j<4),
 semax (initialized_list [_i; _j]
     (func_tycontext f_core SalsaVarSpecs SalsaFunSpecs))
  (PROP  ()
   LOCAL  (temp _j (Vint (Int.repr j));
   lvar _t (tarray tuint 4) t;
   lvar _x (tarray tuint 16) x)
   SEP  (data_at_ Tsh (tarray tuint 4) t; 
           data_at Tsh (tarray tuint 16) (@map int val Vint xs) x))
   array_copy1_statement
  (normal_ret_assert 
  (PROP  ()
   LOCAL  (temp _m (Vint (Int.repr 4)); temp _j (Vint (Int.repr j));
   lvar _t (tarray tuint 4) t;
   lvar _x (tarray tuint 16) x)
   SEP  (data_at Tsh (tarray tuint 16) (map Vint xs) x;
     EX  l : list val,
     !!(forall mm : Z,
         0 <= mm < 4 ->
         Znth mm l Vundef =
         Znth ((5 * j + 4 * mm) mod 16) (map Vint xs) Vundef)
        && data_at Tsh (tarray tuint 4) l t))).
Proof. intros. unfold array_copy1_statement. abbreviate_semax.
  assert_PROP (Zlength (map Vint xs) = 16) as XL by entailer!. (*1*)
  forward_for_simple_bound 4
 (EX m:Z, 
  (PROP  ()
   LOCAL  (temp _j (Vint (Int.repr j)); lvar _t (tarray tuint 4) t;
   lvar _x (tarray tuint 16) x)
   SEP  (EX l:_, !!(forall mm, 0<=mm<m -> Znth mm l Vundef = 
                  Znth ((5*j+4*mm) mod 16) (map Vint xs) Vundef)
            && data_at Tsh (tarray tuint 4) l t; 
       data_at Tsh (tarray tuint 16) (map Vint xs) x))).
  (*1.3*)
  { Exists (list_repeat 4 Vundef). (*Time*) entailer!. (*2.2*)  intros; omega. }
  { rename i into m. rename H into M. Intros T.
    rename H into HT.
    (*Time*) assert_PROP (Zlength T = 4) as TL by entailer!. (*2.2 versus 5.7*)
    destruct (Z_mod_lt (5 * j + 4 * m) 16) as [M1 M2]. omega.
    destruct (Znth_mapVint xs ((5 * j + 4 * m) mod 16) Vundef) as [v NV].
       simpl in XL. rewrite <- (Zlength_map _ _ Vint xs), XL. split; assumption.
    remember ((Int.eq (Int.repr (5 * j + 4 * m))
                         (Int.repr Int.min_signed) &&
                       Int.eq (Int.repr 16) Int.mone)%bool).
    destruct b; simpl.
       { apply andb_true_eq in Heqb. destruct Heqb. 
         apply binop_lemmas2.int_eq_true in H0.
          assert (IS: Int.signed (Int.repr 16) = 
                  Int.signed (Int.repr (-1))) by (rewrite H0; trivial).  clear - IS.
          rewrite Int.signed_repr in IS. 2: rewrite int_max_signed_eq, int_min_signed_eq; omega. 
          rewrite Int.signed_repr in IS. omega. rewrite int_max_signed_eq, int_min_signed_eq; omega. }
    (*Time*) forward. (*2.5*)
    { (*Time*) entailer!. (*1.9 versus 6.6*) rewrite <- Heqb. simpl; trivial. }
    unfold sem_mod, sem_binarith, both_int; simpl. rewrite ?mul_repr, ?add_repr, <- Heqb. simpl.
    unfold Int.mods. repeat rewrite Int.signed_repr.
      2: rewrite int_max_signed_eq, int_min_signed_eq; omega.
      2: rewrite int_max_signed_eq, int_min_signed_eq; omega.
    rewrite Z.rem_mod_nonneg; try omega.
    (*Time*) forward; rewrite NV. (*4.5 versus 15*)
    (*Time*) solve[entailer!]. (*1.1 versus 5.4*)
    (*Time*) forward. (*3.9 versus 14.7*)
    { Exists (upd_Znth m T (Vint v)).
      (*Time*) entailer!. (*4.2 versus 8.9*)
      intros mm ?. 
      destruct (zeq mm m); subst.
      + rewrite upd_Znth_same; try omega. rewrite NV; trivial.
      + rewrite upd_Znth_diff; try omega. apply HT; omega. } 
  }
entailer!.
Time Qed. (*19*) 

Definition Jbody_statement :=
  (Ssequence array_copy1_statement
     (Ssequence
        (Ssequence
           (Sset _aux
              (Ederef
                 (Ebinop Oadd (Evar _t (tarray tuint 4))
                    (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint))
           (Ssequence
              (Sset _aux1
                 (Ederef
                    (Ebinop Oadd (Evar _t (tarray tuint 4))
                       (Econst_int (Int.repr 3) tint) (tptr tuint)) tuint))
              (Ssequence
                 (Sset _aux
                    (Ebinop Oadd (Etempvar _aux tuint) (Etempvar _aux1 tuint)
                       tuint))
                 (Ssequence
                    (Ssequence
                       (Scall (Some 181%positive)
                          (Evar _L32
                             (Tfunction (Tcons tuint (Tcons tint Tnil)) tuint
                                cc_default))
                          [Etempvar _aux tuint; Econst_int (Int.repr 7) tint])
                       (Sset _aux (Etempvar 181%positive tuint)))
                    (Ssequence
                       (Sset _aux1
                          (Ederef
                             (Ebinop Oadd (Evar _t (tarray tuint 4))
                                (Econst_int (Int.repr 1) tint) (tptr tuint))
                             tuint))
                       (Ssequence
                          (Sset _aux1
                             (Ebinop Oxor (Etempvar _aux1 tuint)
                                (Etempvar _aux tuint) tuint))
                          (Sassign
                             (Ederef
                                (Ebinop Oadd (Evar _t (tarray tuint 4))
                                   (Econst_int (Int.repr 1) tint)
                                   (tptr tuint)) tuint)
                             (Etempvar _aux1 tuint))))))))
        (Ssequence
           (Ssequence
              (Sset _aux
                 (Ederef
                    (Ebinop Oadd (Evar _t (tarray tuint 4))
                       (Econst_int (Int.repr 1) tint) (tptr tuint)) tuint))
              (Ssequence
                 (Sset _aux1
                    (Ederef
                       (Ebinop Oadd (Evar _t (tarray tuint 4))
                          (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint))
                 (Ssequence
                    (Sset _aux
                       (Ebinop Oadd (Etempvar _aux tuint)
                          (Etempvar _aux1 tuint) tuint))
                    (Ssequence
                       (Ssequence
                          (Scall (Some 182%positive)
                             (Evar _L32
                                (Tfunction (Tcons tuint (Tcons tint Tnil))
                                   tuint cc_default))
                             [Etempvar _aux tuint;
                             Econst_int (Int.repr 9) tint])
                          (Sset _aux (Etempvar 182%positive tuint)))
                       (Ssequence
                          (Sset _aux1
                             (Ederef
                                (Ebinop Oadd (Evar _t (tarray tuint 4))
                                   (Econst_int (Int.repr 2) tint)
                                   (tptr tuint)) tuint))
                          (Ssequence
                             (Sset _aux1
                                (Ebinop Oxor (Etempvar _aux1 tuint)
                                   (Etempvar _aux tuint) tuint))
                             (Sassign
                                (Ederef
                                   (Ebinop Oadd (Evar _t (tarray tuint 4))
                                      (Econst_int (Int.repr 2) tint)
                                      (tptr tuint)) tuint)
                                (Etempvar _aux1 tuint))))))))
           (Ssequence
              (Ssequence
                 (Sset _aux
                    (Ederef
                       (Ebinop Oadd (Evar _t (tarray tuint 4))
                          (Econst_int (Int.repr 2) tint) (tptr tuint)) tuint))
                 (Ssequence
                    (Sset _aux1
                       (Ederef
                          (Ebinop Oadd (Evar _t (tarray tuint 4))
                             (Econst_int (Int.repr 1) tint) (tptr tuint))
                          tuint))
                    (Ssequence
                       (Sset _aux
                          (Ebinop Oadd (Etempvar _aux tuint)
                             (Etempvar _aux1 tuint) tuint))
                       (Ssequence
                          (Ssequence
                             (Scall (Some 183%positive)
                                (Evar _L32
                                   (Tfunction (Tcons tuint (Tcons tint Tnil))
                                      tuint cc_default))
                                [Etempvar _aux tuint;
                                Econst_int (Int.repr 13) tint])
                             (Sset _aux (Etempvar 183%positive tuint)))
                          (Ssequence
                             (Sset _aux1
                                (Ederef
                                   (Ebinop Oadd (Evar _t (tarray tuint 4))
                                      (Econst_int (Int.repr 3) tint)
                                      (tptr tuint)) tuint))
                             (Ssequence
                                (Sset _aux1
                                   (Ebinop Oxor (Etempvar _aux1 tuint)
                                      (Etempvar _aux tuint) tuint))
                                (Sassign
                                   (Ederef
                                      (Ebinop Oadd (Evar _t (tarray tuint 4))
                                         (Econst_int (Int.repr 3) tint)
                                         (tptr tuint)) tuint)
                                   (Etempvar _aux1 tuint))))))))
              (Ssequence
                 (Ssequence
                    (Sset _aux
                       (Ederef
                          (Ebinop Oadd (Evar _t (tarray tuint 4))
                             (Econst_int (Int.repr 3) tint) (tptr tuint))
                          tuint))
                    (Ssequence
                       (Sset _aux1
                          (Ederef
                             (Ebinop Oadd (Evar _t (tarray tuint 4))
                                (Econst_int (Int.repr 2) tint) (tptr tuint))
                             tuint))
                       (Ssequence
                          (Sset _aux
                             (Ebinop Oadd (Etempvar _aux tuint)
                                (Etempvar _aux1 tuint) tuint))
                          (Ssequence
                             (Ssequence
                                (Scall (Some 184%positive)
                                   (Evar _L32
                                      (Tfunction
                                         (Tcons tuint (Tcons tint Tnil))
                                         tuint cc_default))
                                   [Etempvar _aux tuint;
                                   Econst_int (Int.repr 18) tint])
                                (Sset _aux (Etempvar 184%positive tuint)))
                             (Ssequence
                                (Sset _aux1
                                   (Ederef
                                      (Ebinop Oadd (Evar _t (tarray tuint 4))
                                         (Econst_int (Int.repr 0) tint)
                                         (tptr tuint)) tuint))
                                (Ssequence
                                   (Sset _aux1
                                      (Ebinop Oxor (Etempvar _aux1 tuint)
                                         (Etempvar _aux tuint) tuint))
                                   (Sassign
                                      (Ederef
                                         (Ebinop Oadd
                                            (Evar _t (tarray tuint 4))
                                            (Econst_int (Int.repr 0) tint)
                                            (tptr tuint)) tuint)
                                      (Etempvar _aux1 tuint))))))))
                 (Sfor (Sset _m (Econst_int (Int.repr 0) tint))
                    (Ebinop Olt (Etempvar _m tint)
                       (Econst_int (Int.repr 4) tint) tint)
                    (Ssequence
                       (Sset _aux
                          (Ederef
                             (Ebinop Oadd (Evar _t (tarray tuint 4))
                                (Etempvar _m tint) (tptr tuint)) tuint))
                       (Ssequence
                          (Sset _aux1
                             (Ebinop Oadd
                                (Ebinop Omul (Econst_int (Int.repr 4) tint)
                                   (Etempvar _j tint) tint)
                                (Ebinop Omod
                                   (Ebinop Oadd (Etempvar _j tint)
                                      (Etempvar _m tint) tint)
                                   (Econst_int (Int.repr 4) tint) tint) tint))
                          (Sassign
                             (Ederef
                                (Ebinop Oadd (Evar _w (tarray tuint 16))
                                   (Etempvar _aux1 tuint) (tptr tuint)) tuint)
                             (Etempvar _aux tuint))))
                    (Sset _m
                       (Ebinop Oadd (Etempvar _m tint)
                          (Econst_int (Int.repr 1) tint) tint)))))))).


Lemma Jbody (Espec : OracleKind) FR c k h nonce out w x y t i j xs
  (I : 0 <= i < 20)
  (J : 0 <= j < 4)
  wlist
  t0 t1 t2 t3
  (T0: Znth ((5*j+4*0) mod 16) (map Vint xs) Vundef = Vint t0)
  (T1: Znth ((5*j+4*1) mod 16) (map Vint  xs) Vundef = Vint t1)
  (T2: Znth ((5*j+4*2) mod 16) (map Vint xs) Vundef = Vint t2)
  (T3: Znth ((5*j+4*3) mod 16) (map Vint xs) Vundef = Vint t3):
@semax CompSpecs Espec
  (initialized_list [_i; _j]
     (func_tycontext f_core SalsaVarSpecs SalsaFunSpecs))
  (PROP  ()
   LOCAL  (temp _j (Vint (Int.repr j)); temp _i (Vint (Int.repr i));
   lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
   lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w; temp _in nonce;
   temp _out out; temp _c c; temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (FR; data_at_ Tsh (tarray tuint 4) t;
         data_at Tsh (tarray tuint 16) (*(map Vint wlist)*) wlist w;
         data_at Tsh (tarray tuint 16) (map Vint xs) x))
  Jbody_statement
  (normal_ret_assert
     (PROP  (0 <= j + 1 <= 4)
      LOCAL  (temp _j (Vint (Int.repr j)); temp _i (Vint (Int.repr i));
      lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
      lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w;
      temp _in nonce; temp _out out; temp _c c; temp _k k;
      temp _h (Vint (Int.repr h)))
      SEP  (FR; data_at Tsh (tarray tuint 16) (map Vint xs) x;
          data_at_ Tsh (tarray tuint 4) t; 
          EX W:_, 
             !!(match Wcopyspec t0 t1 t2 t3 with
                 (s0,s1,s2,s3) => wlistJ' wlist j s0 s1 s2 s3 W
                end) 
             && data_at Tsh (tarray tuint 16) (*(map Vint W)*)W w))). 
Proof. intros. abbreviate_semax.
  semax_frame [ ] [ FR ].
  forward_seq.
 {
  semax_frame [   temp _i (Vint (Int.repr i));  lvar _y (tarray tuint 16) y;
     lvar _w (tarray tuint 16) w; temp _in nonce;
     temp _out out; temp _c c; temp _k k; temp _h (Vint (Int.repr h))]
    [ data_at Tsh (tarray tuint 16) wlist w ].
  apply array_copy1; trivial. }
  abbreviate_semax. simpl app.
  Intros tlist.
  rename H into HT.

  assert_PROP (tlist = map Vint [t0; t1;t2;t3]) as TLI. {
   entailer!.
   clear - HT H3 T0 T1 T2 T3. rename H3 into TL.
   rewrite Zlength_correct in TL. change 4 with (Z.of_nat 4) in TL.
   apply Nat2Z.inj in TL.
   destruct tlist as [ | x0 [ | x1 [ | x2 [ | x3 [ | ]]]]]; inv TL.
   rewrite <- HT in T0,T1,T2,T3 by omega.
   rewrite <- T0, <- T1, <- T2, <- T3. reflexivity.
 }
  subst tlist.
  clear T0 T1 T2 T3 HT.

Ltac compute_Znth :=
 let xx := fresh in 
   set (xx := (Znth _ (map Vint (_::_)) _));
   compute in xx; 
   subst xx.

Ltac compute_upd_Znth := 
 let xx := fresh "xx" in 
   set (xx := (upd_Znth _ (map Vint (_::_)) (Vint _)));
   pattern xx;
  match goal with |- ?G xx => 
  let g := fresh "G" in set (g:=G);
  revert xx;
  unfold upd_Znth, Zlength, sublist;
  simpl; rewrite <- (map_nil Vint), <- ?map_cons;
  subst g; cbv beta
 end.

  (*pattern1*)
  forward. compute_Znth.
  forward. compute_Znth.
  forward.
  forward_call (Int.add t0 t3, Int.repr 7).
  forward. compute_Znth.
  forward.
  remember (Int.xor t1 (Int.rol (Int.add t0 t3) (Int.repr 7))) as tt0.
  forward. compute_upd_Znth.

  (*VST Issue: mkConciseDelta SalsaVarSpecs SalsaFunSpecs f_core Delta. doesn't work any longer*)
  (*pattern2*)
  forward. compute_Znth.
  forward. compute_Znth.
  forward. 
  forward_call (Int.add tt0 t0, Int.repr 9). 
  forward. compute_Znth.
  forward. 
  remember (Int.xor t2 (Int.rol (Int.add tt0 t0) (Int.repr 9))) as tt1.
  forward. compute_upd_Znth.

  (*pattern3*)
  forward. compute_Znth.
  forward. compute_Znth.
  forward.
  forward_call (Int.add tt1 tt0, Int.repr 13).
  forward. compute_Znth.
  forward.
  remember (Int.xor t3 (Int.rol (Int.add tt1 tt0) (Int.repr 13))) as tt2.
  forward. compute_upd_Znth.

  (*pattern4*)
  forward. compute_Znth.
  forward. compute_Znth.
  forward.
  forward_call (Int.add tt2 tt1, Int.repr 18).
  forward. compute_Znth.
  forward.
  remember (Int.xor t0 (Int.rol (Int.add tt2 tt1) (Int.repr 18))) as tt3.
  forward. compute_upd_Znth.

(* delete _aux1*) drop_LOCAL 0%nat.
(* delete _aux*) drop_LOCAL 0%nat.
(* delete old m*) drop_LOCAL 0%nat.
(*Time*) assert_PROP (Zlength wlist=16) as WL by entailer!. (*1.6 versus 4.4*)

  subst POSTCONDITION; unfold abbreviate.
  
  semax_frame [
   lvar _x (tarray tuint 16) x;
   temp _i (Vint (Int.repr i));
   lvar _y (tarray tuint 16) y; temp _in nonce;
   temp _out out; temp _c c; temp _k k;
   temp _h (Vint (Int.repr h))]
    [ data_at Tsh (tarray tuint 16) (map Vint xs) x ].

 forward_for_simple_bound 4 (EX m:Z, EX l: list val, 
  (PROP  (WLIST' wlist [tt3; tt0; tt1; tt2] j (Z.to_nat m) l)
   LOCAL  (temp _j (Vint (Int.repr j)); lvar _t (tarray tuint 4) t; lvar _w (tarray tuint 16) w )
   SEP  (data_at Tsh (tarray tuint 4) (map Vint [tt3; tt0; tt1; tt2]) t;
           data_at Tsh (tarray tuint 16) l w))).
   (*1.2 versus 6.3*)
{ Exists wlist. (*Time*) entailer!. (*2.4 versus 6.3*) }
{ rename H into M; rename i0 into m.
  rename x0 into wlist1. Intros. rename H into WLIST1.
  assert (TM: exists tm, Znth m [Vint tt3; Vint tt0; Vint tt1; Vint tt2] Vundef = Vint tm).
    destruct (zeq m 0); subst; simpl. eexists; reflexivity. 
    destruct (zeq m 1); subst; simpl. eexists; reflexivity. 
    destruct (zeq m 2); subst; simpl. eexists; reflexivity. 
    destruct (zeq m 3); subst; simpl. eexists; reflexivity. omega.
  destruct TM as [tm TM].
  (*Time*) forward. (*3.6 versus 11.6*)
  { (*Time*) entailer!. (*1 versus 5*) rewrite TM; simpl; trivial. }
  assert (NEQ: (Int.eq (Int.repr (j + m)) (Int.repr Int.min_signed) &&
                 Int.eq (Int.repr 4) Int.mone)%bool = false).
  { rewrite (Int.eq_false (Int.repr 4)), andb_false_r. simpl; trivial.
    unfold Int.mone. intros N.  
    assert (SGN: Int.signed (Int.repr 4) = Int.signed (Int.repr (-1))).
      rewrite N; trivial.
    rewrite Int.signed_repr, Int.signed_repr in SGN. omega.
    rewrite client_lemmas.int_min_signed_eq, client_lemmas.int_max_signed_eq; omega.
    rewrite client_lemmas.int_min_signed_eq, client_lemmas.int_max_signed_eq; omega. }
  (*Time*) forward. (*2.2 versus 6*)
  { (*Time*) entailer!. (*1.6 versus 5.5*) rewrite NEQ; simpl; trivial. }
  unfold force_val, sem_mod, both_int; simpl.
              unfold sem_cast_neutral, both_int; simpl.
              rewrite mul_repr, add_repr.
              rewrite NEQ. simpl.
  assert (JM: 0 <= Z.rem (j + m) 4 < 4) by (apply Zquot.Zrem_lt_pos_pos; omega).
  assert (A: Int.add (Int.repr (4 * j)) (Int.mods (Int.repr (j + m)) (Int.repr 4))
            = Int.repr (4 * j + (j + m) mod 4)).
             unfold Int.mods.
             rewrite (Int.signed_repr (j+m)).  
             2: rewrite client_lemmas.int_min_signed_eq, client_lemmas.int_max_signed_eq; omega.  
             rewrite (Int.signed_repr 4).  
             2: rewrite client_lemmas.int_min_signed_eq, client_lemmas.int_max_signed_eq; omega.  
             rewrite add_repr. rewrite Z.rem_mod_nonneg. trivial. omega. omega.
  rewrite A; clear A.
  forward.
  { apply prop_right.
    assert (0<= (j + m) mod 4 < 4). apply Z_mod_lt; omega. omega. }
  Exists (upd_Znth (4 * j + (j + m) mod 4) wlist1 (Vint tm)). (*_id0)). *)
  rewrite TM.
  entailer!.

  assert (AP: 0 <= (j + m) mod 4 < 4) by (apply Z_mod_lt; omega).
  rewrite Z.add_comm. rewrite Z2Nat.inj_add; try omega.
    assert (SS: (Z.to_nat 1 + Z.to_nat m)%nat = S (Z.to_nat m)) by reflexivity.
    rewrite SS; simpl.
    exists wlist1, tm.
    assert (WL1: Zlength wlist1 = 16). erewrite WLIST'_length. 2: eassumption. assumption.
    split. rewrite upd_Znth_Zlength. eapply WLIST'_length; eassumption.
           rewrite WL1. omega.
           split. trivial.  
           rewrite Z2Nat.id. split; trivial. omega. }

Intros l. Exists l. 
entailer!. 
split. assumption.
destruct H as [l1 [tm1 [ZL1 [XX1 [Z3 HL1]]]]].
destruct XX1 as [l2 [tm2 [ZL2 [XX2 [Z2 HL2]]]]].
destruct XX2 as [l3 [tm3 [ZL3 [XX3 [Z1 HL3]]]]].
destruct XX3 as [l4 [tm4 [ZL4 [XX4 [Z0 HL4]]]]].
simpl in *.
subst.
rewrite <- Z0, <- Z1, <- Z2, <- Z3.
reflexivity.
Time Qed. (*Finished transaction in 33.191 secs (31.103u,0.051s) (successful)*)

