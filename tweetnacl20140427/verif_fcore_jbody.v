Require Import Recdef.
Require Import floyd.proofauto.
Local Open Scope logic.
Require Import List. Import ListNotations.
Require Import general_lemmas.

Require Import split_array_lemmas.
Require Import ZArith. 
Require Import tweetNaclBase.
Require Import Salsa20.
Require Import verif_salsa_base.
Require Import tweetnaclVerifiableC.
Require Import spec_salsa. Opaque Snuffle.Snuffle.

Opaque littleendian.
    Opaque littleendian_invert. Opaque Snuffle20. Opaque prepare_data. 
    Opaque QuadByte2ValList. Opaque fcore_result.

Lemma pattern1_noStmt Espec Source1 Source2 Target Offset: forall FR
  (S1Range: 0 <= Source1 < 4) (S2Range: 0 <= Source2 < 4) (TgtRange: 0 <= Target < 4)
  (HOffset: 0 < Int.unsigned (Int.repr Offset) < 32)
  ValS1 ValS2 ValTgt (tlist:list val)
  (HS1: Znth Source1 tlist Vundef = Vint ValS1)
  (HS2: Znth Source2 tlist Vundef = Vint ValS2)
  (HTgt: Znth Target tlist Vundef = Vint ValTgt)
  c  i j t y x w out nonce k h,
@semax CompSpecs Espec (initialized_list [_i; _j; _m]
     (func_tycontext f_core SalsaVarSpecs SalsaFunSpecs))
  (PROP  ()
   LOCAL  (temp _i (Vint (Int.repr i)); temp _m (Vint (Int.repr 4));
   temp _j (Vint (Int.repr j)); lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (FR; data_at Tsh (tarray tuint 4) tlist t))
                        (Ssequence
                          (Sset _aux
                            (Ederef
                              (Ebinop Oadd (Evar _t (tarray tuint 4))
                                (Econst_int (Int.repr Source1) tint) (tptr tuint))
                              tuint))
                          (Ssequence
                            (Sset _aux1
                              (Ederef
                                (Ebinop Oadd (Evar _t (tarray tuint 4))
                                  (Econst_int (Int.repr Source2) tint)
                                  (tptr tuint)) tuint))
                            (Ssequence
                              (Sset _aux
                                (Ebinop Oadd (Etempvar _aux tuint)
                                  (Etempvar _aux1 tuint) tuint))
                              (Ssequence
                                (Ssequence
                                  (Scall (Some 182%positive)
                                    (Evar _L32 (Tfunction
                                                 (Tcons tuint
                                                   (Tcons tint Tnil)) tuint
                                                 cc_default))
                                    ((Etempvar _aux tuint) ::
                                     (Econst_int (Int.repr Offset) tint) :: nil))
                                  (Sset _aux (Etempvar 182%positive tuint)))
                                (Ssequence
                                  (Sset _aux1
                                    (Ederef
                                      (Ebinop Oadd (Evar _t (tarray tuint 4))
                                        (Econst_int (Int.repr Target) tint)
                                        (tptr tuint)) tuint))
                                  (Ssequence
                                    (Sset _aux1
                                      (Ebinop Oxor (Etempvar _aux1 tuint)
                                        (Etempvar _aux tuint) tuint))
                                    (Sassign
                                      (Ederef
                                        (Ebinop Oadd
                                          (Evar _t (tarray tuint 4))
                                          (Econst_int (Int.repr Target) tint)
                                          (tptr tuint)) tuint)
                                      (Etempvar _aux1 tuint))))))))
  (normal_ret_assert 
  (PROP  ()
   LOCAL  (temp _i (Vint (Int.repr i)); temp _m (Vint (Int.repr 4));
   temp _j (Vint (Int.repr j)); lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (FR; data_at Tsh (tarray tuint 4) 
        (upd_Znth Target tlist
           (Vint
              (Int.xor ValTgt (Int.rol (Int.add ValS1 ValS2) (Int.repr Offset))))) t))).
Proof. intros. abbreviate_semax.
  Time forward; rewrite HS1. (*3 versus 13.4*)  
  Time solve[entailer!]. (*0.8 versus 4.5*)
  Time forward; rewrite HS2. (*3.3 versus 12*) 
  Time solve[entailer!]. (*0.7 versus 4.5*)
  freeze [0;1] FR1.
  Time forward. (*0.7 versus 4.9*)

  Time forward_call (Int.add ValS1 ValS2, Int.repr Offset). (*2.4 versus 9*)

  thaw FR1.
  Time forward; rewrite HTgt. (*3.4 versus 12.8*) 
  Time solve[entailer!]. (*1 versus 4.7*)
  freeze [0;1] FR2.
  Time forward. (*0.7 versus 5*)
  thaw FR2.
  Time forward. (*3.3 versus 7*)
  Time entailer!. (*1.3 versus 6.2*)
Time Qed. (*22.7 versus 42*) (*NOW: 36secs*)

Lemma pattern2_noStmt Espec Source1 Source2 Target Offset: forall FR
  (S1Range: 0 <= Source1 < 4) (S2Range: 0 <= Source2 < 4) (TgtRange: 0 <= Target < 4)
  (HOffset: 0 < Int.unsigned (Int.repr Offset) < 32)
  ValS1 ValS2 ValTgt (tlist:list val)
  (HS1: Znth Source1 tlist Vundef = Vint ValS1)
  (HS2: Znth Source2 tlist Vundef = Vint ValS2)
  (HTgt: Znth Target tlist Vundef = Vint ValTgt)
  c i j t y x w out nonce k h,
@semax CompSpecs Espec (initialized_list [_i; _j; _m; _aux; _aux1; 182%positive]
     (func_tycontext f_core SalsaVarSpecs SalsaFunSpecs))
  (PROP  ()
   LOCAL  (temp _i (Vint (Int.repr i)); temp _m (Vint (Int.repr 4));
   temp _j (Vint (Int.repr j)); lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (FR; data_at Tsh (tarray tuint 4) tlist t))
  (Ssequence
     (Sset _aux
        (Ederef
           (Ebinop Oadd (Evar _t (tarray tuint 4))
              (Econst_int (Int.repr Source1) tint) (tptr tuint)) tuint))
     (Ssequence
        (Sset _aux1
           (Ederef
              (Ebinop Oadd (Evar _t (tarray tuint 4))
                 (Econst_int (Int.repr Source2) tint) (tptr tuint)) tuint))
        (Ssequence
           (Sset _aux
              (Ebinop Oadd (Etempvar _aux tuint) (Etempvar _aux1 tuint) tuint))
           (Ssequence
              (Ssequence
                 (Scall (Some 183%positive)
                    (Evar _L32
                       (Tfunction (Tcons tuint (Tcons tint Tnil)) tuint
                          cc_default))
                    [Etempvar _aux tuint; Econst_int (Int.repr Offset) tint])
                 (Sset _aux (Etempvar 183%positive tuint)))
              (Ssequence
                 (Sset _aux1
                    (Ederef
                       (Ebinop Oadd (Evar _t (tarray tuint 4))
                          (Econst_int (Int.repr Target) tint) (tptr tuint)) tuint))
                 (Ssequence
                    (Sset _aux1
                       (Ebinop Oxor (Etempvar _aux1 tuint)
                          (Etempvar _aux tuint) tuint))
                    (Sassign
                       (Ederef
                          (Ebinop Oadd (Evar _t (tarray tuint 4))
                             (Econst_int (Int.repr Target) tint) (tptr tuint))
                          tuint) (Etempvar _aux1 tuint))))))))
  (normal_ret_assert 
  (PROP  ()
   LOCAL  (temp _i (Vint (Int.repr i)); temp _m (Vint (Int.repr 4));
   temp _j (Vint (Int.repr j)); lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (FR; data_at Tsh (tarray tuint 4) 
        (upd_Znth Target tlist
           (Vint
              (Int.xor ValTgt (Int.rol (Int.add ValS1 ValS2) (Int.repr Offset))))) t))).
Proof. intros. abbreviate_semax.
  Time forward; rewrite HS1. (*3 versus 13.4*)  
  Time solve[entailer!]. (*0.8 versus 4.5*)
  Time forward; rewrite HS2. (*3.3 versus 12*) 
  Time solve[entailer!]. (*0.7 versus 4.5*)
  freeze [0;1] FR1.
  Time forward. (*0.7 versus 4.9*)

  Time forward_call (Int.add ValS1 ValS2, Int.repr Offset). (*2.5 versus 9*)

  thaw FR1.
  Time forward; rewrite HTgt. (*3.4 versus 12.8*) 
  Time solve[entailer!]. (*1 versus 4.7*)
  freeze [0;1] FR2.
  Time forward. (*0.7 versus 5*)
  thaw FR2.
  Time forward. (*3.3 versus 7*)
  Time entailer!. (*1.3 versus 6.2*)
Time Qed. (*27 versus 44*) (*NOW: 37 secs*)

Lemma pattern3_noStmt Espec Source1 Source2 Target Offset: forall FR
  (S1Range: 0 <= Source1 < 4) (S2Range: 0 <= Source2 < 4) (TgtRange: 0 <= Target < 4)
  (HOffset: 0 < Int.unsigned (Int.repr Offset) < 32)
  ValS1 ValS2 ValTgt (tlist:list val)
  (HS1: Znth Source1 tlist Vundef = Vint ValS1)
  (HS2: Znth Source2 tlist Vundef = Vint ValS2)
  (HTgt: Znth Target tlist Vundef = Vint ValTgt)
  c i j t y x w out nonce k h,
@semax CompSpecs Espec (initialized_list [_i; _j; _m; _aux; _aux1; 183%positive; 182%positive]
     (func_tycontext f_core SalsaVarSpecs SalsaFunSpecs))
  (PROP  ()
   LOCAL  (temp _i (Vint (Int.repr i)); temp _m (Vint (Int.repr 4));
   temp _j (Vint (Int.repr j)); lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (FR; data_at Tsh (tarray tuint 4) tlist t))
  (Ssequence
     (Sset _aux
        (Ederef
           (Ebinop Oadd (Evar _t (tarray tuint 4))
              (Econst_int (Int.repr Source1) tint) (tptr tuint)) tuint))
     (Ssequence
        (Sset _aux1
           (Ederef
              (Ebinop Oadd (Evar _t (tarray tuint 4))
                 (Econst_int (Int.repr Source2) tint) (tptr tuint)) tuint))
        (Ssequence
           (Sset _aux
              (Ebinop Oadd (Etempvar _aux tuint) (Etempvar _aux1 tuint) tuint))
           (Ssequence
              (Ssequence
                 (Scall (Some 184%positive)
                    (Evar _L32
                       (Tfunction (Tcons tuint (Tcons tint Tnil)) tuint
                          cc_default))
                    [Etempvar _aux tuint; Econst_int (Int.repr Offset) tint])
                 (Sset _aux (Etempvar 184%positive tuint)))
              (Ssequence
                 (Sset _aux1
                    (Ederef
                       (Ebinop Oadd (Evar _t (tarray tuint 4))
                          (Econst_int (Int.repr Target) tint) (tptr tuint)) tuint))
                 (Ssequence
                    (Sset _aux1
                       (Ebinop Oxor (Etempvar _aux1 tuint)
                          (Etempvar _aux tuint) tuint))
                    (Sassign
                       (Ederef
                          (Ebinop Oadd (Evar _t (tarray tuint 4))
                             (Econst_int (Int.repr Target) tint) (tptr tuint))
                          tuint) (Etempvar _aux1 tuint))))))))
  (normal_ret_assert 
  (PROP  ()
   LOCAL  (temp _i (Vint (Int.repr i)); temp _m (Vint (Int.repr 4));
   temp _j (Vint (Int.repr j)); lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (FR; data_at Tsh (tarray tuint 4) 
        (upd_Znth Target tlist
           (Vint
              (Int.xor ValTgt (Int.rol (Int.add ValS1 ValS2) (Int.repr Offset)))))
        t))).
Proof. intros. abbreviate_semax.
  Time forward; rewrite HS1. (*3.4 versus 13.4*)  
  Time solve[entailer!]. (*0.8 versus 4.5*)
  Time forward; rewrite HS2. (*5.1 versus 12*) 
  Time solve[entailer!]. (*0.8 versus 4.5*)
  freeze [0;1] FR1.
  Time forward. (*0.9 versus 4.9*)

  Time forward_call (Int.add ValS1 ValS2, Int.repr Offset). (*2.5 versus 9*)

  thaw FR1.
  Time forward; rewrite HTgt. (*3.4 versus 12.8*) 
  Time solve[entailer!]. (*1 versus 4.7*)
  freeze [0;1] FR2.
  Time forward. (*0.7 versus 5*)
  thaw FR2.
  Time forward. (*3.3 versus 7*)
  Time entailer!. (*1.3 versus 6.2*)
Time Qed. (*41.6 versus 52 -- noticably SLOWER than previous 2 lemmas*) (*NOW: 51 secs*)

Lemma pattern4_noStmt Espec Source1 Source2 Target Offset: forall FR
  (S1Range: 0 <= Source1 < 4) (S2Range: 0 <= Source2 < 4) (TgtRange: 0 <= Target < 4)
  (HOffset: 0 < Int.unsigned (Int.repr Offset) < 32)
  ValS1 ValS2 ValTgt (tlist:list val)
  (HS1: Znth Source1 tlist Vundef = Vint ValS1)
  (HS2: Znth Source2 tlist Vundef = Vint ValS2)
  (HTgt: Znth Target tlist Vundef = Vint ValTgt)
   c i j t y x w out nonce k h,
@semax CompSpecs Espec (initialized_list [_i; _j; _m; _aux; _aux1; 184%positive; 183%positive; 182%positive]
     (func_tycontext f_core SalsaVarSpecs SalsaFunSpecs))
  (PROP  ()
   LOCAL  (temp _i (Vint (Int.repr i)); temp _m (Vint (Int.repr 4));
   temp _j (Vint (Int.repr j)); lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (FR; data_at Tsh (tarray tuint 4) tlist t))
  (Ssequence
     (Sset _aux
        (Ederef
           (Ebinop Oadd (Evar _t (tarray tuint 4))
              (Econst_int (Int.repr Source1) tint) (tptr tuint)) tuint))
     (Ssequence
        (Sset _aux1
           (Ederef
              (Ebinop Oadd (Evar _t (tarray tuint 4))
                 (Econst_int (Int.repr Source2) tint) (tptr tuint)) tuint))
        (Ssequence
           (Sset _aux
              (Ebinop Oadd (Etempvar _aux tuint) (Etempvar _aux1 tuint) tuint))
           (Ssequence
              (Ssequence
                 (Scall (Some 185%positive)
                    (Evar _L32
                       (Tfunction (Tcons tuint (Tcons tint Tnil)) tuint
                          cc_default))
                    [Etempvar _aux tuint; Econst_int (Int.repr Offset) tint])
                 (Sset _aux (Etempvar 185%positive tuint)))
              (Ssequence
                 (Sset _aux1
                    (Ederef
                       (Ebinop Oadd (Evar _t (tarray tuint 4))
                          (Econst_int (Int.repr Target) tint) (tptr tuint)) tuint))
                 (Ssequence
                    (Sset _aux1
                       (Ebinop Oxor (Etempvar _aux1 tuint)
                          (Etempvar _aux tuint) tuint))
                    (Sassign
                       (Ederef
                          (Ebinop Oadd (Evar _t (tarray tuint 4))
                             (Econst_int (Int.repr Target) tint) (tptr tuint))
                          tuint) (Etempvar _aux1 tuint))))))))
  (normal_ret_assert 
  (PROP  ()
   LOCAL  (temp _i (Vint (Int.repr i)); temp _m (Vint (Int.repr 4));
   temp _j (Vint (Int.repr j)); lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (FR; data_at Tsh (tarray tuint 4) 
        (upd_Znth Target tlist
           (Vint
              (Int.xor ValTgt (Int.rol (Int.add ValS1 ValS2) (Int.repr Offset)))))
        t))).
Proof. intros. abbreviate_semax.
  Time forward; rewrite HS1. (*3.4 versus 13.4*)  
  Time solve[entailer!]. (*0.8 versus 4.5*)
  Time forward; rewrite HS2. (*5.1 versus 12*) 
  Time solve[entailer!]. (*0.8 versus 4.5*)
  freeze [0;1] FR1.
  Time forward. (*0.9 versus 4.9*)

  Time forward_call (Int.add ValS1 ValS2, Int.repr Offset). (*2.6 versus 9*)

  thaw FR1.
  Time forward; rewrite HTgt. (*3.4 versus 12.8*) 
  Time solve[entailer!]. (*1 versus 4.7*)
  freeze [0;1] FR2.
  Time forward. (*0.7 versus 5*)
  thaw FR2.
  Time forward. (*3.3 versus 7*)
  Time entailer!. (*1.3 versus 6.2*)
Time Qed. (*91!*) (*NOW 103*)

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
  
Lemma array_copy2 Espec FR i (wlist:list val) j t y x w nonce out c k h
       (t0 t1 t2 t3:int) (J:0<=j<4):
@semax CompSpecs Espec
  (initialized_list [_i; _j; _m; _aux; _aux1; 185%positive; 184%positive; 183%positive; 182%positive]
     (func_tycontext f_core SalsaVarSpecs SalsaFunSpecs))
  (PROP  ()
   LOCAL  (temp _i (Vint (Int.repr i)); temp _m (Vint (Int.repr 4));
   temp _j (Vint (Int.repr j)); lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (FR; data_at Tsh (tarray tuint 16) wlist w; 
         data_at Tsh (tarray tuint 4) (map Vint [t0;t1;t2;t3]) t))
  (Sfor (Sset _m (Econst_int (Int.repr 0) tint))
     (Ebinop Olt (Etempvar _m tint) (Econst_int (Int.repr 4) tint) tint)
     (Ssequence
        (Sset _aux
           (Ederef
              (Ebinop Oadd (Evar _t (tarray tuint 4)) (Etempvar _m tint)
                 (tptr tuint)) tuint))
        (Ssequence
           (Sset _aux1
              (Ebinop Oadd
                 (Ebinop Omul (Econst_int (Int.repr 4) tint)
                    (Etempvar _j tint) tint)
                 (Ebinop Omod
                    (Ebinop Oadd (Etempvar _j tint) (Etempvar _m tint) tint)
                    (Econst_int (Int.repr 4) tint) tint) tint))
           (Sassign
              (Ederef
                 (Ebinop Oadd (Evar _w (tarray tuint 16))
                    (Etempvar _aux1 tuint) (tptr tuint)) tuint)
              (Etempvar _aux tuint))))
     (Sset _m
        (Ebinop Oadd (Etempvar _m tint) (Econst_int (Int.repr 1) tint) tint)))
  (normal_ret_assert
  (PROP  ()
   LOCAL  (temp _j (Vint (Int.repr j)); temp _i (Vint (Int.repr i)); 
           lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (FR; data_at Tsh (tarray tuint 4) (map Vint [t0;t1;t2;t3]) t;
         EX W:_, !!(wlistJ' wlist j t0 t1 t2 t3 W) && data_at Tsh (tarray tuint 16) W w))).
Proof. intros. abbreviate_semax.
(*first, delete old m*) drop_LOCAL 1%nat.
Time assert_PROP (Zlength wlist=16) as WL by entailer!. (*1.6 versus 4.4*)
Time forward_for_simple_bound 4 (EX m:Z, 
  (PROP  ()
   LOCAL  (temp _i (Vint (Int.repr i)); 
   temp _j (Vint (Int.repr j)); lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (FR; data_at Tsh (tarray tuint 4) (map Vint [t0;t1;t2;t3]) t;
         EX l:_, !!WLIST' wlist [t0;t1;t2;t3] j (Z.to_nat m) l && data_at Tsh (tarray tuint 16) l w))).
   (*1.2 versus 6.3*)
{ Exists wlist. Time entailer!. (*2.4 versus 6.3*) }
{ rename H into M; rename i0 into m. 
  Intros wlist1. rename H into WLIST1.
  assert (TM: exists tm, Znth m [Vint t0; Vint t1; Vint t2; Vint t3] Vundef = Vint tm).
    destruct (zeq m 0); subst; simpl. eexists; reflexivity. 
    destruct (zeq m 1); subst; simpl. eexists; reflexivity. 
    destruct (zeq m 2); subst; simpl. eexists; reflexivity. 
    destruct (zeq m 3); subst; simpl. eexists; reflexivity. omega.
  destruct TM as [tm TM].
  freeze [0;2] FR1.
  Time forward. (*3.6 versus 11.6*)
  { Time entailer!. (*1 versus 5*) rewrite TM; simpl; trivial. }
  assert (NEQ: (Int.eq (Int.repr (j + m)) (Int.repr Int.min_signed) &&
                 Int.eq (Int.repr 4) Int.mone)%bool = false).
  { rewrite (Int.eq_false (Int.repr 4)), andb_false_r. simpl; trivial.
    unfold Int.mone. intros N.  
    assert (SGN: Int.signed (Int.repr 4) = Int.signed (Int.repr (-1))).
      rewrite N; trivial.
    rewrite Int.signed_repr, Int.signed_repr in SGN. omega.
    rewrite client_lemmas.int_min_signed_eq, client_lemmas.int_max_signed_eq; omega.
    rewrite client_lemmas.int_min_signed_eq, client_lemmas.int_max_signed_eq; omega. }
  Time forward. (*2.2 versus 6*)
  { Time entailer!. (*1.6 versus 5.5*) rewrite NEQ; simpl; trivial. }
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
  thaw FR1. freeze [0;2] FR2.
  Time forward. (*4.8 versus 12.5*)
  { apply prop_right.
    assert (0<= (j + m) mod 4 < 4). apply Z_mod_lt; omega. omega. }
  Exists (upd_Znth (4 * j + (j + m) mod 4) wlist1 (Vint tm)). (*_id0)). *)
  rewrite TM.
  Time entailer!. (*3.2 versus 8.7*)
  (*
  clear H1 H2 H3 H4 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20.
  assert (L1: length wlist1 = 16%nat) by (erewrite (WLIST'_length _ _ _ _ _ WLIST1); trivial).*)
  assert (AP: 0 <= (j + m) mod 4 < 4) by (apply Z_mod_lt; omega).
  rewrite Z.add_comm. rewrite Z2Nat.inj_add; try omega.
    assert (SS: (Z.to_nat 1 + Z.to_nat m)%nat = S (Z.to_nat m)) by reflexivity.
    rewrite SS; simpl.
    exists wlist1, tm.
    assert (WL1: Zlength wlist1 = 16). erewrite WLIST'_length. 2: eassumption. assumption.
    split. rewrite upd_Znth_Zlength. eapply WLIST'_length; eassumption.
           rewrite WL1. omega.
           split. trivial.  
           rewrite Z2Nat.id. split; trivial. omega. 
    Time thaw FR2; cancel. (*0.1 *) }
Time entailer!. (*3.7 versus 5.8*)
Intros l. Exists l. Time entailer!. (*0.5 versus 0.7*)
split. (*rewrite Zlength_map in H20.*) assumption.
destruct H1 as [l1 [tm1 [ZL1 [XX1 [Z3 HL1]]]]].
destruct XX1 as [l2 [tm2 [ZL2 [XX2 [Z2 HL2]]]]].
destruct XX2 as [l3 [tm3 [ZL3 [XX3 [Z1 HL3]]]]].
destruct XX3 as [l4 [tm4 [ZL4 [XX4 [Z0 HL4]]]]].
assert (T0: Znth 0 [Vint t0; Vint t1; Vint t2; Vint t3] Vundef = Vint t0) by reflexivity.
assert (T1: Znth 1 [Vint t0; Vint t1; Vint t2; Vint t3] Vundef = Vint t1) by reflexivity.
assert (T2: Znth 2 [Vint t0; Vint t1; Vint t2; Vint t3] Vundef = Vint t2) by reflexivity.
assert (T3: Znth 3 [Vint t0; Vint t1; Vint t2; Vint t3] Vundef = Vint t3) by reflexivity.
simpl in *.
rewrite Zplus_0_r.
rewrite T0 in Z0; inv Z0.
rewrite T1 in Z1; inv Z1.
rewrite T2 in Z2; inv Z2.
rewrite T3 in Z3; inv Z3; trivial.
Time Qed. (*285 versus 159 SLOW; was 130 in previous round- and I didn't change this lemma at all*)
  (*NOW: 290 secs*)

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

Lemma array_copy1 Espec: forall FR 
      i j t y x w nonce out c k h (xs:list int) (J:0<=j<4),
@semax CompSpecs Espec
  (initialized_list [_i; _j]
     (func_tycontext f_core SalsaVarSpecs SalsaFunSpecs))
  (PROP  ()
   LOCAL  (temp _j (Vint (Int.repr j)); temp _i (Vint (Int.repr i));
   lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y;
   lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out;
   temp _c c; temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (FR; @data_at_ CompSpecs Tsh (tarray tuint 4) t; 
     @data_at CompSpecs Tsh (tarray tuint 16) (@map int val Vint xs) x))
   (Ssequence
                        (Sset _m (Econst_int (Int.repr 0) tint))
                        (Sloop
                          (Ssequence
                            (Sifthenelse (Ebinop Olt (Etempvar _m tint)
                                           (Econst_int (Int.repr 4) tint)
                                           tint)
                              Sskip
                              Sbreak)
                            (Ssequence
                              (Sset _index
                                (Ebinop Omod
                                  (Ebinop Oadd
                                    (Ebinop Omul
                                      (Econst_int (Int.repr 5) tint)
                                      (Etempvar _j tint) tint)
                                    (Ebinop Omul
                                      (Econst_int (Int.repr 4) tint)
                                      (Etempvar _m tint) tint) tint)
                                  (Econst_int (Int.repr 16) tint) tint))
                              (Ssequence
                                (Sset _aux
                                  (Ederef
                                    (Ebinop Oadd (Evar _x (tarray tuint 16))
                                      (Etempvar _index tint) (tptr tuint))
                                    tuint))
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd (Evar _t (tarray tuint 4))
                                      (Etempvar _m tint) (tptr tuint)) tuint)
                                  (Etempvar _aux tuint)))))
                          (Sset _m
                            (Ebinop Oadd (Etempvar _m tint)
                              (Econst_int (Int.repr 1) tint) tint))))
  (normal_ret_assert 
  (PROP  ()
   LOCAL  (temp _i (Vint (Int.repr i)); temp _m (Vint (Int.repr 4)); temp _j (Vint (Int.repr j));
   lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
   lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w; temp _in nonce;
   temp _out out; temp _c c; temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (FR; data_at Tsh (tarray tuint 16) (map Vint xs) x;
     EX  l : list val,
     !!(forall mm : Z,
         0 <= mm < 4 ->
         Znth mm l Vundef =
         Znth ((5 * j + 4 * mm) mod 16) (map Vint xs) Vundef)
        && data_at Tsh (tarray tuint 4) l t))).
Proof. intros. abbreviate_semax.
freeze [0;1] FR1.
Time assert_PROP (Zlength (map Vint xs) = 16) as XL by entailer!. (*1*)
thaw FR1.
Time forward_for_simple_bound 4
 (EX m:Z, 
  (PROP  ()
   LOCAL  (temp _i (Vint (Int.repr i)); temp _j (Vint (Int.repr j)); lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (FR;
     EX l:_, !!(forall mm, 0<=mm<m -> Znth mm l Vundef = 
                  Znth ((5*j+4*mm) mod 16) (map Vint xs) Vundef)
            && data_at Tsh (tarray tuint 4) l t; 
       data_at Tsh (tarray tuint 16) (map Vint xs) x))); try reflexivity; try auto with closed; try repable_signed.
  (*1.3*)
  { Exists (list_repeat 4 Vundef). Time entailer!. (*2.2*) }
  { rename i0 into m. rename H into M. Intros T.
    rename H into HT.
    Time assert_PROP (Zlength T = 4) as TL by entailer!. (*2.2 versus 5.7*)
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
    freeze [0;1;2] FR1.
    Time forward. (*2.5*)
    { Time entailer!. (*1.9 versus 6.6*) rewrite <- Heqb. simpl; trivial. }
    unfold sem_mod, sem_binarith, both_int; simpl. rewrite ?mul_repr, ?add_repr, <- Heqb. simpl.
    unfold Int.mods. repeat rewrite Int.signed_repr.
      2: rewrite int_max_signed_eq, int_min_signed_eq; omega.
      2: rewrite int_max_signed_eq, int_min_signed_eq; omega.
    rewrite Z.rem_mod_nonneg; try omega.
    thaw FR1. freeze [0;1] FR2.
    Time forward; rewrite NV. (*4.5 versus 15*)
    Time solve[entailer!]. (*1.1 versus 5.4*)
    thaw FR2. freeze [0;2] FR3.
    Time forward. (*3.9 versus 14.7*)
    { Exists (upd_Znth m T (Vint v)).
      Time entailer!. (*4.2 versus 8.9*)
      intros mm ?. 
      destruct (zeq mm m); subst.
      + rewrite upd_Znth_same; try omega. rewrite NV; trivial. 
      + rewrite upd_Znth_diff; try omega. apply HT; omega.
      + thaw FR3. Time cancel. (*0.1*) } 
  }
Time entailer!. (*2.4 versus 7.6*)
Time Qed. (*19*) 

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
  (Ssequence
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
              tint)))
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
                       (Scall (Some 182%positive)
                          (Evar _L32
                             (Tfunction (Tcons tuint (Tcons tint Tnil)) tuint
                                cc_default))
                          [Etempvar _aux tuint; Econst_int (Int.repr 7) tint])
                       (Sset _aux (Etempvar 182%positive tuint)))
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
                          (Scall (Some 183%positive)
                             (Evar _L32
                                (Tfunction (Tcons tuint (Tcons tint Tnil))
                                   tuint cc_default))
                             [Etempvar _aux tuint;
                             Econst_int (Int.repr 9) tint])
                          (Sset _aux (Etempvar 183%positive tuint)))
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
                             (Scall (Some 184%positive)
                                (Evar _L32
                                   (Tfunction (Tcons tuint (Tcons tint Tnil))
                                      tuint cc_default))
                                [Etempvar _aux tuint;
                                Econst_int (Int.repr 13) tint])
                             (Sset _aux (Etempvar 184%positive tuint)))
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
                                (Scall (Some 185%positive)
                                   (Evar _L32
                                      (Tfunction
                                         (Tcons tuint (Tcons tint Tnil))
                                         tuint cc_default))
                                   [Etempvar _aux tuint;
                                   Econst_int (Int.repr 18) tint])
                                (Sset _aux (Etempvar 185%positive tuint)))
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
                          (Econst_int (Int.repr 1) tint) tint)))))))) 
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
  freeze [0;2] FR1.
  forward_seq. apply (array_copy1 _ (FRZL FR1)); trivial.
  Intros tlist. rename H into HT.
  freeze [0;1] FR2. 
  Time assert_PROP (Zlength tlist = 4) as TL by entailer!. (*1.1*)

  rewrite <- HT in T0; try omega.
  rewrite <- HT in T1; try omega.
  rewrite <- HT in T2; try omega.
  rewrite <- HT in T3; try omega.
  forward_seq.
  apply (pattern1_noStmt _ 0 3 1 7); try omega; try eassumption.
          rewrite Int.unsigned_repr. omega. rewrite int_max_unsigned_eq; omega.
    remember (Int.xor t1 (Int.rol (Int.add t0 t3) (Int.repr 7))) as tt0.
    remember (upd_Znth 1 tlist (Vint tt0)) as tlist1.
    assert(ZNTH1_1: Znth 1 tlist1 Vundef = Vint tt0).
      subst tlist1; apply upd_Znth_same. omega.
    assert(ZNTH1_0: Znth 0 tlist1 Vundef = Vint t0).
      subst tlist1; rewrite upd_Znth_diff; trivial; omega.
    assert(ZNTH1_2: Znth 2 tlist1 Vundef = Vint t2).
      subst tlist1; rewrite upd_Znth_diff; trivial; omega.
    assert(ZNTH1_3: Znth 3 tlist1 Vundef = Vint t3).
      subst tlist1; rewrite upd_Znth_diff; trivial; omega.
  assert (LT1: Zlength tlist1 = 4).
    subst tlist1. rewrite upd_Znth_Zlength. apply TL. omega.

  (*VST Issue: mkConciseDelta SalsaVarSpecs SalsaFunSpecs f_core Delta. doesn't work any longer*)
  forward_seq. 
    eapply (pattern2_noStmt _ 1 0 2 9); try omega; try eassumption.
          rewrite Int.unsigned_repr. omega. rewrite int_max_unsigned_eq; omega.
    remember (Int.xor t2 (Int.rol (Int.add tt0 t0) (Int.repr 9))) as tt1.
  remember (upd_Znth 2 tlist1 (Vint tt1)) as tlist2.
    assert(ZNTH2_1: Znth 1 tlist2 Vundef = Vint tt0).
      subst tlist2. rewrite upd_Znth_diff; trivial; omega.
    assert(ZNTH2_0: Znth 0 tlist2 Vundef = Vint t0).
      subst tlist2; rewrite upd_Znth_diff; trivial; omega.
    assert(ZNTH2_2: Znth 2 tlist2 Vundef = Vint tt1). 
      subst tlist2; rewrite upd_Znth_same; trivial; omega.
    assert(ZNTH2_3: Znth 3 tlist2 Vundef = Vint t3).
      subst tlist2; rewrite upd_Znth_diff; trivial; omega.
  assert (LT2: Zlength tlist2 = 4).
    subst tlist2. rewrite upd_Znth_Zlength; trivial. omega.

  forward_seq. 
  eapply (pattern3_noStmt _ 2 1 3 13); try omega; try eassumption.
          rewrite Int.unsigned_repr. omega. rewrite int_max_unsigned_eq; omega.
  remember (Int.xor t3 (Int.rol (Int.add tt1 tt0) (Int.repr 13))) as tt2.  
  remember (upd_Znth 3 tlist2 (Vint tt2)) as tlist3.
  assert (LT3:  Zlength tlist3 = 4).
    subst tlist3. rewrite upd_Znth_Zlength; trivial. omega.

  assert(ZNTH3_1: Znth 1 tlist3 Vundef = Vint tt0).
      subst tlist3; rewrite upd_Znth_diff; trivial; omega.
    assert(ZNTH3_0: Znth 0 tlist3 Vundef = Vint t0).
      subst tlist3; rewrite upd_Znth_diff; trivial; omega.
    assert(ZNTH3_2: Znth 2 tlist3 Vundef = Vint tt1).
      subst tlist3; rewrite upd_Znth_diff; trivial; omega.
    assert(ZNTH3_3: Znth 3 tlist3 Vundef = Vint tt2).
      subst tlist3; rewrite upd_Znth_same; trivial; omega.

  forward_seq. 
    eapply (pattern4_noStmt _ 3 2 0 18); try omega; try eassumption.
          rewrite Int.unsigned_repr. omega. rewrite int_max_unsigned_eq; omega.
  remember (Int.xor t0 (Int.rol (Int.add tt2 tt1) (Int.repr 18))) as tt3.
  remember (upd_Znth 0 tlist3 (Vint tt3)) as tlist4.
  assert (LT4:  Zlength tlist4 = 4).
    subst tlist4. rewrite upd_Znth_Zlength; trivial. omega.

   assert (TLI: tlist = map Vint [t0; t1;t2;t3]).
      clear - T0 T1 T2 T3 TL.
      destruct tlist; simpl in *. rewrite Zlength_nil in TL. omega.
      assert (Znth 0 (v :: tlist) Vundef = v) by reflexivity. rewrite H in T0; clear H. subst v.
      destruct tlist; simpl in *. rewrite Zlength_cons', Zlength_nil in TL. omega.
      assert (Znth 1 (Vint t0 :: v :: tlist) Vundef = v) by reflexivity. rewrite H in T1; clear H. subst v.
      destruct tlist; simpl in *. repeat rewrite Zlength_cons' in TL; rewrite Zlength_nil in TL. omega. 
      assert (Znth 2 (Vint t0 :: Vint t1 :: v :: tlist) Vundef = v) by reflexivity. rewrite H in T2; clear H. subst v.
      destruct tlist; simpl in *. repeat rewrite Zlength_cons' in TL; rewrite Zlength_nil in TL. omega.
      assert (Znth 3 (Vint t0 :: Vint t1 :: Vint t2 ::v :: tlist) Vundef = v) by reflexivity. rewrite H in T3; clear H. subst v.
      destruct tlist; trivial. repeat rewrite Zlength_cons' in TL. specialize (Zlength_nonneg tlist); intros; omega.
   assert (tlist4 = map Vint [tt3; tt0; tt1; tt2]).
     subst tlist tlist4 tlist3 tlist2 tlist1. unfold upd_Znth. simpl. f_equal.
   clear Heqtlist4 Heqtlist3 Heqtlist2 Heqtlist1.
   subst tlist4.
   thaw FR2. thaw FR1.
   freeze [0;2] FR3.
   eapply semax_post. 2: apply (array_copy2 Espec (FRZL FR3)); trivial.
   intros ek vl. apply andp_left2.
   apply assert_lemmas.normal_ret_assert_derives'. Intros l.
   thaw FR3. Exists l. old_go_lower. Time entailer!. (*8*)   (*TODO: eliminate old_go_lower*)
Time Qed. (*13.7*)
