(*Require Import Recdef.*)
Require Import VST.floyd.proofauto.
Local Open Scope logic.
Require Import List. Import ListNotations.
Require Import ZArith.
Require Import tweetnacl20140427.tweetNaclBase.
Require Import tweetnacl20140427.Salsa20.
Require Import tweetnacl20140427.verif_salsa_base.
Require Import tweetnacl20140427.tweetnaclVerifiableC.
Require Import tweetnacl20140427.spec_salsa.

Definition Y_content (y: list val)
                     (i:Z) (l X:list val) : Prop :=
    exists l1 l2 yy xx, l = l1 ++ l2 /\
          l1++yy=y /\ xx++l2=X /\
          Zlength l1=i /\ Zlength xx =i.

Lemma f_core_loop2: forall (Espec : OracleKind) FR c k h nonce out w x y t
  (data : SixteenByte * SixteenByte * (SixteenByte * SixteenByte))
  (Delta := func_tycontext f_core SalsaVarSpecs SalsaFunSpecs nil)
  (xInit : list val)
  (XInit : xInit = upd_upto data 4 (list_repeat 16 Vundef)),
@semax CompSpecs Espec
Delta
  (PROP  ()
   LOCAL  (temp _i (Vint (Int.repr 4)); lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (FR; data_at_ Tsh (tarray tuint 16) y;
         data_at Tsh (tarray tuint 16) xInit x))(Sfor (Sset _i (Econst_int (Int.repr 0) tint))
     (Ebinop Olt (Etempvar _i tint) (Econst_int (Int.repr 16) tint) tint)
     (Ssequence
        (Sset _t'34
           (Ederef
              (Ebinop Oadd (Evar _x (tarray tuint 16)) (Etempvar _i tint)
                 (tptr tuint)) tuint))
        (Sassign
           (Ederef
              (Ebinop Oadd (Evar _y (tarray tuint 16)) (Etempvar _i tint)
                 (tptr tuint)) tuint) (Etempvar _t'34 tuint)))
     (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint)))
  (normal_ret_assert
(PROP  ()
   LOCAL  (temp _i (Vint (Int.repr 16)); lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (FR; data_at Tsh (tarray tuint 16) xInit x;
   EX  l : list val,
     !!Y_content xInit 16 l
         [Vundef; Vundef; Vundef; Vundef; Vundef; Vundef; Vundef; Vundef;
         Vundef; Vundef; Vundef; Vundef; Vundef; Vundef; Vundef; Vundef] &&
     data_at Tsh (tarray tuint 16) l y))).
Proof. intros. abbreviate_semax.
  Time forward_for_simple_bound 16 (EX i:Z,
    PROP  ()
    LOCAL  (
      lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
      lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w; temp _in nonce;
      temp _out out; temp _c c; temp _k k; temp _h (Vint (Int.repr h)))
    SEP  (FR; data_at Tsh (tarray tuint 16) xInit x;
          EX l:_, !!(Y_content xInit i l (list_repeat 16 Vundef)) &&
              data_at Tsh (tarray tuint 16) l y)).
  (*1.2*)
  { clear. Time entailer!. (*1.9*)
    Exists (list_repeat 16 Vundef). Time entailer!. (*0.4*)
    exists nil,  (list_repeat 16 Vundef).
      exists xInit, nil; simpl. repeat split; auto. }
  { rename H into I. Intros Y. rename H into YCONT.
    destruct (upd_upto_Vint data i I) as [vi Vi].
      destruct YCONT as [l1 [l2 [yy [xx [APP1 [APP2 [APP3 [L1 L2]]]]]]]].
      assert (V: exists v yT, yy = (Vint v)::yT).
        destruct yy. rewrite app_nil_r in APP2. subst l1 xInit.
         rewrite upd_upto_Zlength in L1. omega.
         rewrite Zlength_list_repeat'. trivial. simpl; omega. subst xInit.
        rewrite <- APP2, app_Znth2, L1, Zminus_diag, Znth_0_cons in Vi. rewrite Vi.
        eexists; eexists; reflexivity. omega.
      destruct V as [v [yT ?]]. subst yy; simpl.
    freeze [0;2] FR1. rewrite <- XInit in Vi.
      Time forward. (*3.4*)
      { Time entailer!. (*1*) clear - Vi. change Inhabitant_val with Vundef in Vi; rewrite Vi; simpl; trivial. }
      change Inhabitant_val with Vundef in Vi; rewrite Vi.
      rewrite <- APP2, app_Znth2, L1, Zminus_diag, Znth_0_cons in Vi.
      inversion Vi; clear Vi; subst vi. 2: omega.
    thaw FR1. freeze [0;2] FR2.
      Time forward. (*3.3*)
      {
        Exists (upd_Znth (Zlength l1) (l1 ++ l2) (Vint v)).
        Time entailer!. (*4.8*)
        + clear - APP2 APP3 I L2.
          assert (TT: exists lT, l2 = Vundef::lT).
          { destruct l2.
            - rewrite app_nil_r in *. subst xx; rewrite <- L2, Zlength_list_repeat' in I.
              simpl in I; omega.
            - rewrite (in_list_repeat 16 Vundef v0). eexists; reflexivity.
              rewrite <- APP3. apply in_app. right; left; trivial. }
          destruct TT as [lT LT2]; subst l2.
          exists (l1 ++ [Vint v]), lT, yT, (xx ++ [Vundef]).
          repeat rewrite Zlength_app.
          repeat rewrite <- app_assoc. simpl. rewrite APP3, L2.
          split.
            rewrite upd_Znth_char; trivial.
            rewrite Zlength_cons', Zlength_nil, Zplus_0_r. solve [auto].
        + (*rewrite <- APP1.*) thaw FR2. Time cancel. (*0.1*)  }
  }
  apply andp_left2; apply derives_refl.
Time Qed. (*VST 2.0: 0.6s *) (*13s*)