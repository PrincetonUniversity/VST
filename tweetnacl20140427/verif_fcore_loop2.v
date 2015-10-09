Require Import Recdef.
Require Import floyd.proofauto.
Local Open Scope logic.
Require Import List. Import ListNotations.
Require Import general_lemmas.
Require Import sublist.
Require Import split_array_lemmas.
(*Require Import fragments.*)
Require Import ZArith. 
Require Import tweetNaclBase.
Require Import Salsa20.
Require Import verif_salsa_base.
Require Import tweetnaclVerifiableC.
Require Import spec_salsa.

Opaque Snuffle.Snuffle. Opaque core_spec. Opaque fcore_result.
Opaque crypto_core_salsa20_spec. Opaque crypto_core_hsalsa20_spec.

Definition Y_content (y: list val)
                     (i:Z) (l X:list val) : Prop :=
    exists l1 l2 yy xx, l = l1 ++ l2 /\
          l1++yy=y /\ xx++l2=X /\
          Zlength l1=i /\ Zlength xx =i.

Lemma f_core_loop2: forall (Espec : OracleKind)
c k h nonce out OUT 
(data : SixteenByte * SixteenByte * (SixteenByte * SixteenByte))
(*(Delta := initialized_list [_i] (func_tycontext f_core SalsaVarSpecs SalsaFunSpecs))*)
(out' : name _out)
(in' : name _in)
(k' : name _k)
(c' : name _c)
(h' : name _h)
(aux' : name _aux)
w x y t
(xInit : list val)
(XInit : xInit = upd_upto data 4 (list_repeat 16 Vundef)),
@semax CompSpecs Espec (initialized_list [_i] (func_tycontext f_core SalsaVarSpecs SalsaFunSpecs))
  (PROP  ()
   LOCAL  (temp _i (Vint (Int.repr 4)); lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(data_at Tsh (tarray tuint 16) xInit x);
   `(data_at_ Tsh (tarray tuint 16) y); `(data_at_ Tsh (tarray tuint 4) t);
   `(data_at_ Tsh (tarray tuint 16) w); `(CoreInSEP data (nonce, c, k));
   `(data_at Tsh (tarray tuchar 64) OUT out)))
  (Sfor (Sset _i (Econst_int (Int.repr 0) tint))
     (Ebinop Olt (Etempvar _i tint) (Econst_int (Int.repr 16) tint) tint)
     (Ssequence
        (Sset _aux
           (Ederef
              (Ebinop Oadd (Evar _x (tarray tuint 16)) (Etempvar _i tint)
                 (tptr tuint)) tuint))
        (Sassign
           (Ederef
              (Ebinop Oadd (Evar _y (tarray tuint 16)) (Etempvar _i tint)
                 (tptr tuint)) tuint) (Etempvar _aux tuint)))
     (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint)))
  (normal_ret_assert
(PROP  ()
   LOCAL  (temp _i (Vint (Int.repr 16)); lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(data_at Tsh (tarray tuint 16) xInit x);
   `(data_at_ Tsh (tarray tuint 4) t);
   `(EX  l : list val,
     !!Y_content xInit 16 l
         [Vundef; Vundef; Vundef; Vundef; Vundef; Vundef; Vundef; Vundef;
         Vundef; Vundef; Vundef; Vundef; Vundef; Vundef; Vundef; Vundef] &&
     data_at Tsh (tarray tuint 16) l y); `(data_at_ Tsh (tarray tuint 16) w);
   `(CoreInSEP data (nonce, c, k));
   `(data_at Tsh (tarray tuchar 64) OUT out)))).
Proof. intros. abbreviate_semax.
  forward_for_simple_bound 16 (EX i:Z, 
    PROP  ()
    LOCAL  ( 
      lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
      lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w; temp _in nonce;
      temp _out out; temp _c c; temp _k k; temp _h (Vint (Int.repr h)))
    SEP  (`(data_at Tsh (tarray tuint 16) xInit x);
     `(data_at_ Tsh (tarray tuint 4) t);
     `(EX l:_, !!(Y_content xInit i l (list_repeat 16 Vundef)) && data_at Tsh (tarray tuint 16) l y);
     `(data_at_ Tsh (tarray tuint 16) w); `(CoreInSEP data (nonce, c, k));
     `(data_at Tsh (tarray tuchar 64) OUT out) (*`(data_block Tsh OUT out)*))).
  { clear XInit. entailer. 
    apply (exp_right (list_repeat 16 Vundef)). entailer.
    apply andp_right.
      apply prop_right. exists nil,  (list_repeat 16 Vundef).
      exists xInit, nil; simpl. repeat split; auto.
    cancel. }
  { rename H into I. normalize. intros Y. normalize. rename H into YCONT.
    destruct (upd_upto_Vint data i I Vundef) as [vi Vi]. 
    
      destruct YCONT as [l1 [l2 [yy [xx [APP1 [APP2 [APP3 [L1 L2]]]]]]]].
      assert (V: exists v yT, yy = (Vint v)::yT).
        destruct yy. rewrite app_nil_r in APP2. subst l1 xInit. 
         rewrite upd_upto_Zlength in L1. omega. 
         rewrite Zlength_list_repeat. trivial. simpl; omega. subst xInit. 
        rewrite <- APP2, app_Znth2, L1, Zminus_diag, Znth_0_cons in Vi. rewrite Vi.
        eexists; eexists; reflexivity. omega.
      destruct V as [v [yT ?]]. subst yy; simpl.
      forward.
      { entailer. rewrite Vi. apply prop_right; simpl; trivial. }
      rewrite <- XInit, <- APP2 in Vi. rewrite <- APP2, Vi.
      rewrite app_Znth2, L1, Zminus_diag, Znth_0_cons in Vi. inversion Vi; clear Vi; subst vi. 2: omega. 
      forward.
      { Opaque upd_upto. entailer.
        apply (exp_right (upd_Znth_in_list (Zlength l1) (l1 ++ l2) (Vint aux'))).
        rewrite APP2. entailer. 
        apply andp_right. 2: cancel.
        apply prop_right. clear - APP2 APP3 I L2. 
        assert (TT: exists lT, l2 = Vundef::lT).
        { destruct l2.
            rewrite app_nil_r in *. subst xx; rewrite <- L2, Zlength_list_repeat in I. simpl in I; omega. 
            rewrite (in_list_repeat 16 Vundef v). eexists; reflexivity.
              rewrite <- APP3. apply in_app. right; left; trivial. }
        destruct TT as [lT LT2]; subst l2.
        exists (l1 ++ [Vint aux']), lT, yT, (xx ++ [Vundef]).
        repeat rewrite Zlength_app.
        repeat rewrite <- app_assoc. simpl. rewrite APP3, L2.
        split. 
          rewrite upd_Znth_in_list_char; trivial. omega.
          rewrite Zlength_cons', Zlength_nil, Zplus_0_r. solve [auto]. }
  }
  normalize.
Qed. 