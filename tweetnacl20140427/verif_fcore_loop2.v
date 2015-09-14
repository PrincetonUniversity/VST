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
Require Import spec_salsa.

Require Import verif_fcore_loop1.

Opaque Snuffle.Snuffle. Opaque core_spec. Opaque fcore_result.
Opaque crypto_core_salsa20_spec. Opaque crypto_core_hsalsa20_spec.

Definition Y_content (y: list val)
                     (i:Z) (l X:list val) : Prop :=
    exists n l1 l2 yy xx, i = Z.of_nat n /\ l = l1 ++ l2 /\
          l1++yy=y /\ xx++l2=X /\
          length l1=n /\ length xx = n.

Lemma f_core_loop2: forall (Espec : OracleKind)
c k h nonce out OUT 
(data : SixteenByte * SixteenByte * (SixteenByte * SixteenByte))
(OUTlen : length OUT = 64%nat)
(Delta := initialized_list [_i] (func_tycontext f_core SalsaVarSpecs SalsaFunSpecs))
(out' : name _out)
(in' : name _in)
(k' : name _k)
(c' : name _c)
(h' : name _h)
(aux' : name _aux)
w x y t
(xInit : list val)
(XInit : xInit = upd_upto data (Z.to_nat 4) (list_repeat 16 Vundef)),
@semax Espec Delta
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
Proof. intros.
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
    apply (exp_right (list_repeat 16 Vundef)). cancel.
    apply andp_right.
      apply prop_right. exists O. exists nil,  (list_repeat 16 Vundef).
      exists xInit, nil; simpl. repeat split; auto.
    cancel. }
  { forward.
    { entailer. 
      apply prop_right. unfold Znth. if_tac. omega. clear H10. 
      destruct H9 as [n [l1 [l2 [yy [xx [? [? [? [? [? ?]]]]]]]]]].
      subst i; rewrite Nat2Z.id.
      rewrite <- H12, app_nth2, H14, minus_diag. simpl.
      assert (V: exists v yT, yy = (Vint v)::yT).
        destruct yy. rewrite app_nil_r in H12. subst l1. 
         rewrite upd_upto_length in H14. omega. rewrite length_list_repeat. trivial. simpl; omega.

       assert (HH: (0 <= n < 16)%nat) by omega. 
       specialize (upd_upto_Vint data n HH Vundef). 
       assert (ZF: Z.to_nat 4 = 4%nat) by reflexivity. rewrite ZF in H12; rewrite <- H12; clear H12.
       intros Q. destruct Q. rewrite app_nth2, H14, minus_diag in H9. simpl in H9. subst v.
       eexists; eexists; reflexivity.
       rewrite H14. omega.

      destruct V as [v [yT ?]]. subst yy; simpl. trivial. omega.
    }
    normalize. intros L. normalize. rename H0 into Ycont.
    forward.
    { entailer.
      apply (exp_right (upd_reptype_array tuint i L
       (force_val
        (sem_cast_neutral
           (Znth i (upd_upto data (Z.to_nat 4) (list_repeat 16 Vundef))
              Vundef))))). 
      entailer.
      apply andp_right; try cancel.
      apply prop_right. destruct Ycont as [n [l1 [l2 [yy [xx [? [? [? [? [? ?]]]]]]]]]].
      assert (YY: exists yT, yy = (Vint aux')::yT).
        destruct yy. rewrite app_nil_r in H13. subst l1. 
          rewrite upd_upto_length in H15. omega. rewrite length_list_repeat; trivial.
          simpl; omega. 
        exists yy. f_equal.
        unfold Znth in H1. if_tac in H1. omega. rewrite <- H13 in H1.
        rewrite app_nth2 in H1. 
           assert ((Z.to_nat i - length l1 = 0)%nat).
             rewrite H11, H15, Nat2Z.id. apply minus_diag.
           rewrite H18 in H1; simpl in H1. trivial.
        rewrite H11, H15, Nat2Z.id. omega.
      destruct YY as [yT Y]; subst yy. rewrite H1 in *; clear H1. rewrite <- H13.
      assert (TT: exists lT, l2 = Vundef::lT).
        destruct l2. rewrite app_nil_r in *.
        subst xx. rewrite length_list_repeat in H16. rewrite <- H16 in *. 
        assert (LL: length (l1 ++ Vint aux' :: yT) = length (upd_upto data (Z.to_nat 4) (list_repeat 16 Vundef))).
            rewrite H13; trivial.
        rewrite upd_upto_length, app_length, H15 in LL. simpl in LL. omega. rewrite length_list_repeat; trivial. simpl; omega.
        rewrite (in_list_repeat 16 Vundef v). eexists; reflexivity. rewrite <- H14. apply in_app. right; left; trivial.
      destruct TT as [lT L2]; subst l2.
      exists (S n). rewrite Nat2Z.inj_succ.
      exists (l1 ++ [Vint aux']), lT, yT, (xx ++ [Vundef]).
      repeat rewrite app_length. rewrite H15, H16, Z.add_comm. 
      split. omega.
(*      repeat rewrite <- app_assoc. simpl. rewrite H13, H14.*)
      assert (XX: xx = list_repeat n Vundef /\ Vundef :: lT=list_repeat (16-n) Vundef).
        specialize (list_repeat_app _ n (16-n) Vundef).
        rewrite <- le_plus_minus. intros. rewrite <- H1 in H14. clear H1. 
        eapply hmac_pure_lemmas.app_inv_length1. assumption. rewrite length_list_repeat; trivial.
        apply Nat2Z.inj_le. rewrite <- H16; simpl. omega.
      destruct XX as [? VV]; subst xx. 
      subst L i.
      rewrite upd_reptype_array_char; trivial. simpl. 
      do 3 rewrite <- app_assoc. simpl.
      split. reflexivity.
      split. reflexivity.
      rewrite H14. split. reflexivity.  omega.
    }
  }
  apply derives_refl.
Qed. 