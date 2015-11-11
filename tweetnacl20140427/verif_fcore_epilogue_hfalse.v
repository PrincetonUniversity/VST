Require Import floyd.proofauto.
Local Open Scope logic.
Require Import List. Import ListNotations.
Require Import general_lemmas.
Require Import sublist.

Require Import split_array_lemmas.
Require Import ZArith. 
Require Import tweetNaclBase.
Require Import Salsa20.
Require Import verif_salsa_base.
Require Import tweetnaclVerifiableC.

Require Import spec_salsa.
Opaque Snuffle.Snuffle. Opaque prepare_data.
Opaque core_spec. Opaque ld32_spec. Opaque L32_spec. Opaque st32_spec.
Opaque crypto_core_salsa20_spec. Opaque crypto_core_hsalsa20_spec.

Definition HFalse_inv l i xs ys :=
        Zlength l = 64 /\
                forall ii, 0<=ii<i -> 
                  exists x_i, Znth ii (map Vint xs) Vundef = Vint x_i /\
                  exists y_i, Znth ii (map Vint ys) Vundef = Vint y_i /\
                  sublist (4*ii) (4*ii+4) l =
                  QuadByte2ValList (littleendian_invert (Int.add x_i y_i)).

Definition HFalsePostCond t y x w nonce out c k h xs ys data := 
PROP  ()
 LOCAL  ((*temp _i (Vint (Int.repr 16));*) lvar _t (tarray tuint 4) t;
 lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
 lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
 temp _k k; temp _h (Vint (Int.repr h)))
 SEP  (`(data_at Tsh (tarray tuint 16) (map Vint xs) x);
 `(data_at Tsh (tarray tuint 16) (map Vint ys) y);
 `(data_at_ Tsh (tarray tuint 4) t); `(data_at_ Tsh (tarray tuint 16) w);
 `(CoreInSEP data (nonce, c, k));
 `(EX  l : list val,
   !!HFalse_inv l 16 xs ys && data_at Tsh (tarray tuchar 64) l out)).

Lemma verif_fcore_epilogue_hfalse Espec t y x w nonce out c k h data OUT xs ys:
@semax CompSpecs Espec
  (initialized_list [_i] (func_tycontext f_core SalsaVarSpecs SalsaFunSpecs))
  (PROP  ()
   LOCAL  (lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
   lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w; temp _in nonce;
   temp _out out; temp _c c; temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(data_at Tsh (tarray tuint 16) (map Vint xs) x);
   `(data_at Tsh (tarray tuint 16) (map Vint ys) y);
   `(data_at_ Tsh (tarray tuint 4) t); `(data_at_ Tsh (tarray tuint 16) w);
   `(CoreInSEP data (nonce, c, k)); `(data_at Tsh (tarray tuchar 64) OUT out)))
        (Ssequence
          (Sset _i (Econst_int (Int.repr 0) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                             (Econst_int (Int.repr 16) tint) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Sset _aux
                  (Ederef
                    (Ebinop Oadd (Evar _x (tarray tuint 16))
                      (Etempvar _i tint) (tptr tuint)) tuint))
                (Ssequence
                  (Sset _aux1
                    (Ederef
                      (Ebinop Oadd (Evar _y (tarray tuint 16))
                        (Etempvar _i tint) (tptr tuint)) tuint))
                  (Ssequence
                    (Sset _aux
                      (Ebinop Oadd (Etempvar _aux tuint)
                        (Etempvar _aux1 tuint) tuint))
                    (Ssequence
                      (Sset _u8_aux
                        (Ebinop Oadd (Etempvar _out (tptr tuchar))
                          (Ebinop Omul (Econst_int (Int.repr 4) tint)
                            (Etempvar _i tint) tint) (tptr tuchar)))
                      (Scall None
                        (Evar _st32 (Tfunction
                                      (Tcons (tptr tuchar)
                                        (Tcons tuint Tnil)) tvoid cc_default))
                        ((Etempvar _u8_aux (tptr tuchar)) ::
                         (Etempvar _aux tuint) :: nil)))))))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                tint))))
(normal_ret_assert (HFalsePostCond t y x w nonce out c k h xs ys data)).
Proof. intros. abbreviate_semax.
eapply semax_post'.
Focus 2.
    Opaque littleendian.
    Opaque littleendian_invert. Opaque Snuffle20. Opaque prepare_data. 
    Opaque QuadByte2ValList.
Time forward_for_simple_bound 16 (EX i:Z, 
  (PROP  ()
   LOCAL  (lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP 
   (`(@data_at CompSpecs Tsh (tarray tuint 16) (map Vint xs) x);
   `(@data_at CompSpecs Tsh (tarray tuint 16) (map Vint ys) y);
   `(@data_at_ CompSpecs Tsh (tarray tuint 4) t); `(@data_at_ CompSpecs Tsh (tarray tuint 16) w);
   `(CoreInSEP data (nonce, c, k));
   `(EX l:_, !!HFalse_inv l i xs ys && @data_at CompSpecs Tsh (tarray tuchar 64) l out)))).
  (*2.9*)
  { Exists OUT. Time entailer!. (*5.6*)
    split; trivial; intros. omega. } 
  { rename H into I. Intros l. rename H into INV_l.
    Time assert_PROP (Zlength (map Vint xs) = 16) as XL by entailer!. (*3*)
    rewrite Zlength_map in XL.
    destruct (Znth_mapVint (xs:list int) i Vundef) as [xi Xi]; try omega.
    Time assert_PROP (Zlength (map Vint ys) = 16) as YL by entailer!.
    rewrite Zlength_map in YL.
    destruct (Znth_mapVint ys i Vundef) as [yi Yi]; try omega.
    Time forward; rewrite Xi. (*9.1*)
    Time solve[entailer!]. (*2.9*) 
    Time forward; rewrite Yi. (*9.6*)
    Time solve[entailer!]. (*3.1*) 
    Time forward. (*3.7*)
    Opaque Z.mul. Opaque Z.add. Opaque Z.sub.
    Time assert_PROP (isptr out) as Pout by entailer!. (*3.2*)
    Time forward. (*3.9*)
    assert (ZL: Zlength l = 64). apply INV_l.
    Time assert_PROP(field_compatible (Tarray tuchar 64 noattr) [] out) as FCO by entailer!. (*3*)
    rewrite <- ZL, (split3_data_at_Tarray_at_tuchar Tsh (Zlength l) (4 *i) 4); try rewrite ZL; try omega; trivial.
    Time normalize. (*5.5*)
Transparent core_spec. Transparent ld32_spec. Transparent L32_spec. Transparent st32_spec.
Transparent crypto_core_salsa20_spec. Transparent crypto_core_hsalsa20_spec.
    Time forward_call (offset_val (Int.repr (4 * i)) out, Int.add xi yi). (*6.8*)
Opaque core_spec. Opaque ld32_spec. Opaque L32_spec. Opaque st32_spec.
Opaque crypto_core_salsa20_spec. Opaque crypto_core_hsalsa20_spec.
    { Exists (sublist (4 * i) (4 + 4 * i) l).
      unfold at_offset at 1. 
      Time entailer!. (*6.9*) }

    Exists ((sublist 0 (4 * i) l) ++ 
                      (QuadByte2ValList (littleendian_invert (Int.add xi yi))) ++
                      (sublist (4 + 4 * i) 64 l)).
    Time entailer!. (*8.7*)
    {  split; intros. do 2 rewrite Zlength_app; repeat rewrite Zlength_sublist.
        rewrite <- QuadByteValList_ZLength, Zminus_0_r. rewrite (Z.add_comm _ (4*i)). rewrite Z.sub_add_distr. 
        do 2 rewrite Z.add_sub_assoc, Z.add_simpl_l. trivial. 
        omega. omega. omega. omega. 
      destruct INV_l as [_ INV_l].
      destruct (zlt ii i).
        + destruct (INV_l ii) as [x_ii [Z_ii [y_ii [Y_iiA Y_iiB]]]]. omega.
          rewrite Z_ii, Y_iiA. exists x_ii; split. trivial. 
          exists y_ii; split. trivial. rewrite <- Y_iiB. clear Y_iiB. clear INV_l.
          rewrite sublist_app1.
          - rewrite sublist_sublist. do 2 rewrite Zplus_0_r. reflexivity. omega. omega. rewrite Zminus_0_r; omega.
          - omega.
          - rewrite Zlength_sublist, Zminus_0_r; omega.
        + assert (IX: ii = i) by omega. subst ii. clear g INV_l.
          exists xi. split; trivial. exists _id1; split; trivial.
          rewrite sublist_app2; rewrite Zlength_sublist; try rewrite Zminus_0_r; try omega.
          rewrite Zminus_diag, Z.add_simpl_l.
          rewrite sublist0_app1; try rewrite <- QuadByteValList_ZLength; try omega.
          apply sublist_same. trivial. apply QuadByteValList_ZLength. }

    { unfold QByte. Transparent Z.sub. 
         rewrite (split3_data_at_Tarray_at_tuchar Tsh 64 (4 *i) 4); 
          repeat rewrite Zlength_app; repeat rewrite Zlength_sublist; repeat rewrite Zminus_0_r; repeat rewrite <- QuadByteValList_ZLength; trivial.
          rewrite sublist0_app1. rewrite sublist_sublist. repeat rewrite Zplus_0_r. cancel.
          unfold at_offset at 2.
          rewrite sublist_app2; try rewrite Zlength_sublist, Zminus_0_r, Zminus_diag, Z.add_simpl_r.
          rewrite sublist0_app1; try rewrite <- QuadByteValList_ZLength.
          apply sepcon_derives. rewrite sublist_same; try rewrite <- QuadByteValList_ZLength; trivial.
          rewrite sublist_app2; repeat rewrite Zlength_sublist, Zminus_0_r.
          rewrite sublist_app2; try rewrite <- QuadByteValList_ZLength; repeat rewrite Zlength_sublist.
          assert (A:(4 * i + (4 + (64 - (4 + 4 * i))) - (4 + 4 * i) = 64 - (4 + 4 * i))%Z). unfold Z.sub; omega.
          rewrite A; clear A.
          repeat rewrite Z.add_simpl_r. rewrite Zminus_diag.
          rewrite sublist_sublist.
          assert (A: (4 * i + (4 + (64 - (4 + 4 * i))) - 4 * i - 4 + (4 + 4 * i) = 64)%Z). unfold Z.sub; omega.
          rewrite A; clear A. trivial.
          omega. unfold Z.sub; omega. unfold Z.sub; omega. unfold Z.sub; omega. omega. omega. omega. omega. omega.
          omega. omega. omega. rewrite Zlength_sublist, Zminus_0_r; omega. omega. omega. rewrite Zminus_0_r; omega.
          rewrite Zlength_sublist, Zminus_0_r; omega. omega. omega. omega. omega. omega. omega. unfold Z.sub; omega.
          omega. omega. omega. omega. } 
    } 
  apply derives_refl.
unfold HFalsePostCond.  (*Exists l. *) Time entailer!. (*3.1*)
(*With temp _i (Vint (Int.repr 16) in LOCAL of HfalsePostCond: apply derives_refl. *)
Time Qed. (*60*)