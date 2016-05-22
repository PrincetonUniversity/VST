Require Import floyd.proofauto.
Local Open Scope logic.
Require Import List. Import ListNotations.
Require Import ZArith. 
Require Import tweetnacl20140427.tweetNaclBase.
Require Import tweetnacl20140427.Salsa20.
Require Import tweetnacl20140427.verif_salsa_base.
Require Import tweetnacl20140427.tweetnaclVerifiableC.

Require Import tweetnacl20140427.spec_salsa.
Opaque Snuffle.Snuffle. Opaque prepare_data.

Definition HFalse_inv l i xs ys :=
        Zlength l = 64 /\
                forall ii, 0<=ii<i -> 
                  exists x_i, Znth ii (map Vint xs) Vundef = Vint x_i /\
                  exists y_i, Znth ii (map Vint ys) Vundef = Vint y_i /\
                  sublist (4*ii) (4*ii+4) l =
                  QuadByte2ValList (littleendian_invert (Int.add x_i y_i)).

Definition HFalsePostCond FR t y x w nonce out c k h xs ys := 
PROP  ()
 LOCAL  (lvar _t (tarray tuint 4) t;
 lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
 lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
 temp _k k; temp _h (Vint (Int.repr h)))
 SEP  (FR; data_at Tsh (tarray tuint 16) (map Vint xs) x;
 data_at Tsh (tarray tuint 16) (map Vint ys) y;
 EX  l : list val,
   !!HFalse_inv l 16 xs ys && data_at Tsh (tarray tuchar 64) l out).

Lemma verif_fcore_epilogue_hfalse Espec FR t y x w nonce out c k h OUT xs ys:
@semax CompSpecs Espec
  (initialized_list [_i] (func_tycontext f_core SalsaVarSpecs SalsaFunSpecs))
  (PROP  ()
   LOCAL  (lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
   lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w; temp _in nonce;
   temp _out out; temp _c c; temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (FR; data_at Tsh (tarray tuchar 64) OUT out;
         data_at Tsh (tarray tuint 16) (map Vint ys) y;
         data_at Tsh (tarray tuint 16) (map Vint xs) x))
(Ssequence (Sset _i (Econst_int (Int.repr 0) tint))
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
(normal_ret_assert (HFalsePostCond FR t y x w nonce out c k h xs ys (*data*))).
Proof. intros. abbreviate_semax.
eapply semax_post'.
Focus 2.
  Time forward_for_simple_bound 16 (EX i:Z, 
  (PROP  ()
   LOCAL  (lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP 
   (FR; @data_at CompSpecs Tsh (tarray tuint 16) (map Vint xs) x;
   @data_at CompSpecs Tsh (tarray tuint 16) (map Vint ys) y;
   EX l:_, !!HFalse_inv l i xs ys && @data_at CompSpecs Tsh (tarray tuchar 64) l out))).
  (*1.9*)
  { Exists OUT. Time entailer!. (*4.2*)
    split; trivial; intros. omega. } 
  { rename H into I. Intros l. rename H into INV_l.
    freeze [0;2;3] FR1.
    Time assert_PROP (Zlength (map Vint xs) = 16) as XL by entailer!. (*1*)
    rewrite Zlength_map in XL.
    destruct (Znth_mapVint (xs:list int) i Vundef) as [xi Xi]; try omega.
    Time forward; rewrite Xi. (*3.3*)
    Time solve[entailer!]. (*1*)
    thaw FR1. freeze [0;2;3] FR2. 
    Time assert_PROP (Zlength (map Vint ys) = 16) as YL by entailer!. (*1*)
    rewrite Zlength_map in YL.
    destruct (Znth_mapVint ys i Vundef) as [yi Yi]; try omega.
    Time forward; rewrite Yi. (*3.7*)
    Time solve[entailer!]. (*1.4*)
    Time forward. (*1.3*)
    thaw FR2. freeze [0;2;3] FR3.
    Time assert_PROP (isptr out) as Pout by entailer!. (*1.9*)
    Time forward. (*1.5*)
    assert (ZL: Zlength l = 64). apply INV_l.
    Time assert_PROP(field_compatible (Tarray tuchar 64 noattr) [] out) as FCO by entailer!. (*1.1*)
    rewrite <- ZL, (split3_data_at_Tarray_tuchar Tsh (Zlength l) (4 *i) (4+4*i)); try rewrite ZL; try omega; trivial.
    rewrite field_address0_offset by auto with field_compatible.
    rewrite field_address0_offset by auto with field_compatible.
    unfold offset_val. simpl. 
    apply isptrD in Pout. destruct Pout as [b [z Pout]]; rewrite Pout in *; simpl in *.
    repeat flatten_sepcon_in_SEP.

    freeze [0;1;3] FR4.
    Time forward_call (Vptr b (Int.add z (Int.repr (4 * i))), Int.add xi yi). (*3.6*)
    { Exists (sublist (4 * i) (4 + 4 * i) l).
      autorewrite with sublist. (*Coq bug: entailer!. yields Anomaly: Coq_omega: Z.sub is not an evaluable constant. Please report.*)
      Time (normalize; cancel). (*2.4*) }

    Exists ((sublist 0 (4 * i) l) ++ 
                      (QuadByte2ValList (littleendian_invert (Int.add xi yi))) ++
                      (sublist (4 + 4 * i) 64 l)).
    autorewrite with sublist. rewrite Pout in *.
    Time entailer!.
    { split; intros; autorewrite with sublist. omega.
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
          exists xi. split; trivial. exists yi; split; trivial.
          rewrite sublist_app2; rewrite Zlength_sublist; try rewrite Zminus_0_r; try omega.
          rewrite Zminus_diag, Z.add_simpl_l.
(*          autorewrite with sublist.*)
          unfold sublist. reflexivity. (* autorewrite with sublist. fails*) }

    { unfold QByte. thaw FR4. thaw FR3. Time cancel. (*0.9*) 
      rewrite (split3_data_at_Tarray_tuchar Tsh 64 (4 *i) (4+4*i)); 
       autorewrite with sublist; try omega.
          rewrite field_address0_offset by auto with field_compatible.
          rewrite field_address0_offset by auto with field_compatible. simpl.
          repeat rewrite Z.mul_1_l.
          unfold sublist; simpl. cancel. 
          apply derives_refl'. f_equal. f_equal. rewrite Z.add_comm. f_equal. omega.
          rewrite Z2Nat.inj_sub. rewrite <- skipn_firstn, firstn_same. trivial.
          rewrite <- ZtoNat_Zlength, ZL. omega.
          omega. } 
    } 
  apply derives_refl.
unfold HFalsePostCond. Time entailer!. (*2.6*)
(*With temp _i (Vint (Int.repr 16) in LOCAL of HfalsePostCond: apply derives_refl. *)
Time Qed. (*27*)