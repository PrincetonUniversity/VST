Require Import VST.floyd.proofauto.
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
                  exists x_i, Znth ii (map Vint xs) = Vint x_i /\
                  exists y_i, Znth ii (map Vint ys) = Vint y_i /\
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

Definition epilogue_hfalse_statement:=
Sfor (Sset _i (Econst_int (Int.repr 0) tint))
     (Ebinop Olt (Etempvar _i tint) (Econst_int (Int.repr 16) tint) tint)
     (Ssequence
        (Sset _t'11
           (Ederef
              (Ebinop Oadd (Evar _x (tarray tuint 16)) (Etempvar _i tint)
                 (tptr tuint)) tuint))
        (Ssequence
           (Sset _t'12
              (Ederef
                 (Ebinop Oadd (Evar _y (tarray tuint 16)) (Etempvar _i tint)
                    (tptr tuint)) tuint))
           (Scall None
              (Evar _st32
                 (Tfunction (Tcons (tptr tuchar) (Tcons tuint Tnil)) tvoid
                    cc_default))
              [Ebinop Oadd (Etempvar _out (tptr tuchar))
                 (Ebinop Omul (Econst_int (Int.repr 4) tint)
                    (Etempvar _i tint) tint) (tptr tuchar);
              Ebinop Oadd (Etempvar _t'11 tuint) (Etempvar _t'12 tuint) tuint])))
     (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint)).

Lemma verif_fcore_epilogue_hfalse Espec FR t y x w nonce out c k h OUT xs ys:
@semax CompSpecs Espec
  (func_tycontext f_core SalsaVarSpecs SalsaFunSpecs nil)
  (PROP  ()
   LOCAL  (lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
   lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w; temp _in nonce;
   temp _out out; temp _c c; temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (FR; data_at Tsh (tarray tuchar 64) OUT out;
         data_at Tsh (tarray tuint 16) (map Vint ys) y;
         data_at Tsh (tarray tuint 16) (map Vint xs) x))
  epilogue_hfalse_statement
  (normal_ret_assert (HFalsePostCond FR t y x w nonce out c k h xs ys (*data*))).
Proof. intros. abbreviate_semax.
  unfold epilogue_hfalse_statement.
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
 * Exists OUT. Time entailer!. (*4.2*)
    split; trivial; intros. omega.
 * rename H into I. Intros l. rename H into INV_l.
    freeze [0;2;3] FR1.
    Time assert_PROP (Zlength (map Vint xs) = 16) as XL by entailer!. (*1*)
    rewrite Zlength_map in XL.
    destruct (Znth_mapVint (xs:list int) i) as [xi Xi]; try omega.
    Time forward. 
    thaw FR1. freeze [0;2;3] FR2. 
    Time assert_PROP (Zlength (map Vint ys) = 16) as YL by entailer!. (*1*)
    rewrite Zlength_map in YL.
    destruct (Znth_mapVint ys i) as [yi Yi]; try omega.
    Time forward.
    thaw FR2. freeze [0;2;3] FR3.
    Time assert_PROP (isptr out) as Pout by entailer!. (*1.9*)
    assert (ZL: Zlength l = 64). apply INV_l.
    Time assert_PROP(field_compatible (Tarray tuchar 64 noattr) [] out) as FCO by entailer!. (*1.1*)
    rewrite <- ZL, (split3_data_at_Tarray_tuchar Tsh (Zlength l) (4 *i) (4+4*i)); try rewrite ZL; try omega; trivial.
    rewrite field_address0_offset by auto with field_compatible.
    rewrite field_address0_offset by auto with field_compatible.
    unfold offset_val. simpl.
    apply isptrD in Pout. destruct Pout as [b [z Pout]]; rewrite Pout in *; simpl in *.
    repeat flatten_sepcon_in_SEP.

    freeze [0;1;3] FR4.
    rewrite Znth_map in Xi, Yi; try omega. 
    inv Xi; inv Yi.
    Time forward_call (Vptr b (Ptrofs.add z (Ptrofs.repr (1 * (4 * i)))), Int.add (Znth i xs) (Znth i ys)). (*3.6*)
    { replace (4 + 4 * i - 4 * i) with 4 by omega. cancel. }
    entailer.

    Exists ((sublist 0 (4 * i) l) ++ 
                      (QuadByte2ValList (littleendian_invert (Int.add (Znth i xs) (Znth i ys)))) ++
                      (sublist (4 + 4 * i) 64 l)).
    autorewrite with sublist; try omega.
    Time entailer!.
    { split; intros; autorewrite with sublist. 
      + rewrite <- QuadByteValList_ZLength. omega.
      + destruct INV_l as [_ INV_l].
      destruct (zlt ii i).
        * destruct (INV_l ii) as [x_ii [Z_ii [y_ii [Y_iiA Y_iiB]]]]. omega.
          autorewrite with sublist in Z_ii,Y_iiA.
          rewrite Z_ii, Y_iiA. exists x_ii; split. trivial.
          exists y_ii; split. trivial. rewrite <- Y_iiB. clear Y_iiB. clear INV_l.
          rewrite sublist_app1.
          - rewrite sublist_sublist. do 2 rewrite Zplus_0_r. reflexivity. omega. omega. rewrite Zminus_0_r; omega.
          - omega.
          - rewrite Zlength_sublist, Zminus_0_r; omega.
        * assert (IX: ii = i) by omega. subst ii. clear g INV_l.
(*          autorewrite with sublist in Xi,Yi.*)
          eexists; split; [reflexivity |].
          eexists; split; [reflexivity |].
          rewrite sublist_app2; rewrite Zlength_sublist; try rewrite Zminus_0_r; try omega.
          rewrite Zminus_diag, Z.add_simpl_l.
(*          autorewrite with sublist.*)
          unfold sublist. reflexivity. (* autorewrite with sublist. fails*) }

    { unfold QByte. thaw FR4. thaw FR3. Time cancel. (*0.9*)
      rewrite (split3_data_at_Tarray_tuchar Tsh 64 (4 *i) (4+4*i));
       autorewrite with sublist; try omega.
       2: rewrite <- QuadByteValList_ZLength; omega.
       rewrite field_address0_offset by auto with field_compatible.
       rewrite field_address0_offset by auto with field_compatible.
          repeat rewrite Z.mul_1_l. cancel.
          replace (offset_val (nested_field_offset (Tarray tuchar 64 noattr) [ArraySubsc (4 * i)]) (Vptr b z))
          with (Vptr b (Ptrofs.add z (Ptrofs.repr (4 * i)))). 2: simpl; do 3 f_equal; omega.
          replace (offset_val (nested_field_offset (Tarray tuchar 64 noattr) [ArraySubsc (4 + 4 * i)]) (Vptr b z))
          with (Vptr b (Ptrofs.add z (Ptrofs.repr (4 + 4 * i)))). 2: simpl; do 3 f_equal; omega.
          apply sepcon_derives; apply data_at_ext.
          + rewrite sublist_app1. rewrite sublist_same; trivial. omega. rewrite <- QuadByteValList_ZLength; omega.
          + rewrite 2 sublist_app2; try rewrite <- QuadByteValList_ZLength; rewrite ! Zlength_sublist; try omega. 
            rewrite sublist_sublist; try omega. f_equal; omega. }
  * unfold HFalsePostCond.
    Time entailer!. (*2.6*)
(*With temp _i (Vint (Int.repr 16) in LOCAL of HfalsePostCond: apply derives_refl. *)
Time Qed. (*June 4th, 2017 (laptop): inished transaction in 2.217 secs (1.88u,0.s) (successful)*)