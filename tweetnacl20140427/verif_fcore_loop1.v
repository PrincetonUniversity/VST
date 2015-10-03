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
Require Import tweetnaclVerifiableC.
Require Import verif_salsa_base.

Require Import spec_salsa. Opaque Snuffle.Snuffle. Opaque fcore_result.

Opaque core_spec. Opaque ld32_spec. Opaque L32_spec. Opaque st32_spec.
Opaque crypto_core_salsa20_spec. Opaque crypto_core_hsalsa20_spec.

Definition X_content (x: SixteenByte * SixteenByte * (SixteenByte * SixteenByte))
                     (i:Z) (l:list val) : Prop :=
    l = upd_upto x (Z.to_nat i) (list_repeat 16 Vundef).

Lemma XcontUpdate Nonce C Key1 Key2 i l
      (I: 0 <= i < 4)
      (L: X_content (Nonce, C, (Key1, Key2)) i l):
X_content (Nonce, C, (Key1, Key2)) (i + 1)
  (upd_Znth_in_list (11 + i)
     (upd_Znth_in_list (6 + i)
        (upd_Znth_in_list (1 + i)
           (upd_Znth_in_list (5 * i) l
              (Vint (littleendian (Select16Q C i))))
           (Vint (littleendian (Select16Q Key1 i))))
        (Vint (littleendian (Select16Q Nonce i))))
     (Vint (littleendian (Select16Q Key2 i)))).
Proof. unfold X_content in *. Opaque Z.add. Opaque Z.mul. simpl.
  rewrite (Z.add_comm _ 1), Z2Nat.inj_add; try omega. simpl.
  rewrite Z2Nat.id; try omega. subst l; reflexivity.
Qed.

(*Issue : writing the lemma using the Delta := func_typcontext ...
  @semax CompSepcs Espec Delta ...
  leads to failure - but only 40 lines down, in the call to forward_call,
  where check_Delta (and also check_DeltaOLD will now fail with
  the temporary "Error in check_Delta (match-case 3)" message,
  or (if the error message is replaced by the original
   abbreviate D : tycontext as Delta) the fwd_call'/forward_call/forward_callOLD
  will completely fail since it introduces a Delta0.
  I think we need to complement the line (
    Delta := @abbreviate tycontext (mk_tycontext _ _ _ _ _) |- _ => ...
  in checkDelta (checkDeltaOLD) with a second option,
  Delta := func_tycontext ... =>.
  Note that
  1. rerunning abbreviate_semax at that place (before calling forward_call)
     does not resolve the situation
  2. In the master-branch, we actually could write the lemma using Delta :=,
     so this is really an isstue ith the new_compcert branch*)


Lemma f_core_loop1: forall (Espec : OracleKind)
c k h nonce out OUT 
(data : SixteenByte * SixteenByte * (SixteenByte * SixteenByte))
(*(Delta := func_tycontext f_core SalsaVarSpecs SalsaFunSpecs) *)
(out' : name _out)
(in' : name _in)
(k' : name _k)
(c' : name _c)
(h' : name _h)
(aux' : name _aux)
w x y t,
@semax CompSpecs Espec (func_tycontext f_core SalsaVarSpecs SalsaFunSpecs)
  (PROP  ()
   LOCAL  (lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
   lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w; temp _in nonce;
   temp _out out; temp _c c; temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(data_at_ Tsh (tarray tuint 16) y);
   `(data_at_ Tsh (tarray tuint 4) t); `(data_at_ Tsh (tarray tuint 16) x);
   `(data_at_ Tsh (tarray tuint 16) w); `(CoreInSEP data (nonce, c, k));
   `(data_at Tsh (tarray tuchar 64) OUT out)))
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                       (Econst_int (Int.repr 4) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Ssequence
            (Scall (Some 177%positive)
              (Evar _ld32 (Tfunction (Tcons (tptr tuchar) Tnil) tuint
                            cc_default))
              ((Ebinop Oadd (Etempvar _c (tptr tuchar))
                 (Ebinop Omul (Econst_int (Int.repr 4) tint)
                   (Etempvar _i tint) tint) (tptr tuchar)) :: nil))
            (Sset _aux (Etempvar 177%positive tuint)))
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd (Evar _x (tarray tuint 16))
                  (Ebinop Omul (Econst_int (Int.repr 5) tint)
                    (Etempvar _i tint) tint) (tptr tuint)) tuint)
              (Etempvar _aux tuint))
            (Ssequence
              (Ssequence
                (Scall (Some 178%positive)
                  (Evar _ld32 (Tfunction (Tcons (tptr tuchar) Tnil) tuint
                                cc_default))
                  ((Ebinop Oadd (Etempvar _k (tptr tuchar))
                     (Ebinop Omul (Econst_int (Int.repr 4) tint)
                       (Etempvar _i tint) tint) (tptr tuchar)) :: nil))
                (Sset _aux (Etempvar 178%positive tuint)))
              (Ssequence
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Evar _x (tarray tuint 16))
                      (Ebinop Oadd (Econst_int (Int.repr 1) tint)
                        (Etempvar _i tint) tint) (tptr tuint)) tuint)
                  (Etempvar _aux tuint))
                (Ssequence
                  (Ssequence
                    (Scall (Some 179%positive)
                      (Evar _ld32 (Tfunction (Tcons (tptr tuchar) Tnil) tuint
                                    cc_default))
                      ((Ebinop Oadd (Etempvar _in (tptr tuchar))
                         (Ebinop Omul (Econst_int (Int.repr 4) tint)
                           (Etempvar _i tint) tint) (tptr tuchar)) :: nil))
                    (Sset _aux (Etempvar 179%positive tuint)))
                  (Ssequence
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Evar _x (tarray tuint 16))
                          (Ebinop Oadd (Econst_int (Int.repr 6) tint)
                            (Etempvar _i tint) tint) (tptr tuint)) tuint)
                      (Etempvar _aux tuint))
                    (Ssequence
                      (Ssequence
                        (Scall (Some 180%positive)
                          (Evar _ld32 (Tfunction (Tcons (tptr tuchar) Tnil)
                                        tuint cc_default))
                          ((Ebinop Oadd
                             (Ebinop Oadd (Etempvar _k (tptr tuchar))
                               (Econst_int (Int.repr 16) tint) (tptr tuchar))
                             (Ebinop Omul (Econst_int (Int.repr 4) tint)
                               (Etempvar _i tint) tint) (tptr tuchar)) ::
                           nil))
                        (Sset _aux (Etempvar 180%positive tuint)))
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Evar _x (tarray tuint 16))
                            (Ebinop Oadd (Econst_int (Int.repr 11) tint)
                              (Etempvar _i tint) tint) (tptr tuint)) tuint)
                        (Etempvar _aux tuint))))))))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
  (normal_ret_assert (
PROP  ()
   LOCAL  (temp _i (Vint (Int.repr 4)); lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(data_at_ Tsh (tarray tuint 16) y);
   `(data_at_ Tsh (tarray tuint 4) t);
   `(EX  l : list val,
     !!X_content data 4 l && data_at Tsh (tarray tuint 16) l x);
   `(data_at_ Tsh (tarray tuint 16) w); `(CoreInSEP data (nonce, c, k));
   `(data_at Tsh (tarray tuchar 64) OUT out)))).
Proof. intros. abbreviate_semax.
LENBforward_for_simple_bound 4 (EX i:Z, 
   PROP  ()
   LOCAL  ( 
   lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
   lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w; temp _in nonce;
   temp _out out; temp _c c; temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(data_at_ Tsh (tarray tuint 16) y);
   `(data_at_ Tsh (tarray tuint 4) t);
   `(EX l:_, !!(X_content data i l) && data_at Tsh (tarray tuint 16) l x);
   `(data_at_ Tsh (tarray tuint 16) w); `(CoreInSEP data (nonce, c, k));
   `(data_at Tsh (tarray tuchar 64) OUT out))).
{ entailer. apply (exp_right (list_repeat 16 Vundef)). entailer. }
{ rename H into I.
 
  destruct data as ((Nonce, C), Key). unfold CoreInSEP.
  unfold SByte at 2. normalize. intros X0; normalize. rename H into X0cont.

  assert (C16:= SixteenByte2ValList_Zlength C).
  remember (SplitSelect16Q C i) as FB; destruct FB as (Front, Back).
  (*rewrite (Select_SplitSelect16Q C i _ _ HeqFB) in *.*)
  (*assert (FrontBack:= Select_SplitSelect16Q_Zlength _ _ _ _ HeqFB I). (* as [FL BL].*)*)
  assert_PROP (field_compatible (Tarray tuchar 16 noattr) [] c). entailer.
  rename H into FC.
  assert_PROP(isptr c). entailer. apply isptrD in H; destruct H as [cb [coff CP]]. rewrite CP in *.
  rewrite (split3_data_at_Tarray_at_tuchar Tsh 16 (Zlength (QuadChunks2ValList Front)) 
        (Zlength (QuadChunks2ValList [Select16Q C i]))); trivial; 
    repeat rewrite Zlength_app;
    repeat rewrite QuadChunk2ValList_ZLength;
(*    repeat rewrite FL; try rewrite BL; *)
    try rewrite <- QuadByteValList_ZLength; try rewrite Z.mul_1_r; try omega.
    2: destruct (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFB I) as [FL _]; rewrite FL; omega.
    2: destruct (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFB I) as [FL _]; rewrite FL; omega.
  normalize. 
  rewrite (Select_SplitSelect16Q C i _ _ HeqFB) at 2.
  rewrite (sublist_app2 (4 * Zlength Front) (4 + 4 * Zlength Front)); 
    repeat rewrite QuadChunk2ValList_ZLength. 
    2: destruct (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFB I) as [FL _]; rewrite FL; omega.
  rewrite Zminus_diag, Z.add_simpl_r.
  unfold at_offset at 1.
  rewrite (sublist0_app1 4), (sublist_same 0 4); try rewrite QuadChunk2ValList_ZLength;
     try rewrite Z.mul_1_r; trivial; try omega.
Transparent core_spec. Transparent ld32_spec. Transparent L32_spec. Transparent st32_spec.
Transparent crypto_core_salsa20_spec. Transparent crypto_core_hsalsa20_spec. 
  forward_call (offset_val (Int.repr (4 * i)) (Vptr cb coff), Select16Q C i) pat.
(*Ltac check_DeltaOLD :=
match goal with 
 | Delta := @abbreviate tycontext (mk_tycontext _ _ _ _ _) |- _ =>
    match goal with 
    | |- _ => clear Delta; check_DeltaOLD
    | |- semax Delta _ _ _ => idtac 
    end
 | _ => first [simplify_Delta_OLD | fail 4 "Error in check_Delta (match-case 2): simplify_Delta fails. (Definition is in semax_tactic.v)"];
     match goal with |- semax ?D _ _ _ => 
            fail 4 "Error in check_Delta (match-case 3)"
            (*abbreviate D : tycontext as Delta*)
     end
end. (* abbreviate_semax. unfold Delta. unfold func_tycontext. simpl.*)
  (*check_DeltaOLD. succeeds, while check_Delta. fails*)
Tactic Notation "forward_callOLD" constr(witness) simple_intropattern_list(v) :=
    check_canonical_call;
    check_DeltaOLD;
    fwd_call' witness;
  [ .. 
  | first 
      [ (* body of uniform_intros tactic *)
         (((assert True by (intros v; apply I);
            assert (forall a: unit, True) by (intros v; apply I);
            fail 1)
          || intros v) 
        || idtac);
        (* end body of uniform_intros tactic *)
        match goal with
        | |- semax _ _ _ _ => idtac 
        | |- unit -> semax _ _ _ _ => intros _ 
        end;
        repeat (apply semax_extract_PROP; intro);
       abbreviate_semax;
       try fwd_skip
     | complain_intros
     ]  
  ].
(*Issue: without clearing BL, or unfolding Z.sub in *, even forward_callOLD fails*)
clear BL. Opaque Z.sub. Opaque Z.mul. Opaque Z.add. simpl. rewrite app_nil_r.
abbreviate_semax.
    check_canonical_call;
    check_DeltaOLD.
    fwd_call' (offset_val (Int.repr (4 * i)) (Vptr cb coff), Select16Q C i).
Focus 3.
  forward_callOLD (offset_val (Int.repr (4 * i)) (Vptr cb coff), Select16Q C i) pat.*)

assert (Q: QuadChunks2ValList [Select16Q C i] = QuadByte2ValList (Select16Q C i)) by apply app_nil_r.
 destruct (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFB I) as [FL _]; rewrite FL.
rewrite Q; cancel.
(*Alternative:  to use of Q here:
clear BL. Opaque Z.sub. Opaque Z.mul. Opaque Z.add. simpl. rewrite app_nil_r. cancel.*)

(*Issue: again we need to instantiate parts of LOCAL explicitly, in the "spurious" delete_temps*)
instantiate (1:= [lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out;
   temp _c (Vptr cb coff); temp _k k; temp _h (Vint (Int.repr h))]). admit. admit.

normalize. subst pat.
  apply semax_pre with (P':=
  (PROP  ()
   LOCAL  ( temp _aux (Vint (littleendian (Select16Q C i)));
   temp _i (Vint (Int.repr i));
   lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
   lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w; temp _in nonce;
   temp _out out; temp _c c; temp _k k; temp _h (Vint (Int.repr h)))
   SEP 
   (`(data_at Tsh (Tarray tuchar 16 noattr) (SixteenByte2ValList C) c);
   `(SByte Nonce nonce);
   `(ThirtyTwoByte Key k);
   `(data_at_ Tsh (tarray tuint 16) y); `(data_at_ Tsh (tarray tuint 4) t);
   `(data_at Tsh (tarray tuint 16) X0 x);
   `(data_at_ Tsh (tarray tuint 16) w); 
   `(data_at Tsh (tarray tuchar 64) OUT out)))). 
  { rewrite (Select_SplitSelect16Q C i _ _ HeqFB). unfold QByte.
    rewrite (split3_data_at_Tarray_at_tuchar Tsh 16 (Zlength (QuadChunks2ValList Front)) 4); trivial;
    repeat rewrite Zlength_app; 
    repeat rewrite QuadChunk2ValList_ZLength;
(*    repeat rewrite FL; try rewrite BL; *)
    try rewrite <- QuadByteValList_ZLength; try rewrite Z.mul_1_r; try omega.
     2: destruct (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFB I) as [FL _]; rewrite FL; omega.
     2: destruct (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFB I) as [FL _]; rewrite FL; omega.
     2: destruct (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFB I) as [FL BL]; rewrite FL, BL; omega.
     2: rewrite CP; trivial.
    Opaque Z.sub. Opaque Z.mul. Opaque Z.add. entailer. 
    destruct (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFB I) as [FL BL]; rewrite FL, BL. 
    cancel. 
    rewrite sublist_app2; repeat rewrite QuadChunk2ValList_ZLength; repeat rewrite FL; try omega.
    rewrite Zminus_diag, Z.add_simpl_r.
    unfold at_offset at 1.
    rewrite (sublist0_app1 4), (sublist_same 0 4); try rewrite <- QuadByteValList_ZLength;
        try rewrite app_nil_r; try omega.
    cancel. apply QuadByteValList_ZLength. rewrite <- QuadByteValList_ZLength; omega. }

  (*Store into x[...]*)
  Transparent firstn.
  forward.

  destruct Key as [Key1 Key2]. 
  assert_PROP (field_compatible (Tarray tuchar 32 noattr) [] k).
    solve [unfold ThirtyTwoByte; entailer]. 
  rename H into FCK32.
  erewrite ThirtyTwoByte_split16; trivial. unfold SByte at 2. normalize.
  assert_PROP (field_compatible (Tarray tuchar 16 noattr) [] k). solve [entailer].
  rename H into FCK16.
  assert (K1_16:= SixteenByte2ValList_Zlength Key1).
  remember (SplitSelect16Q Key1 i) as FB_K1. destruct FB_K1 as (Front_K1, Back_K1).
(*  rewrite (Select_SplitSelect16Q Key1 i _ _ HeqFB_K1).*)
  erewrite Select_Unselect_Tarray_at. (*; repeat rewrite <- K1_16; trivial.*)
    2: symmetry; apply (Select_SplitSelect16Q Key1 i _ _ HeqFB_K1). 2: assumption. 
    2: rewrite <- (Select_SplitSelect16Q Key1 i _ _ HeqFB_K1), <- K1_16; trivial.
    2: rewrite <- (Select_SplitSelect16Q Key1 i _ _ HeqFB_K1), <- K1_16; cbv; trivial.
  unfold Select_at. simpl. rewrite app_nil_r.
  (*assert (FrontBackK1:= (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFB_K1 I)) as [FLK BLK].*)
  rewrite <- QuadByteValList_ZLength. (*rewrite Z.mul_1_l. *)
  rewrite  QuadChunk2ValList_ZLength.
Transparent core_spec. Transparent ld32_spec. Transparent L32_spec. Transparent st32_spec.
Transparent crypto_core_salsa20_spec. Transparent crypto_core_hsalsa20_spec.
  forward_call (offset_val (Int.repr (4 * i)) k, 
                 Select16Q Key1 i) v. 
  { destruct (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFB_K1 I) as [FLK _]; rewrite FLK.
    cancel. }
  { instantiate (1:= [lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
      lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w; temp _in nonce;
      temp _out out; temp _c c; temp _k k; temp _h (Vint (Int.repr h))]).
      admit. }
  { admit. }
Opaque core_spec. Opaque ld32_spec. Opaque L32_spec. Opaque st32_spec.
Opaque crypto_core_salsa20_spec. Opaque crypto_core_hsalsa20_spec.
  normalize. subst v.

  apply semax_pre with (P':=
  (PROP  ()
   LOCAL  ((*temp _aux v;*) temp _aux (Vint (littleendian (Select16Q Key1 i)));
   temp _i (Vint (Int.repr i));
   lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
   lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w; temp _in nonce;
   temp _out out; temp _c c; temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(ThirtyTwoByte (Key1,Key2) k);
   `(data_at Tsh (Tarray tuchar 16 noattr) (SixteenByte2ValList C) c);
   `(SByte Nonce nonce); `(data_at_ Tsh (tarray tuint 16) y);
   `(data_at_ Tsh (tarray tuint 4) t);
   `(data_at Tsh (tarray tuint 16)
       (upd_Znth_in_list (5 * i) X0
          (Vint (littleendian (Select16Q C i)))) x);
   `(data_at_ Tsh (tarray tuint 16) w);
   `(data_at Tsh (tarray tuchar 64) OUT out)))). 
  { erewrite ThirtyTwoByte_split16; trivial. 
    entailer. cancel.
    unfold SByte. rewrite (Select_SplitSelect16Q _ _ _ _ HeqFB_K1) in *.
    erewrite Select_Unselect_Tarray_at; try rewrite <- K1_16; try reflexivity; try assumption.
    unfold QByte, Select_at. simpl. repeat rewrite app_nil_r.
    rewrite  QuadChunk2ValList_ZLength.
    rewrite <- QuadByteValList_ZLength.
    destruct (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFB_K1 I) as [FLK _]; rewrite FLK; cancel.
    rewrite <- K1_16; trivial. rewrite <- K1_16; cbv; trivial. }

  (*Store into x[...]*)
  forward. simpl.

  (*Load nonce*)
  unfold SByte at 1.
  assert (N16:= SixteenByte2ValList_Zlength Nonce).
  remember (SplitSelect16Q Nonce i) as FB_N; destruct FB_N as (Front_N, BACK_N).
    rewrite (Select_SplitSelect16Q _ i _ _ HeqFB_N) in *. 
  assert_PROP (field_compatible (Tarray tuchar 16 noattr) [] nonce). entailer.
  rename H into FCN.
  erewrite Select_Unselect_Tarray_at with (d:=nonce); try reflexivity; try assumption. normalize.
  2: rewrite <- N16; trivial. 2: rewrite <- N16; cbv; trivial.
  unfold Select_at. simpl. rewrite app_nil_r.
  (*destruct (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFB_N I) as [FrontN BackN].*)
Transparent core_spec. Transparent ld32_spec. Transparent L32_spec. Transparent st32_spec.
Transparent crypto_core_salsa20_spec. Transparent crypto_core_hsalsa20_spec.
  forward_call (offset_val (Int.repr (4 * i)) nonce, 
                 Select16Q Nonce i) v. 
  { rewrite <- QuadByteValList_ZLength. (*rewrite Z.mul_1_l.  simpl.*)
    rewrite  QuadChunk2ValList_ZLength.
    destruct (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFB_N I) as [FrontN _]; rewrite FrontN.
    cancel. }
  { instantiate (1:= [lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
      lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w; temp _in nonce;
      temp _out out; temp _c c; temp _k k; temp _h (Vint (Int.repr h))]).
      admit. }
  { admit. }
Opaque core_spec. Opaque ld32_spec. Opaque L32_spec. Opaque st32_spec.
Opaque crypto_core_salsa20_spec. Opaque crypto_core_hsalsa20_spec.
  
  normalize. subst v.
  apply semax_pre with (P':=
  (PROP  ()
   LOCAL  ((*temp _aux v; *)
   temp _aux (Vint (littleendian (Select16Q Nonce i)));
   temp _i (Vint (Int.repr i));
   lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
   lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w; temp _in nonce;
   temp _out out; temp _c c; temp _k k; temp _h (Vint (Int.repr h)))
   SEP 
   (`(data_at Tsh (Tarray tuchar 16 noattr) (SixteenByte2ValList C) c);
   `(SByte Nonce nonce);
   `(ThirtyTwoByte (Key1,Key2) k);
   `(data_at_ Tsh (tarray tuint 16) y); `(data_at_ Tsh (tarray tuint 4) t);
   `(data_at Tsh (tarray tuint 16)
       (upd_Znth_in_list (1 + i)
          (upd_Znth_in_list (5 * i) X0
             (Vint (littleendian (Select16Q C i))))
          (Vint (littleendian (Select16Q Key1 i)))) x);
   `(data_at_ Tsh (tarray tuint 16) w);
   `(data_at Tsh (tarray tuchar 64) OUT out) (*`(data_block Tsh OUT out)*)))). 
  { entailer. cancel. 
   
    (*Apart from the unfold QByte, the next 9 lines are exactly as above, inside the function call*)
    unfold SByte. rewrite (Select_SplitSelect16Q _ _ _ _ HeqFB_N) in *.
    erewrite Select_Unselect_Tarray_at; try reflexivity; try assumption. 
    unfold QByte, Select_at. simpl. rewrite app_nil_r. cancel.
    rewrite <- QuadByteValList_ZLength. (*rewrite Z.mul_1_l. simpl.*)
    rewrite  QuadChunk2ValList_ZLength.
    destruct (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFB_N I) as [FrontN _]; rewrite FrontN; cancel. 

    rewrite <- N16; trivial. rewrite <- N16; cbv; trivial. }

  (*Store into x[...]*)
  forward.

  (*Load Key2*)
  rewrite ThirtyTwoByte_split16; trivial. normalize.
  unfold SByte at 2.
  assert (K2_16:= SixteenByte2ValList_Zlength Key2).
  assert_PROP(field_compatible (Tarray tuchar 16 noattr) [] (offset_val (Int.repr 16) k)). entailer.
  rename H into FCK2.
  remember (SplitSelect16Q Key2 i) as FB_K2; destruct FB_K2 as (Front_K2, Back_K2).
  rewrite (Select_SplitSelect16Q _ i _ _ HeqFB_K2) in *. 
    erewrite Select_Unselect_Tarray_at with (d:=offset_val (Int.repr 16) k); try reflexivity; try assumption. normalize.
  2: rewrite <- K2_16; trivial. 2: rewrite <- K2_16; cbv; trivial.
  unfold Select_at. simpl. rewrite app_nil_r.
  assert_PROP (isptr k). unfold SByte. entailer. 
  apply isptrD in H; destruct H as [kb [koff KP]]; rewrite KP in *. 
   
Transparent core_spec. Transparent ld32_spec. Transparent L32_spec. Transparent st32_spec.
Transparent crypto_core_salsa20_spec. Transparent crypto_core_hsalsa20_spec.
repeat rewrite <- QuadByteValList_ZLength. simpl.
    rewrite  QuadChunk2ValList_ZLength.
  forward_call (Vptr kb
           (Int.add (Int.add koff (Int.repr 16)) (Int.repr (4 * Zlength Front_K2))),
                 Select16Q Key2 i) v. 
Opaque core_spec. Opaque ld32_spec. Opaque L32_spec. Opaque st32_spec.
Opaque crypto_core_salsa20_spec. Opaque crypto_core_hsalsa20_spec.
  { destruct (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFB_K2 I) as [FK2 _]; rewrite FK2. apply prop_right; trivial. }
  { instantiate (1:= [lvar _t (tarray tuint 4) t;
     lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
     lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
     temp _k (Vptr kb koff); temp _h (Vint (Int.repr h))]). admit. }
  { admit. }

  normalize. subst v.
  apply semax_pre with (P':=
  (PROP  ()
   LOCAL  ((*temp _aux v;*)
   temp _aux (Vint (littleendian (Select16Q Key2 i)));
   temp _i (Vint (Int.repr i));
   lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
   lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w; temp _in nonce;
   temp _out out; temp _c c; temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(ThirtyTwoByte (Key1,Key2) k);
   `(data_at Tsh (Tarray tuchar 16 noattr) (SixteenByte2ValList C) c);
   `(SByte Nonce nonce); `(data_at_ Tsh (tarray tuint 16) y);
   `(data_at_ Tsh (tarray tuint 4) t);
   `(data_at Tsh (tarray tuint 16)
       (upd_Znth_in_list (6 + i)
          (upd_Znth_in_list (1 + i)
             (upd_Znth_in_list (5 * i) X0
                (Vint (littleendian (Select16Q C i))))
             (Vint (littleendian (Select16Q Key1 i))))
          (Vint (littleendian (Select16Q Nonce i)))) x);
   `(data_at_ Tsh (tarray tuint 16) w); 
   `(data_at Tsh (tarray tuchar 64) OUT out) (*`(data_block Tsh OUT out)*)))). 
  { erewrite ThirtyTwoByte_split16. 2: rewrite KP; assumption.
    entailer. cancel. 
   
    (*Apart from the unfold QByte, the next 9 lines are exactly as above, inside the function call*)
    unfold SByte. rewrite (Select_SplitSelect16Q _ _ _ _ HeqFB_K2) in *.
    erewrite Select_Unselect_Tarray_at; try reflexivity; try assumption. 
    unfold QByte, Select_at. simpl. repeat rewrite app_nil_r. cancel.
    rewrite <- QuadByteValList_ZLength. (*rewrite Z.mul_1_l. simpl.*)
    rewrite  QuadChunk2ValList_ZLength. rewrite Int.add_assoc. rewrite add_repr. cancel.

    rewrite <- K2_16. assumption.
    rewrite <- K2_16. cbv; trivial. }

  (*Store into x[...]*)
  forward.

  entailer. 
  apply (exp_right (upd_Znth_in_list (11 + i)
     (upd_Znth_in_list (6 + i)
        (upd_Znth_in_list (1 + i)
           (upd_Znth_in_list (5 * i) X0
              (Vint (littleendian (Select16Q C i))))
           (Vint (littleendian (Select16Q Key1 i))))
        (Vint (littleendian (Select16Q Nonce i))))
     (Vint (littleendian (Select16Q Key2 i))))).
  entailer.
  apply andp_right. 2: cancel.
  apply prop_right. clear - X0cont I. apply XcontUpdate; trivial. }
entailer. apply (exp_right l). entailer.
Qed.

Lemma XX data l: X_content data 4 l -> 
  l = match data with ((Nonce, C), (Key1, Key2)) =>
          match Nonce with (N1, N2, N3, N4) =>
          match C with (C1, C2, C3, C4) =>
          match Key1 with (K1, K2, K3, K4) =>
          match Key2 with (L1, L2, L3, L4) =>
      map Vint (map littleendian [C1; K1; K2; K3; 
                                  K4; C2; N1; N2;
                                  N3; N4; C3; L1;
                                  L2; L3; L4; C4]) 
      end end end end end.
Proof.
intros. red in H. subst l. 
apply upd_upto_char. reflexivity.
Qed.
