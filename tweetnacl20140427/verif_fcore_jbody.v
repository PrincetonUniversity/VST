Require Import Recdef.
Require Import floyd.proofauto.
Local Open Scope logic.
Require Import List. Import ListNotations.
Require Import general_lemmas.

Require Import split_array_lemmas.
(*Require Import fragments.*)
Require Import ZArith. 
Require Import tweetNaclBase.
Require Import Salsa20.
Require Import verif_salsa_base.
Require Import tweetnaclVerifiableC.
Require Import spec_salsa. Opaque Snuffle.Snuffle.

Opaque Zplus. Opaque Z.mul. Opaque mult. Opaque plus. Opaque skipn. Opaque Z.sub.
    Opaque littleendian.
    Opaque littleendian_invert. Opaque Snuffle20. Opaque prepare_data. 
    Opaque QuadByte2ValList. Opaque fcore_result.

Opaque core_spec. Opaque ld32_spec. Opaque L32_spec. Opaque st32_spec.
Opaque crypto_core_salsa20_spec. Opaque crypto_core_hsalsa20_spec.

Lemma array_copy1I Espec:
forall i wlist data OUT j t y x w nonce out c k h ys xs
       (J:0<=j<4) (XL: Zlength xs = 16),
@semax CompSpecs Espec
  (initialized_list [_i; _j]
     (func_tycontext f_core SalsaVarSpecs SalsaFunSpecs))
  (PROP  ()
   LOCAL  (temp _j (Vint (Int.repr j)); temp _i (Vint (Int.repr i));
   lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
   lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w; temp _in nonce;
   temp _out out; temp _c c; temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(data_at Tsh (tarray tuint 16) wlist w);
   `(data_at Tsh (tarray tuint 16) (map Vint xs) x);
   `(data_at Tsh (tarray tuint 16) ys y);
   `(data_at_ Tsh (tarray tuint 4) t);
   `(CoreInSEP data (nonce, c, k));
   `(data_at Tsh (tarray tuchar 64) OUT out)))
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
   SEP  (`(data_at Tsh (tarray tuint 16) wlist w);
   `(data_at Tsh (tarray tuint 16) (map Vint xs) x);
   `(data_at Tsh (tarray tuint 16) ys y);
   `(EX  l : list val,
     !!(forall mm : Z,
         0 <= mm < 4 ->
         Znth mm l Vundef =
         Znth ((5 * j + 4 * mm) mod 16) (map Vint xs) Vundef)
        && data_at Tsh (tarray tuint 4) l t);
   `(CoreInSEP data (nonce, c, k)); 
   `(data_at Tsh (tarray tuchar 64) OUT out)))).
Proof. intros. abbreviate_semax.
LENBforward_for_simple_bound 4
 (EX m:Z, 
  (PROP  ()
   LOCAL  (temp _i (Vint (Int.repr i)); temp _j (Vint (Int.repr j)); lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(data_at Tsh (tarray tuint 16) wlist w);
   `(data_at Tsh (tarray tuint 16) ys y);
   `(data_at Tsh (tarray tuint 16) (map Vint xs) x);
   `(EX l:_, !!(forall mm, 0<=mm<m -> Znth mm l Vundef = 
                  Znth ((5*j+4*mm) mod 16) (map Vint xs) Vundef)
            && data_at Tsh (tarray tuint 4) l t); `(CoreInSEP data (nonce, c, k));
   `(data_at Tsh (tarray tuchar 64) OUT out)))); try reflexivity; try auto with closed; try repable_signed.

  { entailer. apply (exp_right (list_repeat 4 Vundef)). entailer. 
    apply andp_right. apply prop_right. intros; omega. cancel. }
  { rename i0 into m. rename H into M. normalize. intros T. normalize.
    rename H into HT.
    assert_PROP (Zlength T = 4). entailer. rename H into TL.
    destruct (Z_mod_lt (5 * j + 4 * m) 16) as [M1 M2]. omega.
    destruct (Znth_mapVint xs ((5 * j + 4 * m) mod 16) Vundef) as [v NV].
       rewrite XL. split; assumption.
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
    forward. { entailer. rewrite <- Heqb. simpl. apply prop_right; trivial. }
    unfold sem_mod, sem_binarith, both_int; simpl. rewrite <- Heqb. simpl.
    unfold Int.mods. repeat rewrite Int.signed_repr.
      2: rewrite int_max_signed_eq, int_min_signed_eq; omega.
      2: rewrite int_max_signed_eq, int_min_signed_eq; omega.
    rewrite Z.rem_mod_nonneg; try omega.
    forward. { entailer. rewrite NV. simpl. apply prop_right; trivial. }
    rewrite NV.
    forward.
    { entailer. 
      apply (exp_right (upd_Znth_in_list m T (Vint _id))).
      entailer. apply andp_right. 2: cancel. 
      apply prop_right.
      intros. 

      destruct (zeq mm m); subst.
      + rewrite upd_Znth_same; try omega. rewrite NV; trivial. 
      + rewrite upd_Znth_diff; try omega. apply HT; omega. } 
  }
entailer. apply (exp_right l). entailer. cancel.
Qed. 

Lemma array_copy3:
forall (Espec : OracleKind) c k h nonce out OUT
       (data : SixteenByte * SixteenByte * (SixteenByte * SixteenByte))
       (out' : name _out)
       (in' : name _in)
       (k' : name _k)
       (c' : name _c)
       (h' : name _h)
       (aux' : name _aux)
       i w x y t ys xlist wlist 
       (WL: length wlist = 16%nat)
       (XL: length xlist = 16%nat)
       (WZ: forall m, 0<=m<16 -> exists mval, Znth m wlist Vundef =Vint mval),
@semax CompSpecs Espec
  (initialized_list [_i; _j]
     (func_tycontext f_core SalsaVarSpecs SalsaFunSpecs))
  (PROP  ()
   LOCAL  (temp _j (Vint (Int.repr 4)); temp _i (Vint (Int.repr i)); lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(data_at Tsh (tarray tuint 16) wlist w);
   `(data_at Tsh (tarray tuint 16) xlist x); 
   `(data_at Tsh (tarray tuint 16) ys y);
   `(data_at_ Tsh (tarray tuint 4) t);
   `(CoreInSEP data (nonce, c, k));
   `(data_at Tsh (tarray tuchar 64) OUT out)))
  (Sfor (Sset _m (Econst_int (Int.repr 0) tint))
     (Ebinop Olt (Etempvar _m tint) (Econst_int (Int.repr 16) tint) tint)
     (Ssequence
        (Sset _aux
           (Ederef
              (Ebinop Oadd (Evar _w (tarray tuint 16)) (Etempvar _m tint)
                 (tptr tuint)) tuint))
        (Sassign
           (Ederef
              (Ebinop Oadd (Evar _x (tarray tuint 16)) (Etempvar _m tint)
                 (tptr tuint)) tuint) (Etempvar _aux tuint)))
     (Sset _m
        (Ebinop Oadd (Etempvar _m tint) (Econst_int (Int.repr 1) tint) tint)))
  (normal_ret_assert
  (PROP  ()
   LOCAL  (temp _j (Vint (Int.repr 4)); temp _i (Vint (Int.repr i)); lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(data_at Tsh (tarray tuint 16) wlist w);
   `(data_at Tsh (tarray tuint 16) ys y);
   `(data_at Tsh (tarray tuint 16) wlist x); 
   `(data_at_ Tsh (tarray tuint 4) t);
   `(CoreInSEP data (nonce, c, k));
   `(data_at Tsh (tarray tuchar 64) OUT out)))).
Proof. intros. abbreviate_semax.
LENBforward_for_simple_bound 16 (EX m:Z, 
  (PROP  ()
   LOCAL  (temp _j (Vint (Int.repr 4)); temp _i (Vint (Int.repr i)); lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(data_at Tsh (tarray tuint 16) wlist w);
   `(data_at Tsh (tarray tuint 16) ys y);
   `(EX mlist:_, !!(forall mm, 0<=mm<m -> Znth mm mlist Vundef = Znth mm wlist Vundef)
                && data_at Tsh (tarray tuint 16) mlist x);
   `(data_at_ Tsh (tarray tuint 4) t); `(CoreInSEP data (nonce, c, k));
   `(data_at Tsh (tarray tuchar 64) OUT out)))).
{ entailer. apply (exp_right xlist). entailer. apply andp_right. apply prop_right. intros; omega. cancel. }
{ normalize. intros mlist. normalize. rename H into M. rename i0 into m.
       rename H0 into HM.
       destruct (WZ _ M) as [mval MVAL].
       assert_PROP (Zlength mlist = 16). entailer. rename H into ML.
       forward. 
       { entailer. rewrite MVAL. apply prop_right. simpl; trivial. }
       forward.
       { entailer. rewrite MVAL. simpl. 
         apply (exp_right (upd_Znth_in_list m mlist (Vint mval))).
         entailer. apply andp_right. 2: cancel.
         apply prop_right. 
         intros.
         destruct (zeq mm m); subst.
         + rewrite MVAL, upd_Znth_same; trivial. omega.
         + rewrite <- HM. 2: omega.
        apply upd_Znth_diff; trivial; omega. } }
{ entailer. cancel. apply data_at_ext.
  eapply Znth_extensional with (d:=Vundef). clear - H8 H19. rewrite <- H8 in H19. apply H19.
  intros k K. apply H17. rewrite <- H19; apply K. }
Qed.

Lemma pattern1_noStmt Espec Source1 Source2 Target Offset: forall
  (S1Range: 0 <= Source1 < 4) (S2Range: 0 <= Source2 < 4) (TgtRange: 0 <= Target < 4)
  (HOffset: 0 < Int.unsigned (Int.repr Offset) < 32)
  ValS1 ValS2 ValTgt tlist
  (HS1: Znth Source1 tlist Vundef = Vint ValS1)
  (HS2: Znth Source2 tlist Vundef = Vint ValS2)
  (HTgt: Znth Target tlist Vundef = Vint ValTgt)
  data c ys wlist OUT i j t y x w out nonce k h xs,
@semax CompSpecs Espec (initialized_list [_i; _j; _m]
     (func_tycontext f_core SalsaVarSpecs SalsaFunSpecs))
  (PROP  ()
   LOCAL  (temp _i (Vint (Int.repr i)); temp _m (Vint (Int.repr 4));
   temp _j (Vint (Int.repr j)); lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(data_at Tsh (tarray tuint 4) tlist t);
   `(data_at Tsh (tarray tuint 16) wlist w);
   `(data_at Tsh (tarray tuint 16) xs x); 
   `(data_at Tsh (tarray tuint 16) ys y);
   `(CoreInSEP data (nonce, c, k));
   `(data_at Tsh (tarray tuchar 64) OUT out)))
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
                                  (Scall (Some 181%positive)
                                    (Evar _L32 (Tfunction
                                                 (Tcons tuint
                                                   (Tcons tint Tnil)) tuint
                                                 cc_default))
                                    ((Etempvar _aux tuint) ::
                                     (Econst_int (Int.repr Offset) tint) :: nil))
                                  (Sset _aux (Etempvar 181%positive tuint)))
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
   SEP  (`(data_at Tsh (tarray tuint 4) 
        (upd_Znth_in_list Target tlist
           (Vint
              (Int.xor ValTgt (Int.rol (Int.add ValS1 ValS2) (Int.repr Offset)))))
        t); 
   `(data_at Tsh (tarray tuint 16) wlist w);
   `(data_at Tsh (tarray tuint 16) xs x);
   `(data_at Tsh (tarray tuint 16) ys y);
   `(CoreInSEP data (nonce, c, k));
   `(data_at Tsh (tarray tuchar 64) OUT out)))).
Proof. intros. abbreviate_semax.
  forward v1.  
  { entailer. rewrite HS1. apply prop_right; simpl; trivial. }
  rewrite HS1. 
  forward v2. 
  { entailer. rewrite HS2. apply prop_right; simpl; trivial. } 
  rewrite HS2.
  forward sum.
Transparent core_spec. Transparent ld32_spec. Transparent L32_spec. Transparent st32_spec.
Transparent crypto_core_salsa20_spec. Transparent crypto_core_hsalsa20_spec.
  forward_call (Int.add ValS1 ValS2, Int.repr Offset) v.
Opaque core_spec. Opaque ld32_spec. Opaque L32_spec. Opaque st32_spec.
Opaque crypto_core_salsa20_spec. Opaque crypto_core_hsalsa20_spec.
  { instantiate (1:= [lvar _t (tarray tuint 4) t;
       lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
       lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
       temp _k k; temp _h (Vint (Int.repr h))]). admit. } admit. (*VST Issue: the usual delete_temps / LOCALS issue*)
(*  { entailer.
    assert (FR: Frame = [`(data_at Tsh (tarray tuint 4) tlist t * data_at Tsh (tarray tuint 16) wlist w *
           data_at Tsh (tarray tuint 16) xs x *
           data_at Tsh (tarray tuint 16) ys y * CoreInSEP data (nonce, c, k) *
           data_at Tsh (tarray tuchar 64) OUT out)]). 
       subst Frame. reflexivity.
    subst Frame; clear FR. simpl. entailer. } 
  { constructor; constructor. (* TODO - is the existence of this subgoal linked to the failure of forward_call'??*) }
  after_call.  
  simpl; normalize. subst x0.  *) subst v.
  forward u.
  { entailer. rewrite HTgt. apply prop_right; simpl; trivial. }  
  subst u.
  rewrite HTgt. 
  forward u.
  forward. entailer.
Qed.
(*
Lemma pattern1_noStmt Espec Source1 Source2 Target Offset: forall
  (S1Range: 0 <= Source1 < 4) (S2Range: 0 <= Source2 < 4) (TgtRange: 0 <= Target < 4)
  (HOffset: 0 < Int.unsigned (Int.repr Offset) < 32)
  ValS1 ValS2 ValTgt tlist
  (HS1: Znth Source1 tlist Vundef = Vint ValS1)
  (HS2: Znth Source2 tlist Vundef = Vint ValS2)
  (HTgt: Znth Target tlist Vundef = Vint ValTgt)
  data c ys wlist OUT i j t y x w out nonce k h xs,
@semax CompSpecs Espec (initialized_list [_i; _j; _m]
     (func_tycontext f_core SalsaVarSpecs SalsaFunSpecs))
  (PROP  ()
   LOCAL  (temp _i (Vint (Int.repr i)); temp _m (Vint (Int.repr 4));
   temp _j (Vint (Int.repr j)); lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(data_at Tsh (tarray tuint 4) tlist t);
   `(data_at Tsh (tarray tuint 16) wlist w);
   `(data_at Tsh (tarray tuint 16) xs x); 
   `(data_at Tsh (tarray tuint 16) ys y);
   `(CoreInSEP data (nonce, c, k));
   `(data_at Tsh (tarray tuchar 64) OUT out)))(Ssequence
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
                 (Scall (Some _aux'4)
                    (Evar _L32
                       (Tfunction (Tcons tuint (Tcons tint Tnil)) tuint
                          cc_default))
                    [Etempvar _aux tuint; Econst_int (Int.repr Offset) tint])
                 (Sset _aux (Etempvar _aux'4 tuint)))
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
   SEP  (`(data_at Tsh (tarray tuint 4) 
        (upd_Znth_in_list Target tlist
           (Vint
              (Int.xor ValTgt (Int.rol (Int.add ValS1 ValS2) (Int.repr Offset)))))
        t); 
   `(data_at Tsh (tarray tuint 16) wlist w);
   `(data_at Tsh (tarray tuint 16) xs x);
   `(data_at Tsh (tarray tuint 16) ys y);
   `(CoreInSEP data (nonce, c, k));
   `(data_at Tsh (tarray tuchar 64) OUT out)))).
Proof. intros. Transparent firstn.
  forward v1.  
  { entailer. rewrite HS1. entailer. }
  rewrite HS1. 
  forward v2. 
  { entailer. rewrite HS2. entailer. } 
  rewrite HS2.
  forward sum. subst sum.
Transparent core_spec. Transparent ld32_spec. Transparent L32_spec. Transparent st32_spec.
Transparent crypto_core_salsa20_spec. Transparent crypto_core_hsalsa20_spec.
  forward_call (Int.add ValS1 ValS2, Int.repr Offset). (*TODO: forward_call' fails*)
Opaque core_spec. Opaque ld32_spec. Opaque L32_spec. Opaque st32_spec.
Opaque crypto_core_salsa20_spec. Opaque crypto_core_hsalsa20_spec.
  { entailer.
    assert (FR: Frame = [`(data_at Tsh (tarray tuint 4) tlist t * data_at Tsh (tarray tuint 16) wlist w *
           data_at Tsh (tarray tuint 16) xs x *
           data_at Tsh (tarray tuint 16) ys y * CoreInSEP data (nonce, c, k) *
           data_at Tsh (tarray tuchar 64) OUT out)]). 
       subst Frame. reflexivity.
    subst Frame; clear FR. simpl. entailer. } 
  { constructor; constructor. (* TODO - is the existence of this subgoal linked to the failure of forward_call'??*) }
  after_call.  
  simpl; normalize. subst x0.  
  forward u.
  { entailer. rewrite HTgt. entailer. }  
  subst u.
  rewrite HTgt. 
  forward u.
  (*TODO: eliminate/investigate the need for the following weakening of the precondition*)
  apply semax_pre with (P':=
  (PROP  ()
   LOCAL 
   (temp _aux1
      (Vint
         (Int.xor ValTgt (Int.rol (Int.add ValS1 ValS2) (Int.repr Offset))));
   temp _i (Vint (Int.repr i)); temp _m (Vint (Int.repr 4));
   temp _j (Vint (Int.repr j)); lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(data_at Tsh (tarray tuint 4) tlist t);
   `(data_at Tsh (tarray tuint 16) wlist w);
   `(data_at Tsh (tarray tuint 16) xs x);
   `(data_at Tsh (tarray tuint 16) ys y); `(CoreInSEP data (nonce, c, k));
   `(data_at Tsh (tarray tuchar 64) OUT out)))). entailer.

  forward. entailer. 
Qed.

Lemma pattern2_noStmt Espec Source1 Source2 Target Offset: forall
  (S1Range: 0 <= Source1 < 4) (S2Range: 0 <= Source2 < 4) (TgtRange: 0 <= Target < 4)
  (HOffset: 0 < Int.unsigned (Int.repr Offset) < 32)
  ValS1 ValS2 ValTgt tlist
  (HS1: Znth Source1 tlist Vundef = Vint ValS1)
  (HS2: Znth Source2 tlist Vundef = Vint ValS2)
  (HTgt: Znth Target tlist Vundef = Vint ValTgt)
  data c ys wlist OUT i j t y x w out nonce k h xs,
@semax Espec (initialized_list [_i; _j; _m; _aux; _aux1; _aux'4]
     (func_tycontext f_core SalsaVarSpecs SalsaFunSpecs))
  (PROP  ()
   LOCAL  (temp _i (Vint (Int.repr i)); temp _m (Vint (Int.repr 4));
   temp _j (Vint (Int.repr j)); lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(data_at Tsh (tarray tuint 4) tlist t);
   `(data_at Tsh (tarray tuint 16) wlist w);
   `(data_at Tsh (tarray tuint 16) xs x); 
   `(data_at Tsh (tarray tuint 16) ys y);
   `(CoreInSEP data (nonce, c, k));
   `(data_at Tsh (tarray tuchar 64) OUT out)))
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
                 (Scall (Some _aux'5)
                    (Evar _L32
                       (Tfunction (Tcons tuint (Tcons tint Tnil)) tuint
                          cc_default))
                    [Etempvar _aux tuint; Econst_int (Int.repr Offset) tint])
                 (Sset _aux (Etempvar _aux'5 tuint)))
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
   SEP  (`(data_at Tsh (tarray tuint 4) 
        (upd_reptype_array tuint Target tlist
           (Vint
              (Int.xor ValTgt (Int.rol (Int.add ValS1 ValS2) (Int.repr Offset)))))
        t); 
   `(data_at Tsh (tarray tuint 16) wlist w);
   `(data_at Tsh (tarray tuint 16) xs x);
   `(data_at Tsh (tarray tuint 16) ys y);
   `(CoreInSEP data (nonce, c, k));
   `(data_at Tsh (tarray tuchar 64) OUT out)))).
Proof. intros.
  forward w1.  
  { entailer. rewrite HS1. entailer. }
  rewrite HS1. 
  forward w2. 
  { entailer. rewrite HS2. entailer. } 
  rewrite HS2.
  forward sum. subst sum.
Transparent core_spec. Transparent ld32_spec. Transparent L32_spec. Transparent st32_spec.
Transparent crypto_core_salsa20_spec. Transparent crypto_core_hsalsa20_spec.
  forward_call (Int.add ValS1 ValS2, Int.repr Offset). (*TODO: forward_call' fails*)
Opaque core_spec. Opaque ld32_spec. Opaque L32_spec. Opaque st32_spec.
Opaque crypto_core_salsa20_spec. Opaque crypto_core_hsalsa20_spec.
  { entailer.
    assert (FR: Frame = [`(data_at Tsh (tarray tuint 4) tlist t * data_at Tsh (tarray tuint 16) wlist w *
           data_at Tsh (tarray tuint 16) xs x *
           data_at Tsh (tarray tuint 16) ys y * CoreInSEP data (nonce, c, k) *
           data_at Tsh (tarray tuchar 64) OUT out)]). 
       subst Frame. reflexivity.
    subst Frame; clear FR. simpl. entailer. } 
  { constructor; constructor. (* TODO - is the existence of this subgoal linked to the failure of forward_call'??*) }
  after_call.  
  simpl; normalize. subst x0.  
  forward u.
  { entailer. rewrite HTgt. entailer. }  
  subst u.
  rewrite HTgt. 
  forward u.
  (*TODO: eliminate/investigate the need for the following weakening of the precondition*)
  apply semax_pre with (P':=
  (PROP  ()
   LOCAL 
   (temp _aux1
      (Vint
         (Int.xor ValTgt (Int.rol (Int.add ValS1 ValS2) (Int.repr Offset))));
   temp _i (Vint (Int.repr i)); temp _m (Vint (Int.repr 4));
   temp _j (Vint (Int.repr j)); lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(data_at Tsh (tarray tuint 4) tlist t);
   `(data_at Tsh (tarray tuint 16) wlist w);
   `(data_at Tsh (tarray tuint 16) xs x);
   `(data_at Tsh (tarray tuint 16) ys y); `(CoreInSEP data (nonce, c, k));
   `(data_at Tsh (tarray tuchar 64) OUT out)))). entailer. 

  forward. entailer. 
Qed.

Lemma pattern3_noStmt Espec Source1 Source2 Target Offset: forall
  (S1Range: 0 <= Source1 < 4) (S2Range: 0 <= Source2 < 4) (TgtRange: 0 <= Target < 4)
  (HOffset: 0 < Int.unsigned (Int.repr Offset) < 32)
  ValS1 ValS2 ValTgt tlist
  (HS1: Znth Source1 tlist Vundef = Vint ValS1)
  (HS2: Znth Source2 tlist Vundef = Vint ValS2)
  (HTgt: Znth Target tlist Vundef = Vint ValTgt)
  data c ys wlist OUT i j t y x w out nonce k h xs,
@semax Espec
  (initialized_list [_i; _j; _m; _aux; _aux1; _aux'5; _aux'4]
     (func_tycontext f_core SalsaVarSpecs SalsaFunSpecs))
  (PROP  ()
   LOCAL  (temp _i (Vint (Int.repr i)); temp _m (Vint (Int.repr 4));
   temp _j (Vint (Int.repr j)); lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(data_at Tsh (tarray tuint 4) tlist t);
   `(data_at Tsh (tarray tuint 16) wlist w);
   `(data_at Tsh (tarray tuint 16) xs x); 
   `(data_at Tsh (tarray tuint 16) ys y);
   `(CoreInSEP data (nonce, c, k));
   `(data_at Tsh (tarray tuchar 64) OUT out)))
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
                 (Scall (Some _aux'6)
                    (Evar _L32
                       (Tfunction (Tcons tuint (Tcons tint Tnil)) tuint
                          cc_default))
                    [Etempvar _aux tuint; Econst_int (Int.repr Offset) tint])
                 (Sset _aux (Etempvar _aux'6 tuint)))
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
   SEP  (`(data_at Tsh (tarray tuint 4) 
        (upd_reptype_array tuint Target tlist
           (Vint
              (Int.xor ValTgt (Int.rol (Int.add ValS1 ValS2) (Int.repr Offset)))))
        t); 
   `(data_at Tsh (tarray tuint 16) wlist w);
   `(data_at Tsh (tarray tuint 16) xs x);
   `(data_at Tsh (tarray tuint 16) ys y);
   `(CoreInSEP data (nonce, c, k));
   `(data_at Tsh (tarray tuchar 64) OUT out)))).
Proof. intros.
  forward w1.  
  { entailer. rewrite HS1. entailer. }
  rewrite HS1. 
  forward w2. 
  { entailer. rewrite HS2. entailer. } 
  rewrite HS2.
  forward sum. subst sum.
Transparent core_spec. Transparent ld32_spec. Transparent L32_spec. Transparent st32_spec.
Transparent crypto_core_salsa20_spec. Transparent crypto_core_hsalsa20_spec.
  forward_call (Int.add ValS1 ValS2, Int.repr Offset). (*TODO: forward_call' fails*)
Opaque core_spec. Opaque ld32_spec. Opaque L32_spec. Opaque st32_spec.
Opaque crypto_core_salsa20_spec. Opaque crypto_core_hsalsa20_spec.
  { entailer.
    assert (FR: Frame = [`(data_at Tsh (tarray tuint 4) tlist t * data_at Tsh (tarray tuint 16) wlist w *
           data_at Tsh (tarray tuint 16) xs x *
           data_at Tsh (tarray tuint 16) ys y * CoreInSEP data (nonce, c, k) *
           data_at Tsh (tarray tuchar 64) OUT out)]). 
       subst Frame. reflexivity.
    subst Frame; clear FR. simpl. entailer. } 
  { constructor; constructor. (* TODO - is the existence of this subgoal linked to the failure of forward_call'??*) }
  after_call.  
  simpl; normalize. subst x0.  
  forward u.
  { entailer. rewrite HTgt. entailer. }  
  subst u.
  rewrite HTgt. 
  forward u.
  (*TODO: eliminate/investigate the need for the following weakening of the precondition*)
  apply semax_pre with (P':=
  (PROP  ()
   LOCAL 
   (temp _aux1
      (Vint
         (Int.xor ValTgt (Int.rol (Int.add ValS1 ValS2) (Int.repr Offset))));
   temp _i (Vint (Int.repr i)); temp _m (Vint (Int.repr 4));
   temp _j (Vint (Int.repr j)); lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(data_at Tsh (tarray tuint 4) tlist t);
   `(data_at Tsh (tarray tuint 16) wlist w);
   `(data_at Tsh (tarray tuint 16) xs x);
   `(data_at Tsh (tarray tuint 16) ys y); `(CoreInSEP data (nonce, c, k));
   `(data_at Tsh (tarray tuchar 64) OUT out)))). entailer. 

  forward. entailer. 
Qed.
*)
Definition wlistJ' (wlist:list int) (j: Z) (t0 t1 t2 t3:int) (l: list int): Prop :=
  Zlength l = 16 /\ 
  l = upd_Znth_in_list (4 * j + (j + 3) mod 4)
       (upd_Znth_in_list (4 * j + (j + 2) mod 4)
         (upd_Znth_in_list (4 * j + (j + 1) mod 4)
          (upd_Znth_in_list (4 * j + (j + 0) mod 4) wlist t0)
          t1) t2) t3.

Fixpoint WLIST' (wlist tlist: list int) (j:Z) m l :=
  match m with 
    O => l=wlist
  | S m' => exists l' tm, 
            Zlength l = Zlength wlist /\
            WLIST' wlist tlist j m' l' /\
            Znth (Z.of_nat m') (map Vint tlist) Vundef = Vint tm /\
            l = upd_Znth_in_list (4*j+ ((j+Z.of_nat m') mod 4)) l' tm
  end.
Lemma WLIST'_length wlist tlist j : forall m l, WLIST' wlist tlist j m l -> Zlength l=Zlength wlist.
Proof. induction m; simpl; intros; subst; trivial.
  destruct H as [l' [tm [ L [W [ZZ LL]]]]]. subst. apply IHm in W; trivial.
Qed.
  
Lemma array_copy2 Espec:
forall i wlist data OUT j t y x w nonce out c k h ys (t0 t1 t2 t3:int) xs
       (J:0<=j<4)(WL: Zlength wlist=16),
@semax CompSpecs Espec
  (initialized_list [_i; _j; _m; _aux; _aux1; 184%positive; 183%positive; 182%positive; 181%positive]
     (func_tycontext f_core SalsaVarSpecs SalsaFunSpecs))
  (PROP  ()
   LOCAL  (temp _i (Vint (Int.repr i)); temp _m (Vint (Int.repr 4));
   temp _j (Vint (Int.repr j)); lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(data_at Tsh (tarray tuint 4) (map Vint [t0;t1;t2;t3]) t);
   `(data_at Tsh (tarray tuint 16) (map Vint wlist) w);
   `(data_at Tsh (tarray tuint 16) xs x);
   `(data_at Tsh (tarray tuint 16) ys y);
   `(CoreInSEP data (nonce, c, k));
   `(data_at Tsh (tarray tuchar 64) OUT out)))
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
   SEP  (`(data_at Tsh (tarray tuint 4) (map Vint [t0;t1;t2;t3]) t);
   `(EX W:_, !!(wlistJ' wlist j t0 t1 t2 t3 W) && data_at Tsh (tarray tuint 16) (map Vint W) w);
   `(data_at Tsh (tarray tuint 16) xs x);
   `(data_at Tsh (tarray tuint 16) ys y);
   `(CoreInSEP data (nonce, c, k));
   `(data_at Tsh (tarray tuchar 64) OUT out)))).
Proof. intros. abbreviate_semax.
(*first, delete old m*) drop_LOCAL 1%nat.
LENBforward_for_simple_bound 4 (EX m:Z, 
  (PROP  ()
   LOCAL  (temp _i (Vint (Int.repr i)); 
   temp _j (Vint (Int.repr j)); lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(data_at Tsh (tarray tuint 4) (map Vint [t0;t1;t2;t3]) t);
   `(EX l:_, !!WLIST' wlist [t0;t1;t2;t3] j (Z.to_nat m) l && data_at Tsh (tarray tuint 16) (map Vint l) w);
   `(data_at Tsh (tarray tuint 16) xs x);
   `(data_at Tsh (tarray tuint 16) ys y);
   `(CoreInSEP data (nonce, c, k));
   `(data_at Tsh (tarray tuchar 64) OUT out)))).
{ entailer. apply (exp_right wlist). entailer. }
{ rename H into M; rename i0 into m. 
  normalize. intros wlist1. normalize. rename H into WLIST1.
  assert (TM: exists tm, Znth m [Vint t0; Vint t1; Vint t2; Vint t3] Vundef = Vint tm).
    destruct (zeq m 0); subst; simpl. eexists; reflexivity. 
    destruct (zeq m 1); subst; simpl. eexists; reflexivity. 
    destruct (zeq m 2); subst; simpl. eexists; reflexivity. 
    destruct (zeq m 3); subst; simpl. eexists; reflexivity. omega.
  destruct TM as [tm TM].
  forward. entailer. rewrite TM. apply prop_right; simpl; trivial.
  assert (NEQ: (Int.eq (Int.repr (j + m)) (Int.repr Int.min_signed) &&
                 Int.eq (Int.repr 4) Int.mone)%bool = false).
    rewrite (Int.eq_false (Int.repr 4)), andb_false_r. simpl; trivial.
    unfold Int.mone. intros N.  
    assert (SGN: Int.signed (Int.repr 4) = Int.signed (Int.repr (-1))).
      rewrite N; trivial.
    rewrite Int.signed_repr, Int.signed_repr in SGN. omega.
    rewrite client_lemmas.int_min_signed_eq, client_lemmas.int_max_signed_eq; omega.
    rewrite client_lemmas.int_min_signed_eq, client_lemmas.int_max_signed_eq; omega.
  rewrite TM.
  forward. entailer. rewrite NEQ. apply prop_right; simpl; trivial.
  unfold force_val, sem_mod, both_int; simpl.
              unfold sem_cast_neutral, both_int; simpl.
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
  rewrite A.
(*  assert (A: 4 * j + Int.unsigned (Int.mods (Int.repr (j + m)) (Int.repr 4)) = 4 * j + (j + m) mod 4).
             unfold Int.mods.
             rewrite Int.signed_repr.  
             2: rewrite client_lemmas.int_min_signed_eq, client_lemmas.int_max_signed_eq; omega.  
             rewrite Int.signed_repr.  
             2: rewrite client_lemmas.int_min_signed_eq, client_lemmas.int_max_signed_eq; omega.  
             rewrite Int.unsigned_repr. rewrite Z.rem_mod_nonneg. trivial. omega. omega. 
             rewrite int_max_unsigned_eq; omega.*)
Opaque Z.mul. Opaque Z.add. 
  forward. { apply prop_right.
             assert (0<= (j + m) mod 4 < 4). apply Z_mod_lt; omega.
             omega. }
  entailer. apply (exp_right (upd_Znth_in_list (4 * j + (j + m) mod 4) wlist1 _id0)). 
  entailer. (*
  clear H1 H2 H3 H4 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20.
  assert (L1: length wlist1 = 16%nat) by (erewrite (WLIST'_length _ _ _ _ _ WLIST1); trivial).*)
  assert (AP: 0 <= (j + m) mod 4 < 4) by (apply Z_mod_lt; omega).
  apply andp_right. apply prop_right.
    rewrite Z.add_comm. rewrite Z2Nat.inj_add; try omega.
    assert (SS: (Z.to_nat 1 + Z.to_nat m)%nat = S (Z.to_nat m)) by reflexivity.
    rewrite SS; simpl.
    exists wlist1, _id0.
    assert (WL1: Zlength wlist1 = 16). erewrite WLIST'_length. 2: eassumption. assumption.
    split. rewrite upd_Znth_in_list_Zlength. eapply WLIST'_length; eassumption.
           rewrite WL1. omega.
           split. trivial.  
           rewrite Z2Nat.id. split; trivial. omega.
  cancel.
  rewrite upd_Znth_in_list_map. cancel. }
entailer. apply (exp_right l). entailer.
apply prop_right.
split. rewrite Zlength_map in H20. assumption.
Transparent plus. 
destruct H18 as [l1 [tm1 [ZL1 [XX1 [Z3 HL1]]]]].
destruct XX1 as [l2 [tm2 [ZL2 [XX2 [Z2 HL2]]]]].
destruct XX2 as [l3 [tm3 [ZL3 [XX3 [Z1 HL3]]]]].
destruct XX3 as [l4 [tm4 [ZL4 [XX4 [Z0 HL4]]]]].
assert (T0: Znth 0 [Vint t0; Vint t1; Vint t2; Vint t3] Vundef = Vint t0) by reflexivity.
assert (T1: Znth 1 [Vint t0; Vint t1; Vint t2; Vint t3] Vundef = Vint t1) by reflexivity.
assert (T2: Znth 2 [Vint t0; Vint t1; Vint t2; Vint t3] Vundef = Vint t2) by reflexivity.
assert (T3: Znth 3 [Vint t0; Vint t1; Vint t2; Vint t3] Vundef = Vint t3) by reflexivity.
simpl in *.
rewrite T0 in Z0; inv Z0.
rewrite T1 in Z1; inv Z1.
rewrite T2 in Z2; inv Z2.
rewrite T3 in Z3; inv Z3. trivial.
Opaque plus.
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
(*
Lemma pattern4_noStmt Espec Source1 Source2 Target Offset: forall
  (S1Range: 0 <= Source1 < 4) (S2Range: 0 <= Source2 < 4) (TgtRange: 0 <= Target < 4)
  (HOffset: 0 < Int.unsigned (Int.repr Offset) < 32)
  ValS1 ValS2 ValTgt tlist
  (HS1: Znth Source1 tlist Vundef = Vint ValS1)
  (HS2: Znth Source2 tlist Vundef = Vint ValS2)
  (HTgt: Znth Target tlist Vundef = Vint ValTgt)
  data c ys wlist OUT i j t y x w out nonce k h xs,
@semax Espec
  (initialized_list [_i; _j; _m; _aux; _aux1; _aux'6; _aux'5; _aux'4]
     (func_tycontext f_core SalsaVarSpecs SalsaFunSpecs))
  (PROP  ()
   LOCAL  (temp _i (Vint (Int.repr i)); temp _m (Vint (Int.repr 4));
   temp _j (Vint (Int.repr j)); lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(data_at Tsh (tarray tuint 4) tlist t);
   `(data_at Tsh (tarray tuint 16) wlist w);
   `(data_at Tsh (tarray tuint 16) xs x); 
   `(data_at Tsh (tarray tuint 16) ys y);
   `(CoreInSEP data (nonce, c, k));
   `(data_at Tsh (tarray tuchar 64) OUT out)))
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
                 (Scall (Some _aux'7)
                    (Evar _L32
                       (Tfunction (Tcons tuint (Tcons tint Tnil)) tuint
                          cc_default))
                    [Etempvar _aux tuint; Econst_int (Int.repr Offset) tint])
                 (Sset _aux (Etempvar _aux'7 tuint)))
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
   SEP  (`(data_at Tsh (tarray tuint 4) 
        (upd_reptype_array tuint Target tlist
           (Vint
              (Int.xor ValTgt (Int.rol (Int.add ValS1 ValS2) (Int.repr Offset)))))
        t); 
   `(data_at Tsh (tarray tuint 16) wlist w);
   `(data_at Tsh (tarray tuint 16) xs x);
   `(data_at Tsh (tarray tuint 16) ys y);
   `(CoreInSEP data (nonce, c, k));
   `(data_at Tsh (tarray tuchar 64) OUT out)))).
Proof. intros.
  forward w1.  
  { entailer. rewrite HS1. entailer. }
  rewrite HS1. 
  forward w2. 
  { entailer. rewrite HS2. entailer. } 
  rewrite HS2.
  forward sum. subst sum.
Transparent core_spec. Transparent ld32_spec. Transparent L32_spec. Transparent st32_spec.
Transparent crypto_core_salsa20_spec. Transparent crypto_core_hsalsa20_spec.
  forward_call (Int.add ValS1 ValS2, Int.repr Offset). (*TODO: forward_call' fails*)
Opaque core_spec. Opaque ld32_spec. Opaque L32_spec. Opaque st32_spec.
Opaque crypto_core_salsa20_spec. Opaque crypto_core_hsalsa20_spec.
  { entailer.
    assert (FR: Frame = [`(data_at Tsh (tarray tuint 4) tlist t * data_at Tsh (tarray tuint 16) wlist w *
           data_at Tsh (tarray tuint 16) xs x *
           data_at Tsh (tarray tuint 16) ys y * CoreInSEP data (nonce, c, k) *
           data_at Tsh (tarray tuchar 64) OUT out)]). 
       subst Frame. reflexivity.
    subst Frame; clear FR. simpl. entailer. } 
  { constructor; constructor. (* TODO - is the existence of this subgoal linked to the failure of forward_call'??*) }
  after_call.  
  simpl; normalize. subst x0.  
  forward u.
  { entailer. rewrite HTgt. entailer. }  
  subst u.
  rewrite HTgt. 
  forward u.
  (*TODO: eliminate/investigate the need for the following weakening of the precondition*)
  apply semax_pre with (P':=
  (PROP  ()
   LOCAL 
   (temp _aux1
      (Vint
         (Int.xor ValTgt (Int.rol (Int.add ValS1 ValS2) (Int.repr Offset))));
   temp _i (Vint (Int.repr i)); temp _m (Vint (Int.repr 4));
   temp _j (Vint (Int.repr j)); lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(data_at Tsh (tarray tuint 4) tlist t);
   `(data_at Tsh (tarray tuint 16) wlist w);
   `(data_at Tsh (tarray tuint 16) xs x);
   `(data_at Tsh (tarray tuint 16) ys y); `(CoreInSEP data (nonce, c, k));
   `(data_at Tsh (tarray tuchar 64) OUT out)))). entailer. 

  forward. entailer. 
Qed.
*)

Lemma pattern2_noStmt Espec Source1 Source2 Target Offset: forall
  (S1Range: 0 <= Source1 < 4) (S2Range: 0 <= Source2 < 4) (TgtRange: 0 <= Target < 4)
  (HOffset: 0 < Int.unsigned (Int.repr Offset) < 32)
  ValS1 ValS2 ValTgt tlist
  (HS1: Znth Source1 tlist Vundef = Vint ValS1)
  (HS2: Znth Source2 tlist Vundef = Vint ValS2)
  (HTgt: Znth Target tlist Vundef = Vint ValTgt)
  data c ys wlist OUT i j t y x w out nonce k h xs,
@semax CompSpecs Espec (initialized_list [_i; _j; _m; _aux; _aux1; 181%positive]
     (func_tycontext f_core SalsaVarSpecs SalsaFunSpecs))
  (PROP  ()
   LOCAL  (temp _i (Vint (Int.repr i)); temp _m (Vint (Int.repr 4));
   temp _j (Vint (Int.repr j)); lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(data_at Tsh (tarray tuint 4) tlist t);
   `(data_at Tsh (tarray tuint 16) wlist w);
   `(data_at Tsh (tarray tuint 16) xs x); 
   `(data_at Tsh (tarray tuint 16) ys y);
   `(CoreInSEP data (nonce, c, k));
   `(data_at Tsh (tarray tuchar 64) OUT out)))
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
                 (Scall (Some 182%positive)
                    (Evar _L32
                       (Tfunction (Tcons tuint (Tcons tint Tnil)) tuint
                          cc_default))
                    [Etempvar _aux tuint; Econst_int (Int.repr Offset) tint])
                 (Sset _aux (Etempvar 182%positive tuint)))
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
   SEP  (`(data_at Tsh (tarray tuint 4) 
        (upd_Znth_in_list Target tlist
           (Vint
              (Int.xor ValTgt (Int.rol (Int.add ValS1 ValS2) (Int.repr Offset)))))
        t); 
   `(data_at Tsh (tarray tuint 16) wlist w);
   `(data_at Tsh (tarray tuint 16) xs x);
   `(data_at Tsh (tarray tuint 16) ys y);
   `(CoreInSEP data (nonce, c, k));
   `(data_at Tsh (tarray tuchar 64) OUT out)))).
Proof. intros. abbreviate_semax.
  forward v1.  
  { entailer. rewrite HS1. apply prop_right; simpl; trivial. }
  rewrite HS1. 
  forward v2. 
  { entailer. rewrite HS2. apply prop_right; simpl; trivial. } 
  rewrite HS2.
  forward sum.
Transparent core_spec. Transparent ld32_spec. Transparent L32_spec. Transparent st32_spec.
Transparent crypto_core_salsa20_spec. Transparent crypto_core_hsalsa20_spec.
  forward_call (Int.add ValS1 ValS2, Int.repr Offset) v.
Opaque core_spec. Opaque ld32_spec. Opaque L32_spec. Opaque st32_spec.
Opaque crypto_core_salsa20_spec. Opaque crypto_core_hsalsa20_spec.
  { instantiate (1:= [lvar _t (tarray tuint 4) t;
       lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
       lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
       temp _k k; temp _h (Vint (Int.repr h))]). admit. } admit. (*VST Issue: the usual delete_temps / LOCALS issue*)
(*  { entailer.
    assert (FR: Frame = [`(data_at Tsh (tarray tuint 4) tlist t * data_at Tsh (tarray tuint 16) wlist w *
           data_at Tsh (tarray tuint 16) xs x *
           data_at Tsh (tarray tuint 16) ys y * CoreInSEP data (nonce, c, k) *
           data_at Tsh (tarray tuchar 64) OUT out)]). 
       subst Frame. reflexivity.
    subst Frame; clear FR. simpl. entailer. } 
  { constructor; constructor. (* TODO - is the existence of this subgoal linked to the failure of forward_call'??*) }
  after_call.  
  simpl; normalize. subst x0.  *) subst v.
  forward u.
  { entailer. rewrite HTgt. apply prop_right; simpl; trivial. }  
  subst u.
  rewrite HTgt. 
  forward u.
  forward. entailer.
Qed.

Lemma pattern3_noStmt Espec Source1 Source2 Target Offset: forall
  (S1Range: 0 <= Source1 < 4) (S2Range: 0 <= Source2 < 4) (TgtRange: 0 <= Target < 4)
  (HOffset: 0 < Int.unsigned (Int.repr Offset) < 32)
  ValS1 ValS2 ValTgt tlist
  (HS1: Znth Source1 tlist Vundef = Vint ValS1)
  (HS2: Znth Source2 tlist Vundef = Vint ValS2)
  (HTgt: Znth Target tlist Vundef = Vint ValTgt)
  data c ys wlist OUT i j t y x w out nonce k h xs,
@semax CompSpecs Espec (initialized_list [_i; _j; _m; _aux; _aux1; 182%positive; 181%positive]
     (func_tycontext f_core SalsaVarSpecs SalsaFunSpecs))
  (PROP  ()
   LOCAL  (temp _i (Vint (Int.repr i)); temp _m (Vint (Int.repr 4));
   temp _j (Vint (Int.repr j)); lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(data_at Tsh (tarray tuint 4) tlist t);
   `(data_at Tsh (tarray tuint 16) wlist w);
   `(data_at Tsh (tarray tuint 16) xs x); 
   `(data_at Tsh (tarray tuint 16) ys y);
   `(CoreInSEP data (nonce, c, k));
   `(data_at Tsh (tarray tuchar 64) OUT out)))
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
   SEP  (`(data_at Tsh (tarray tuint 4) 
        (upd_Znth_in_list Target tlist
           (Vint
              (Int.xor ValTgt (Int.rol (Int.add ValS1 ValS2) (Int.repr Offset)))))
        t); 
   `(data_at Tsh (tarray tuint 16) wlist w);
   `(data_at Tsh (tarray tuint 16) xs x);
   `(data_at Tsh (tarray tuint 16) ys y);
   `(CoreInSEP data (nonce, c, k));
   `(data_at Tsh (tarray tuchar 64) OUT out)))).
Proof. intros. abbreviate_semax.
  forward v1.  
  { entailer. rewrite HS1. apply prop_right; simpl; trivial. }
  rewrite HS1. 
  forward v2. 
  { entailer. rewrite HS2. apply prop_right; simpl; trivial. } 
  rewrite HS2.
  forward sum.
Transparent core_spec. Transparent ld32_spec. Transparent L32_spec. Transparent st32_spec.
Transparent crypto_core_salsa20_spec. Transparent crypto_core_hsalsa20_spec.
  forward_call (Int.add ValS1 ValS2, Int.repr Offset) v.
Opaque core_spec. Opaque ld32_spec. Opaque L32_spec. Opaque st32_spec.
Opaque crypto_core_salsa20_spec. Opaque crypto_core_hsalsa20_spec.
  { instantiate (1:= [lvar _t (tarray tuint 4) t;
       lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
       lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
       temp _k k; temp _h (Vint (Int.repr h))]). admit. } admit. (*VST Issue: the usual delete_temps / LOCALS issue*)
(*  { entailer.
    assert (FR: Frame = [`(data_at Tsh (tarray tuint 4) tlist t * data_at Tsh (tarray tuint 16) wlist w *
           data_at Tsh (tarray tuint 16) xs x *
           data_at Tsh (tarray tuint 16) ys y * CoreInSEP data (nonce, c, k) *
           data_at Tsh (tarray tuchar 64) OUT out)]). 
       subst Frame. reflexivity.
    subst Frame; clear FR. simpl. entailer. } 
  { constructor; constructor. (* TODO - is the existence of this subgoal linked to the failure of forward_call'??*) }
  after_call.  
  simpl; normalize. subst x0.  *) subst v.
  forward u.
  { entailer. rewrite HTgt. apply prop_right; simpl; trivial. }  
  subst u.
  rewrite HTgt. 
  forward u.
  forward. entailer.
Qed.

Lemma pattern4_noStmt Espec Source1 Source2 Target Offset: forall
  (S1Range: 0 <= Source1 < 4) (S2Range: 0 <= Source2 < 4) (TgtRange: 0 <= Target < 4)
  (HOffset: 0 < Int.unsigned (Int.repr Offset) < 32)
  ValS1 ValS2 ValTgt tlist
  (HS1: Znth Source1 tlist Vundef = Vint ValS1)
  (HS2: Znth Source2 tlist Vundef = Vint ValS2)
  (HTgt: Znth Target tlist Vundef = Vint ValTgt)
  data c ys wlist OUT i j t y x w out nonce k h xs,
@semax CompSpecs Espec (initialized_list [_i; _j; _m; _aux; _aux1; 183%positive; 182%positive; 181%positive]
     (func_tycontext f_core SalsaVarSpecs SalsaFunSpecs))
  (PROP  ()
   LOCAL  (temp _i (Vint (Int.repr i)); temp _m (Vint (Int.repr 4));
   temp _j (Vint (Int.repr j)); lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(data_at Tsh (tarray tuint 4) tlist t);
   `(data_at Tsh (tarray tuint 16) wlist w);
   `(data_at Tsh (tarray tuint 16) xs x); 
   `(data_at Tsh (tarray tuint 16) ys y);
   `(CoreInSEP data (nonce, c, k));
   `(data_at Tsh (tarray tuchar 64) OUT out)))
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
   SEP  (`(data_at Tsh (tarray tuint 4) 
        (upd_Znth_in_list Target tlist
           (Vint
              (Int.xor ValTgt (Int.rol (Int.add ValS1 ValS2) (Int.repr Offset)))))
        t); 
   `(data_at Tsh (tarray tuint 16) wlist w);
   `(data_at Tsh (tarray tuint 16) xs x);
   `(data_at Tsh (tarray tuint 16) ys y);
   `(CoreInSEP data (nonce, c, k));
   `(data_at Tsh (tarray tuchar 64) OUT out)))).
Proof. intros. abbreviate_semax.
  forward v1.  
  { entailer. rewrite HS1. apply prop_right; simpl; trivial. }
  rewrite HS1. 
  forward v2. 
  { entailer. rewrite HS2. apply prop_right; simpl; trivial. } 
  rewrite HS2.
  forward sum.
Transparent core_spec. Transparent ld32_spec. Transparent L32_spec. Transparent st32_spec.
Transparent crypto_core_salsa20_spec. Transparent crypto_core_hsalsa20_spec.
  forward_call (Int.add ValS1 ValS2, Int.repr Offset) v.
Opaque core_spec. Opaque ld32_spec. Opaque L32_spec. Opaque st32_spec.
Opaque crypto_core_salsa20_spec. Opaque crypto_core_hsalsa20_spec.
  { instantiate (1:= [lvar _t (tarray tuint 4) t;
       lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
       lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
       temp _k k; temp _h (Vint (Int.repr h))]). admit. } admit. (*VST Issue: the usual delete_temps / LOCALS issue*)
(*  { entailer.
    assert (FR: Frame = [`(data_at Tsh (tarray tuint 4) tlist t * data_at Tsh (tarray tuint 16) wlist w *
           data_at Tsh (tarray tuint 16) xs x *
           data_at Tsh (tarray tuint 16) ys y * CoreInSEP data (nonce, c, k) *
           data_at Tsh (tarray tuchar 64) OUT out)]). 
       subst Frame. reflexivity.
    subst Frame; clear FR. simpl. entailer. } 
  { constructor; constructor. (* TODO - is the existence of this subgoal linked to the failure of forward_call'??*) }
  after_call.  
  simpl; normalize. subst x0.  *) subst v.
  forward u.
  { entailer. rewrite HTgt. apply prop_right; simpl; trivial. }  
  subst u.
  rewrite HTgt. 
  forward u.
  forward. entailer.
Qed.

Lemma Jbody (Espec : OracleKind): forall 
c k h nonce out w x y t ys i j OUT
(data : SixteenByte * SixteenByte * (SixteenByte * SixteenByte))
(*(OUTlen : length OUT = 64%nat)*)
(out' : name _out)
(in' : name _in)
(k' : name _k)
(c' : name _c)
(h' : name _h)
(aux' : name _aux)
xs
(I : 0 <= i < 20)
(J : 0 <= j < 4)
(XZL: Zlength xs = 16)
wlist (WL: Zlength wlist = 16)
t0 t1 t2 t3
(T0: Znth ((5*j+4*0) mod 16) (map Vint xs) Vundef = Vint t0)
(T0: Znth ((5*j+4*1) mod 16) (map Vint  xs) Vundef = Vint t1)
(T0: Znth ((5*j+4*2) mod 16) (map Vint xs) Vundef = Vint t2)
(T0: Znth ((5*j+4*3) mod 16) (map Vint xs) Vundef = Vint t3),
@semax CompSpecs Espec
  (initialized_list [_i; _j]
     (func_tycontext f_core SalsaVarSpecs SalsaFunSpecs))
  (PROP  ()
   LOCAL  (temp _j (Vint (Int.repr j)); temp _i (Vint (Int.repr i));
   lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
   lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w; temp _in nonce;
   temp _out out; temp _c c; temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(data_at Tsh (tarray tuint 16) (map Vint wlist) w);
   `(data_at Tsh (tarray tuint 16) (map Vint xs) x);
   `(data_at Tsh (tarray tuint 16) ys y);
   `(data_at_ Tsh (tarray tuint 4) t); `(CoreInSEP data (nonce, c, k));
   `(data_at Tsh (tarray tuchar 64) OUT out)))
                    (Ssequence
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
                      (Ssequence
                        (Ssequence
                          (Sset _aux
                            (Ederef
                              (Ebinop Oadd (Evar _t (tarray tuint 4))
                                (Econst_int (Int.repr 0) tint) (tptr tuint))
                              tuint))
                          (Ssequence
                            (Sset _aux1
                              (Ederef
                                (Ebinop Oadd (Evar _t (tarray tuint 4))
                                  (Econst_int (Int.repr 3) tint)
                                  (tptr tuint)) tuint))
                            (Ssequence
                              (Sset _aux
                                (Ebinop Oadd (Etempvar _aux tuint)
                                  (Etempvar _aux1 tuint) tuint))
                              (Ssequence
                                (Ssequence
                                  (Scall (Some 181%positive)
                                    (Evar _L32 (Tfunction
                                                 (Tcons tuint
                                                   (Tcons tint Tnil)) tuint
                                                 cc_default))
                                    ((Etempvar _aux tuint) ::
                                     (Econst_int (Int.repr 7) tint) :: nil))
                                  (Sset _aux (Etempvar 181%positive tuint)))
                                (Ssequence
                                  (Sset _aux1
                                    (Ederef
                                      (Ebinop Oadd (Evar _t (tarray tuint 4))
                                        (Econst_int (Int.repr 1) tint)
                                        (tptr tuint)) tuint))
                                  (Ssequence
                                    (Sset _aux1
                                      (Ebinop Oxor (Etempvar _aux1 tuint)
                                        (Etempvar _aux tuint) tuint))
                                    (Sassign
                                      (Ederef
                                        (Ebinop Oadd
                                          (Evar _t (tarray tuint 4))
                                          (Econst_int (Int.repr 1) tint)
                                          (tptr tuint)) tuint)
                                      (Etempvar _aux1 tuint))))))))
                        (Ssequence
                          (Ssequence
                            (Sset _aux
                              (Ederef
                                (Ebinop Oadd (Evar _t (tarray tuint 4))
                                  (Econst_int (Int.repr 1) tint)
                                  (tptr tuint)) tuint))
                            (Ssequence
                              (Sset _aux1
                                (Ederef
                                  (Ebinop Oadd (Evar _t (tarray tuint 4))
                                    (Econst_int (Int.repr 0) tint)
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
                                       (Econst_int (Int.repr 9) tint) :: nil))
                                    (Sset _aux (Etempvar 182%positive tuint)))
                                  (Ssequence
                                    (Sset _aux1
                                      (Ederef
                                        (Ebinop Oadd
                                          (Evar _t (tarray tuint 4))
                                          (Econst_int (Int.repr 2) tint)
                                          (tptr tuint)) tuint))
                                    (Ssequence
                                      (Sset _aux1
                                        (Ebinop Oxor (Etempvar _aux1 tuint)
                                          (Etempvar _aux tuint) tuint))
                                      (Sassign
                                        (Ederef
                                          (Ebinop Oadd
                                            (Evar _t (tarray tuint 4))
                                            (Econst_int (Int.repr 2) tint)
                                            (tptr tuint)) tuint)
                                        (Etempvar _aux1 tuint))))))))
                          (Ssequence
                            (Ssequence
                              (Sset _aux
                                (Ederef
                                  (Ebinop Oadd (Evar _t (tarray tuint 4))
                                    (Econst_int (Int.repr 2) tint)
                                    (tptr tuint)) tuint))
                              (Ssequence
                                (Sset _aux1
                                  (Ederef
                                    (Ebinop Oadd (Evar _t (tarray tuint 4))
                                      (Econst_int (Int.repr 1) tint)
                                      (tptr tuint)) tuint))
                                (Ssequence
                                  (Sset _aux
                                    (Ebinop Oadd (Etempvar _aux tuint)
                                      (Etempvar _aux1 tuint) tuint))
                                  (Ssequence
                                    (Ssequence
                                      (Scall (Some 183%positive)
                                        (Evar _L32 (Tfunction
                                                     (Tcons tuint
                                                       (Tcons tint Tnil))
                                                     tuint cc_default))
                                        ((Etempvar _aux tuint) ::
                                         (Econst_int (Int.repr 13) tint) ::
                                         nil))
                                      (Sset _aux
                                        (Etempvar 183%positive tuint)))
                                    (Ssequence
                                      (Sset _aux1
                                        (Ederef
                                          (Ebinop Oadd
                                            (Evar _t (tarray tuint 4))
                                            (Econst_int (Int.repr 3) tint)
                                            (tptr tuint)) tuint))
                                      (Ssequence
                                        (Sset _aux1
                                          (Ebinop Oxor (Etempvar _aux1 tuint)
                                            (Etempvar _aux tuint) tuint))
                                        (Sassign
                                          (Ederef
                                            (Ebinop Oadd
                                              (Evar _t (tarray tuint 4))
                                              (Econst_int (Int.repr 3) tint)
                                              (tptr tuint)) tuint)
                                          (Etempvar _aux1 tuint))))))))
                            (Ssequence
                              (Ssequence
                                (Sset _aux
                                  (Ederef
                                    (Ebinop Oadd (Evar _t (tarray tuint 4))
                                      (Econst_int (Int.repr 3) tint)
                                      (tptr tuint)) tuint))
                                (Ssequence
                                  (Sset _aux1
                                    (Ederef
                                      (Ebinop Oadd (Evar _t (tarray tuint 4))
                                        (Econst_int (Int.repr 2) tint)
                                        (tptr tuint)) tuint))
                                  (Ssequence
                                    (Sset _aux
                                      (Ebinop Oadd (Etempvar _aux tuint)
                                        (Etempvar _aux1 tuint) tuint))
                                    (Ssequence
                                      (Ssequence
                                        (Scall (Some 184%positive)
                                          (Evar _L32 (Tfunction
                                                       (Tcons tuint
                                                         (Tcons tint Tnil))
                                                       tuint cc_default))
                                          ((Etempvar _aux tuint) ::
                                           (Econst_int (Int.repr 18) tint) ::
                                           nil))
                                        (Sset _aux
                                          (Etempvar 184%positive tuint)))
                                      (Ssequence
                                        (Sset _aux1
                                          (Ederef
                                            (Ebinop Oadd
                                              (Evar _t (tarray tuint 4))
                                              (Econst_int (Int.repr 0) tint)
                                              (tptr tuint)) tuint))
                                        (Ssequence
                                          (Sset _aux1
                                            (Ebinop Oxor
                                              (Etempvar _aux1 tuint)
                                              (Etempvar _aux tuint) tuint))
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Evar _t (tarray tuint 4))
                                                (Econst_int (Int.repr 0) tint)
                                                (tptr tuint)) tuint)
                                            (Etempvar _aux1 tuint))))))))
                              (Ssequence
                                (Sset _m (Econst_int (Int.repr 0) tint))
                                (Sloop
                                  (Ssequence
                                    (Sifthenelse (Ebinop Olt
                                                   (Etempvar _m tint)
                                                   (Econst_int (Int.repr 4) tint)
                                                   tint)
                                      Sskip
                                      Sbreak)
                                    (Ssequence
                                      (Sset _aux
                                        (Ederef
                                          (Ebinop Oadd
                                            (Evar _t (tarray tuint 4))
                                            (Etempvar _m tint) (tptr tuint))
                                          tuint))
                                      (Ssequence
                                        (Sset _aux1
                                          (Ebinop Oadd
                                            (Ebinop Omul
                                              (Econst_int (Int.repr 4) tint)
                                              (Etempvar _j tint) tint)
                                            (Ebinop Omod
                                              (Ebinop Oadd (Etempvar _j tint)
                                                (Etempvar _m tint) tint)
                                              (Econst_int (Int.repr 4) tint)
                                              tint) tint))
                                        (Sassign
                                          (Ederef
                                            (Ebinop Oadd
                                              (Evar _w (tarray tuint 16))
                                              (Etempvar _aux1 tuint)
                                              (tptr tuint)) tuint)
                                          (Etempvar _aux tuint)))))
                                  (Sset _m
                                    (Ebinop Oadd (Etempvar _m tint)
                                      (Econst_int (Int.repr 1) tint) tint)))))))))
  (normal_ret_assert
     (PROP  (0 <= j + 1 <= 4)
      LOCAL  (temp _j (Vint (Int.repr j)); temp _i (Vint (Int.repr i));
      lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
      lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w;
      temp _in nonce; temp _out out; temp _c c; temp _k k;
      temp _h (Vint (Int.repr h)))
      SEP  (`(data_at Tsh (tarray tuint 16) ys y);
      `(data_at Tsh (tarray tuint 16) (map Vint xs) x);
      `(data_at_ Tsh (tarray tuint 4) t);
      `(EX W:_, 
             !!(match Wcopyspec t0 t1 t2 t3 with
                 (s0,s1,s2,s3) => wlistJ' wlist j s0 s1 s2 s3 W
                end) 
             && data_at Tsh (tarray tuint 16) (map Vint W) w);
      `(CoreInSEP data (nonce, c, k));
      `(data_at Tsh (tarray tuchar 64) OUT out)))).
Proof. intros. abbreviate_semax.
  forward_seq. apply array_copy1I; trivial.

  normalize. intros tlist. normalize. rename H into HT.
  assert_PROP (Zlength tlist = 4). entailer. rename H into TL.

  rewrite <- HT in T0; try omega.
  rewrite <- HT in T1; try omega.
  rewrite <- HT in T2; try omega.
  rewrite <- HT in T3; try omega.

  forward_seq.
    eapply (pattern1_noStmt _ 0 3 1 7); try omega; try eassumption.
          rewrite Int.unsigned_repr. omega. rewrite int_max_unsigned_eq; omega.
    remember (Int.xor t1 (Int.rol (Int.add t0 t3) (Int.repr 7))) as tt0.
    remember (upd_Znth_in_list 1 tlist (Vint tt0)) as tlist1.
    assert(ZNTH1_1: Znth 1 tlist1 Vundef = Vint tt0).
      subst tlist1; apply upd_Znth_same. omega.
    assert(ZNTH1_0: Znth 0 tlist1 Vundef = Vint t0).
      subst tlist1; rewrite upd_Znth_diff; trivial; omega.
    assert(ZNTH1_2: Znth 2 tlist1 Vundef = Vint t2).
      subst tlist1; rewrite upd_Znth_diff; trivial; omega.
    assert(ZNTH1_3: Znth 3 tlist1 Vundef = Vint t3).
      subst tlist1; rewrite upd_Znth_diff; trivial; omega.
  assert (LT1: Zlength tlist1 = 4).
    subst tlist1. rewrite upd_Znth_in_list_Zlength. apply TL. omega.
 
  (*VST Issue: mkConciseDelta SalsaVarSpecs SalsaFunSpecs f_core Delta. doesn't wotk any longer*)
  forward_seq. 

    (*VST Issue we'd maybe like to use a variant of pattern2_noStmt that doesn't mention the
      dead variables aux, aux1, 181%positive in Delta, using subcontext:
    eapply semax_extensionality_Delta.
    2: eapply (pattern2_noStmt _ 1 0 2 9); try omega; try eassumption.
     but where are the tactics to discharge this subcontext-side-condition?*)

    eapply (pattern2_noStmt _ 1 0 2 9); try omega; try eassumption.
          rewrite Int.unsigned_repr. omega. rewrite int_max_unsigned_eq; omega.
    remember (Int.xor t2 (Int.rol (Int.add tt0 t0) (Int.repr 9))) as tt1.

  remember (upd_Znth_in_list 2 tlist1 (Vint tt1)) as tlist2.
    assert(ZNTH2_1: Znth 1 tlist2 Vundef = Vint tt0).
      subst tlist2. rewrite upd_Znth_diff; trivial; omega.
    assert(ZNTH2_0: Znth 0 tlist2 Vundef = Vint t0).
      subst tlist2; rewrite upd_Znth_diff; trivial; omega.
    assert(ZNTH2_2: Znth 2 tlist2 Vundef = Vint tt1). 
      subst tlist2; rewrite upd_Znth_same; trivial; omega.
    assert(ZNTH2_3: Znth 3 tlist2 Vundef = Vint t3).
      subst tlist2; rewrite upd_Znth_diff; trivial; omega.
  assert (LT2: Zlength tlist2 = 4).
    subst tlist2. rewrite upd_Znth_in_list_Zlength; trivial. omega.

  forward_seq. 
  eapply (pattern3_noStmt _ 2 1 3 13); try omega; try eassumption.
          rewrite Int.unsigned_repr. omega. rewrite int_max_unsigned_eq; omega.
  remember (Int.xor t3 (Int.rol (Int.add tt1 tt0) (Int.repr 13))) as tt2.  
  remember (upd_Znth_in_list 3 tlist2 (Vint tt2)) as tlist3.
  assert (LT3:  Zlength tlist3 = 4).
    subst tlist3. rewrite upd_Znth_in_list_Zlength; trivial. omega.

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
  remember (upd_Znth_in_list 0 tlist3 (Vint tt3)) as tlist4.
  assert (LT4:  Zlength tlist4 = 4).
    subst tlist4. rewrite upd_Znth_in_list_Zlength; trivial. omega.

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
   subst tlist.
   assert (tlist4 = map Vint [tt3; tt0; tt1; tt2]).
     subst tlist4 tlist3 tlist2 tlist1. unfold upd_Znth_in_list. Transparent plus. Transparent Z.add. Transparent Z.sub. simpl.
     f_equal.
   clear Heqtlist4 Heqtlist3 Heqtlist2 Heqtlist1.
   subst tlist4.
   apply semax_pre with (P':= 
  (PROP  ()
   LOCAL  (temp _i (Vint (Int.repr i));
   temp _m (Vint (Int.repr 4)); temp _j (Vint (Int.repr j));
   lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
   lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w; temp _in nonce;
   temp _out out; temp _c c; temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(data_at Tsh (tarray tuint 4) (map Vint [tt3; tt0; tt1; tt2]) t);
   `(data_at Tsh (tarray tuint 16) (map Vint wlist) w);
   `(data_at Tsh (tarray tuint 16) (map Vint xs) x);
   `(data_at Tsh (tarray tuint 16) ys y); `(CoreInSEP data (nonce, c, k));
   `(data_at Tsh (tarray tuchar 64) OUT out)))). entailer.
   eapply semax_post. 2: eapply array_copy2; trivial; try eassumption.
   intros ek vl.
   apply andp_left2. 
   unfold POSTCONDITION, abbreviate.
   (*Issue: in master branch, normal_ret_assert_derives worked fine here. 
    Now even doing expliti intros rho, the normal_ret_assert_derives and then
    normalize and/or entailer don't break down the PROP LCOAL SEP structire and don't manage
    to pull out the EX W fron the precondition*)
   apply assert_lemmas.normal_ret_assert_derives'. entailer. apply (exp_right W). entailer. cancel.
Qed.
