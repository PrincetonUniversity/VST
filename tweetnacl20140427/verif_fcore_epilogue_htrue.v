Require Import floyd.proofauto.
Local Open Scope logic.
Require Import List. Import ListNotations.
Require Import general_lemmas.

Require Import split_array_lemmas.
(*Require Import fragments.*)
Require Import ZArith. 
Require Import tweetNaclBase.
Require Import Salsa20.
Require Import tweetnaclVerifiableC.
Require Import verif_salsa_base.

Require Import spec_salsa. 
Opaque Snuffle.Snuffle. Opaque prepare_data.
Opaque core_spec. Opaque ld32_spec. Opaque L32_spec. Opaque st32_spec.
Opaque crypto_core_salsa20_spec. Opaque crypto_core_hsalsa20_spec.

Definition HTrue_inv1 l i ys xs : Prop :=
      Zlength l = 16 /\ exists ints, l=map Vint ints /\
               forall j, 0<=j<16 -> exists xj,
                Znth j xs Vundef = Vint xj
                /\ (j<i -> exists yj, Znth j ys Vundef = Vint yj /\
                                      Znth j l Vundef = Vint (Int.add yj xj)) 
                /\ (i<=j ->  Znth j l Vundef = Vint xj).

Lemma HTrue_loop1 Espec: forall t y x w nonce out c k h data OUT xs ys,
@semax CompSpecs Espec
  (initialized_list [_i] (func_tycontext f_core SalsaVarSpecs SalsaFunSpecs))
  (PROP  ()
   LOCAL  (temp _i (Vint (Int.repr 20)); lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(data_at Tsh (tarray tuint 16) (map Vint xs) x);
   `(data_at Tsh (tarray tuint 16) (map Vint ys) y);
   `(data_at_ Tsh (tarray tuint 4) t); `(data_at_ Tsh (tarray tuint 16) w);
   `(CoreInSEP data (nonce, c, k)); `(data_at Tsh (tarray tuchar 64) OUT out)))
  (Sfor (Sset _i (Econst_int (Int.repr 0) tint))
     (Ebinop Olt (Etempvar _i tint) (Econst_int (Int.repr 16) tint) tint)
     (Ssequence
        (Sset _aux
           (Ederef
              (Ebinop Oadd (Evar _y (tarray tuint 16)) (Etempvar _i tint)
                 (tptr tuint)) tuint))
        (Ssequence
           (Sset _aux1
              (Ederef
                 (Ebinop Oadd (Evar _x (tarray tuint 16)) (Etempvar _i tint)
                    (tptr tuint)) tuint))
           (Sassign
              (Ederef
                 (Ebinop Oadd (Evar _x (tarray tuint 16)) (Etempvar _i tint)
                    (tptr tuint)) tuint)
              (Ebinop Oadd (Etempvar _aux tuint) (Etempvar _aux1 tuint) tuint))))
     (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint)))
  (normal_ret_assert 
   (EX  l : list val,
     PROP  (HTrue_inv1 l 16 (map Vint ys) (map Vint xs))
     LOCAL  (temp _i (Vint (Int.repr 16)); lvar _t (tarray tuint 4) t;
             lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
             lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out;
             temp _c c; temp _k k; temp _h (Vint (Int.repr h)))
     SEP (`(data_at Tsh (tarray tuint 16) l x);
          `(data_at Tsh (tarray tuint 16) (map Vint ys) y);
          `(data_at_ Tsh (tarray tuint 4) t); `(data_at_ Tsh (tarray tuint 16) w);
          `(CoreInSEP data (nonce, c, k)); `(data_at Tsh (tarray tuchar 64) OUT out)))).
Proof. intros. abbreviate_semax.
  assert_PROP (Zlength (map Vint xs) = 16). entailer. rename H into XL.
  assert_PROP (Zlength (map Vint ys) = 16). entailer. rename H into YL.
  LENBforward_for_simple_bound 16 (EX i:Z, 
  (PROP  ()
   LOCAL  (lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(EX l:_, !!HTrue_inv1 l i (map Vint ys) (map Vint xs)
              && data_at Tsh (tarray tuint 16) l x);
   `(data_at Tsh (tarray tuint 16) (map Vint ys) y);
   `(data_at_ Tsh (tarray tuint 4) t); `(data_at_ Tsh (tarray tuint 16) w);
   `(CoreInSEP data (nonce, c, k));
   `(data_at Tsh (tarray tuchar 64) OUT out)))).
  { entailer. apply (exp_right (map Vint xs)).
    entailer. apply prop_right. split. assumption.
    exists xs; split; trivial.
    intros. 
    destruct (Znth_mapVint xs j Vundef) as [xj Xj]. rewrite Zlength_map in XL; omega.
    exists xj; split; trivial.
    split; intros. omega. trivial. }
  { rename H into I. normalize. intros xlist; normalize. 
    destruct H as [XLL XLIST].
    destruct XLIST as [xints [INTS J]]. subst xlist.
    destruct (J _ I) as [xi [Xi [_ HXi]]].
    destruct (Znth_mapVint ys i Vundef) as [yi Yi]. rewrite Zlength_map in YL; omega.
    forward. 
    { entailer. rewrite Yi. entailer. }
    forward.
    { entailer. rewrite HXi. entailer. omega. }
    forward. 
    entailer. rewrite Yi in H1. symmetry in H1; inv H1. rewrite Yi, HXi; simpl. 2: omega. 
    apply (exp_right (upd_Znth_in_list i (map Vint xints) (Vint (Int.add yi xi)))); entailer.
    apply prop_right.
    split.
      rewrite upd_Znth_in_list_Zlength. assumption. simpl; rewrite XLL. omega.
    eexists; split. apply upd_Znth_in_list_ints. 
    intros k K. destruct (J _ K) as [xj [Xj [IJ1 IJ2]]].
      exists xj. split. assumption.
      split; intros. 
      + destruct (zlt k i).
        - destruct (IJ1 l) as [yj [Yj Xj']]. exists yj; split; trivial.
          rewrite upd_Znth_diff; trivial. 
            simpl in *; omega.
            simpl in *; omega.
            omega.
        - assert (JJ: k=i) by omega. subst k.
          rewrite Xj in Xi; inv Xi. 
          rewrite upd_Znth_same, Yi. exists yi; split; trivial.
          simpl in *; omega.
      + rewrite upd_Znth_diff. apply IJ2; omega. 
            simpl in *; omega.
            simpl in *; omega.
            omega. }
entailer. apply (exp_right l); entailer. 
Qed.

(* Fragment:
       FOR(i,4) {
        x[5*i] -= ld32(c+4*i);
        x[6+i] -= ld32(in+4*i);
       }*)  
Fixpoint hPosLoop2 (n:nat) (sumlist: list int) (C Nonce: SixteenByte): list int :=
       match n with
         O => sumlist 
       | S m => let j:= Z.of_nat m in
                let s := hPosLoop2 m sumlist C Nonce in
                let five := Int.sub (Znth (5*j) sumlist Int.zero) (littleendian (Select16Q C j)) in
                let six := Int.sub (Znth (6+j) sumlist Int.zero) (littleendian (Select16Q Nonce j)) in
                upd_Znth_in_list (6+j) (upd_Znth_in_list (5*j) s five) six
       end.

Lemma HTrue_loop2 Espec: forall t y x w nonce out c k h OUT ys intsums Nonce C K,
@semax CompSpecs Espec 
  (initialized_list [_i] (func_tycontext f_core SalsaVarSpecs SalsaFunSpecs))
  (PROP  ()
   LOCAL  ((*temp _i (Vint (Int.repr 16)); *) lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(data_at Tsh (tarray tuint 16) (map Vint intsums) x);
   `(data_at Tsh (tarray tuint 16) (map Vint ys) y);
   `(data_at_ Tsh (tarray tuint 4) t); `(data_at_ Tsh (tarray tuint 16) w);
   `(CoreInSEP(Nonce, C, K) (nonce, c, k));
   `(data_at Tsh (tarray tuchar 64) OUT out)))
   (Ssequence (Sset _i (Econst_int (Int.repr 0) tint))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                 (Econst_int (Int.repr 4) tint) tint)
                    Sskip
                    Sbreak)
                  (Ssequence
                    (Sset _u8_aux
                      (Ebinop Oadd (Etempvar _c (tptr tuchar))
                        (Ebinop Omul (Econst_int (Int.repr 4) tint)
                          (Etempvar _i tint) tint) (tptr tuchar)))
                    (Ssequence
                      (Ssequence
                        (Scall (Some 185%positive)
                          (Evar _ld32 (Tfunction (Tcons (tptr tuchar) Tnil)
                                        tuint cc_default))
                          ((Etempvar _u8_aux (tptr tuchar)) :: nil))
                        (Sset _aux (Etempvar 185%positive tuint)))
                      (Ssequence
                        (Sset _aux1
                          (Ederef
                            (Ebinop Oadd (Evar _x (tarray tuint 16))
                              (Ebinop Omul (Econst_int (Int.repr 5) tint)
                                (Etempvar _i tint) tint) (tptr tuint)) tuint))
                        (Ssequence
                          (Sassign
                            (Ederef
                              (Ebinop Oadd (Evar _x (tarray tuint 16))
                                (Ebinop Omul (Econst_int (Int.repr 5) tint)
                                  (Etempvar _i tint) tint) (tptr tuint))
                              tuint)
                            (Ebinop Osub (Etempvar _aux1 tuint)
                              (Etempvar _aux tuint) tuint))
                          (Ssequence
                            (Sset _u8_aux
                              (Ebinop Oadd (Etempvar _in (tptr tuchar))
                                (Ebinop Omul (Econst_int (Int.repr 4) tint)
                                  (Etempvar _i tint) tint) (tptr tuchar)))
                            (Ssequence
                              (Ssequence
                                (Scall (Some 186%positive)
                                  (Evar _ld32 (Tfunction
                                                (Tcons (tptr tuchar) Tnil)
                                                tuint cc_default))
                                  ((Etempvar _u8_aux (tptr tuchar)) :: nil))
                                (Sset _aux (Etempvar 186%positive tuint)))
                              (Ssequence
                                (Sset _aux1
                                  (Ederef
                                    (Ebinop Oadd (Evar _x (tarray tuint 16))
                                      (Ebinop Oadd
                                        (Econst_int (Int.repr 6) tint)
                                        (Etempvar _i tint) tint)
                                      (tptr tuint)) tuint))
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd (Evar _x (tarray tuint 16))
                                      (Ebinop Oadd
                                        (Econst_int (Int.repr 6) tint)
                                        (Etempvar _i tint) tint)
                                      (tptr tuint)) tuint)
                                  (Ebinop Osub (Etempvar _aux1 tuint)
                                    (Etempvar _aux tuint) tuint))))))))))
                (Sset _i
                  (Ebinop Oadd (Etempvar _i tint)
                    (Econst_int (Int.repr 1) tint) tint))))
  (normal_ret_assert (PROP  ()
 LOCAL  (temp _i (Vint (Int.repr 4)); lvar _t (tarray tuint 4) t;
 lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
 lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
 temp _k k; temp _h (Vint (Int.repr h)))
 SEP  (`(SByte Nonce nonce); `(SByte C c); `(ThirtyTwoByte K k);
 `(data_at Tsh (tarray tuint 16) (map Vint (hPosLoop2 4 intsums C Nonce)) x);
 `(data_at Tsh (tarray tuint 16) (map Vint ys) y);
 `(data_at_ Tsh (tarray tuint 4) t); `(data_at_ Tsh (tarray tuint 16) w);
 `(data_at Tsh (tarray tuchar 64) OUT out)))).
Proof. intros. abbreviate_semax. unfold CoreInSEP. normalize.
  assert_PROP (Zlength (map Vint ys) = 16). entailer. rename H into ZL_Y; rewrite Zlength_map in ZL_Y.
  assert_PROP (Zlength (map Vint intsums) = 16). entailer. rename H into SL; rewrite Zlength_map in SL.
  LENBforward_for_simple_bound 4 (EX i:Z, 
  (PROP  ()
   LOCAL  ((*NOTE: we have to remove the old i here to get things to work: temp _i (Vint (Int.repr 16)); *)
           lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(SByte Nonce nonce); `(SByte C c); `(ThirtyTwoByte K k);
   `(data_at Tsh (tarray tuint 16) (map Vint (hPosLoop2 (Z.to_nat i) intsums C Nonce)) x);
   `(data_at Tsh (tarray tuint 16) (map Vint ys) y);
   `(data_at_ Tsh (tarray tuint 4) t); `(data_at_ Tsh (tarray tuint 16) w);
   `(data_at Tsh (tarray tuchar 64) OUT out)))).
    { entailer. }
    { rename H into I.
      unfold SByte at 2. rewrite data_at_isptr with (p:=c). normalize.
      apply isptrD in Pc. destruct Pc as [cb [coff HC]]. rewrite HC in *.
      Opaque Zmult. Opaque Z.add. 

      forward v.
      assert (C16:= SixteenByte2ValList_Zlength C).
      remember (SplitSelect16Q C i) as FB; destruct FB as (Front, BACK).
      specialize (Select_SplitSelect16Q C i _ _ HeqFB); intros SSS.
      assert_PROP (field_compatible (Tarray tuchar 16 noattr) [] (Vptr cb coff)). entailer.
      rename H into FC.
      destruct (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFB I) as[FL BL].

 (* An alternative to Select_Unselect_Tarray_at is to use
    (split3_data_at_Tarray_at_tuchar Tsh 16 (Zlength (QuadChunks2ValList Front)) 
        (Zlength (QuadChunks2ValList [Select16Q C i]))); trivial;
    repeat rewrite Zlength_app;
    repeat rewrite QuadChunk2ValList_ZLength;
    repeat rewrite FL; try rewrite BL; 
    try rewrite <- QuadByteValList_ZLength; try rewrite Z.mul_1_r.
    2: clear - I; omega. 2: clear - I; omega. 2: clear - I; omega. 
    2: rewrite <- HC; trivial. etc*)  
  erewrite (@Select_Unselect_Tarray_at CompSpecs 16 (Vptr cb coff)); try assumption.
      2: rewrite SSS; reflexivity.
      2: rewrite <- SSS, <- C16; trivial.
      2: rewrite <- SSS, <- C16; cbv; trivial.
  unfold Select_at. repeat rewrite QuadChunk2ValList_ZLength. rewrite Z.mul_1_r, FL.
       simpl. rewrite app_nil_r. simpl. 
       normalize.
      
Transparent core_spec. Transparent ld32_spec. Transparent L32_spec. Transparent st32_spec.
Transparent crypto_core_salsa20_spec. Transparent crypto_core_hsalsa20_spec.
      (*Issue: Like the old forward_call', the new forward_call here leaves delete-temp_from_locals_side 
        conditions. The old forward_call succeeded, and the Frame I used is indeed the one the 
        new forward_call rule also identifies).*)

Inductive delete_temp_from_locals (id: ident) : list (environ -> Prop) -> list (environ -> Prop) -> Prop :=
| dtfl_nil: delete_temp_from_locals id nil nil
| dtfl_here: forall v Q Q',
                delete_temp_from_locals id Q Q' ->
                delete_temp_from_locals id (temp id v :: Q) Q'
| dtfl_cons: forall j v Q Q',
                j<>id ->
                delete_temp_from_locals id Q Q' ->
                delete_temp_from_locals id (temp j v :: Q) (temp j v :: Q')
(*LENB: add the following case:*)
| dtfl_lvar: forall j t v Q Q',
                delete_temp_from_locals id Q Q' ->
                delete_temp_from_locals id (lvar j t v :: Q) (lvar j t v :: Q')
| dtfl_gvar: forall j v Q Q',
                delete_temp_from_locals id Q Q' ->
                delete_temp_from_locals id (gvar j v :: Q) (gvar j v :: Q')
| dtfl_sgvar: forall j v Q Q',
                delete_temp_from_locals id Q Q' ->
                delete_temp_from_locals id (sgvar j v :: Q) (sgvar j v :: Q').      

Lemma LENBsemax_call_id1_wow:
 forall  {A} (witness: A) (Frame: list mpred) 
           Espec {cs: compspecs} Delta P Q R ret id (paramty: typelist) (retty: type) (bl: list expr)
                  (argsig: list (ident * type)) (Pre Post: A -> environ -> mpred)
             (Post2: environ -> mpred)
             (Ppre: list Prop)
             (Qpre Qnew: list (environ -> Prop))
             (Qtemp Qactuals Qpre_temp : PTree.t _)
             (Qvar Qpre_var: PTree.t vardesc)
             (B: Type) 
             (Ppost: B -> list Prop)
             (F: B -> val)
             (Rpre: list (environ -> mpred))
             (Rpost: B -> list (environ -> mpred))
             (Rpost': B -> list mpred)
             (R' Rpre' : list mpred)
             (vl : list val)
   (GLBL: (var_types Delta) ! id = None)
   (GLOBS: (glob_specs Delta) ! id = Some (mk_funspec (argsig,retty) A Pre Post))
   (GLOBT: (glob_types Delta) ! id = Some (type_of_funspec (mk_funspec (argsig,retty) A Pre Post)))
   (TYret: typeof_temp Delta ret = Some retty)
   (OKretty: match retty with Tvoid => False | Tarray _ _ _ => False | _ => True end)
   (H: paramty = type_of_params argsig)
   (PTREE: local2ptree Q Qtemp Qvar nil nil)
   (EXTRACT: extract_trivial_liftx R R')
   (TC1: PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R))
          |--  (tc_exprlist Delta (argtypes argsig) bl))
   (PRE1: Pre witness = PROPx Ppre (LOCALx Qpre (SEPx Rpre)))
   (PTREE': local2ptree Qpre Qpre_temp Qpre_var nil nil)
   (EXTRACT': extract_trivial_liftx Rpre Rpre')
   (MSUBST: force_list (map (msubst_eval_expr Qtemp Qvar) 
                    (explicit_cast_exprlist (argtypes argsig) bl))
                = Some vl)
   (PTREE'': pTree_from_elements (List.combine (var_names argsig) vl) = Qactuals)
   (CHECKTEMP: PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) 
           |-- !! Forall (check_one_temp_spec Qactuals) (PTree.elements Qpre_temp))
   (CHECKVAR: PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R))
           |-- !! Forall (check_one_var_spec Qvar) (PTree.elements Qpre_var))
   (FRAME: fold_right sepcon emp R' |-- fold_right sepcon emp Rpre' * fold_right sepcon emp Frame)
   (POST1: Post witness = EX vret:B, PROPx (Ppost vret)
                              (LOCALx (temp ret_temp (F vret) :: nil) 
                              (SEPx (Rpost vret))))
   (EXTRACT'': forall vret, extract_trivial_liftx (Rpost vret) (Rpost' vret))
   (DELETE: delete_temp_from_locals ret Q Qnew)
   (H0: Post2 = EX vret:B, PROPx (P++ Ppost vret) (LOCALx (temp ret (F vret) :: Qnew)
             (SEPx (map liftx (Rpost' vret ++ Frame)))))
   (PPRE: fold_right_and True Ppre),
   @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R)))
    (Scall (Some ret)
             (Evar id (Tfunction paramty retty cc_default))
             bl)
    (normal_ret_assert Post2).
Proof.
intros.
apply extract_trivial_liftx_e in EXTRACT.
apply extract_trivial_liftx_e in EXTRACT'.
subst.
eapply semax_pre_post; 
   [ | 
   | apply semax_call_id1 with (x:=witness) (P:=P)(Q:=Q) (R := map liftx Frame)
   ];
   try eassumption;
   [ | 
   | clear - OKretty; destruct retty; intuition 
   | hnf; clear - TYret; unfold typeof_temp in TYret;
      destruct ((temp_types Delta) ! ret) as [[? ?] | ]; inv TYret; auto 
    ].
*
 rewrite insert_local.
 apply andp_right; auto.
 rewrite PRE1.
 match goal with |- PROPx ?A ?B |-- ?C =>
  apply derives_trans with (PROPx ((length (argtypes argsig) = length bl) :: A) B);
    [ rewrite <- canonicalize.canon17; apply andp_right; auto | ]
 end.
 eapply derives_trans; [apply TC1 | ].
 clear. go_lowerx.
 unfold tc_exprlist.
 revert bl; induction (argtypes argsig); destruct bl; 
   simpl; try apply @FF_left.
 apply prop_right; auto.
 repeat rewrite denote_tc_assert_andp. apply andp_left2.
 eapply derives_trans; [ apply IHl | ]. normalize.
 progress (autorewrite with norm1 norm2); normalize.
apply derives_extract_PROP; intro LEN.
 clear - PTREE LEN PTREE' MSUBST CHECKVAR FRAME PPRE CHECKTEMP.
 normalize.
replace (@map (environ -> mpred) (LiftEnviron mpred)
               (fun r : environ -> mpred =>
                `r
                  (make_args' (argsig, Tvoid)
                     (eval_exprlist (argtypes argsig) bl)))
               (@map (lift_T (LiftEnviron mpred)) (LiftEnviron mpred)
                  (@liftx (LiftEnviron mpred)) Rpre'))
  with (map liftx Rpre')
  by (rewrite map_map; reflexivity).
 eapply derives_trans.
 apply andp_right. apply andp_right. apply CHECKVAR. apply CHECKTEMP. apply derives_refl.
 rewrite andp_assoc. apply derives_extract_prop; intro CVAR.
 apply derives_extract_prop; intro CTEMP.
 clear CHECKTEMP CHECKVAR.
 apply andp_right. apply andp_left1.
 rewrite fold_right_and_app_low.
 clear - PPRE; apply prop_derives; intuition.
 revert PPRE; induction Ppre; simpl; intuition.
 clear PPRE Ppre.
 rewrite <- insert_local. apply andp_left2. 
 apply andp_right.
2: do 2 apply andp_left2;  unfold SEPx;
  rewrite fold_right_sepcon_app;
  intro rho;  normalize; 
 progress (autorewrite with norm1 norm2); normalize;
  repeat rewrite fold_right_sepcon_liftx; auto.
 clear FRAME Frame Rpre'.
 rewrite fold_right_and_app_lifted, local_lift2_and.
 apply andp_right.  apply andp_left2. apply andp_left1. auto.
 apply (local2ptree_soundness P _ (map liftx R')) in PTREE.
 simpl app in PTREE.
 apply msubst_eval_exprlist_eq with (P:=P)(R:=map liftx R')(Q:=nil) in MSUBST.
 rewrite PTREE.
 clear PTREE Q.
 eapply derives_trans. apply andp_right. apply MSUBST. apply derives_refl.
 clear MSUBST.
 apply (local2ptree_soundness nil _ (TT::nil)) in PTREE'.
 simpl app in PTREE'.
 rewrite !isolate_LOCAL_lem1 in PTREE'.
 intro rho.
 unfold local at 1, lift1.
 simpl.
 apply derives_extract_prop; intro. unfold_lift in H. subst vl.
 unfold PROPx, LOCALx, SEPx. simpl.
apply andp_left2. apply andp_left1.
 assert (LEN': length (var_names argsig) = length (eval_exprlist (argtypes argsig) bl rho)).
 clear - LEN.
  revert bl LEN; induction argsig as [ | [? ?]]; destruct bl; 
    simpl; intros; auto.
 inv LEN.
 forget (argtypes argsig) as tys.
 cut (local (fold_right `and `True (LocalD Qtemp Qvar nil)) rho |-- `(local (fold_right `and `True Qpre))
               (fun rho => (make_args (var_names argsig) (eval_exprlist tys bl rho) rho)) rho).
 intro. eapply derives_trans; [apply H  |]. 
 unfold make_args'. simpl @fst. change (map fst argsig) with (var_names argsig).
 clear.  unfold_lift. unfold local, lift1. apply prop_derives.
 induction Qpre; simpl; auto.  intros [? ?]. split; auto.
 rewrite PTREE'. clear PTREE' Qpre.
 apply prop_derives; intro. forget (var_names argsig) as fl.
 forget (eval_exprlist tys bl rho) as vl.
 clear - CVAR CTEMP H LEN'.
 eapply check_specs_lemma; try eassumption.
*
 clear CHECKVAR CHECKTEMP TC1 PRE1 PPRE.
 intros.
 unfold normal_ret_assert. normalize.
 simpl exit_tycon. rewrite POST1; clear POST1.
 apply derives_trans with
  (EX vret: B,
  PROPx (P ++ Ppost vret)
  (LOCALx (tc_environ (initialized ret Delta) :: map (subst ret `old) Q)
     (SEPx
        (`(PROPx nil
             LOCAL  (temp ret_temp (F vret))  (SEPx (Rpost vret)))
           (get_result1 ret) :: map (subst ret `old) (map liftx Frame))))).
 clear.
 go_lowerx. normalize. apply exp_right with x; normalize.
 apply andp_right; auto.
 apply prop_right; split; auto.
 rewrite fold_right_and_app_low. split; auto.
 apply exp_left; intro vret. apply exp_right with vret.
 normalize.
 progress (autorewrite with norm1 norm2); normalize.
 rewrite <- app_nil_end.
 specialize (EXTRACT'' vret).
 apply extract_trivial_liftx_e in EXTRACT''. rewrite EXTRACT''.
 clear EXTRACT''.
 replace (map (fun r : environ -> mpred => `r (get_result1 ret)) (map liftx (Rpost' vret)))
      with (map liftx (Rpost' vret)) 
  by (rewrite map_map; reflexivity).
 replace (map (subst ret `old) (map liftx Frame))
     with (map liftx Frame)
  by (rewrite map_map; reflexivity).
 clear R' FRAME.
 simpl app.
 rewrite <- insert_local.  apply andp_left2.
 forget (P ++ Ppost vret) as P1.
 rewrite <- map_app.
change  (@map mpred (environ -> mpred))
 with (@map (lift_T (LiftEnviron mpred)) (LiftEnviron mpred)).
 forget (map liftx (Rpost' vret ++ Frame)) as R.
 clear - PTREE DELETE.
 apply (local2ptree_soundness P1 _ R) in PTREE.
 apply andp_derives; auto.
 apply andp_derives; auto.
 intro rho.
 apply prop_derives; intro.
 rewrite fold_right_and_app in H.
 destruct H.
 destruct H0. clear H1.
 unfold_lift in H0. unfold temp, get_result1 in H0.
 normalize in H0. subst.
 split.
 rewrite H0; hnf; reflexivity.
 clear - DELETE H.
 induction DELETE.
 + apply I.
 + destruct H. auto.
 + destruct H; split; auto.
     clear - H H0.
     autorewrite with subst in H. auto.
(*LENB: this case is new:*)  + destruct H; split; auto.
 + destruct H; split; auto.
 + destruct H; split; auto.
Qed.

Ltac LENBforward_call_id1_wow witness :=
let Frame := fresh "Frame" in
 evar (Frame: list (mpred));
 eapply (LENBsemax_call_id1_wow witness Frame);
 [ reflexivity | reflexivity | reflexivity | reflexivity
 | apply (*LENB: added full identifier, to avoid clash with any hypothesis named "I"*) Coq.Init.Logic.I
 | reflexivity
 | prove_local2ptree
 | repeat constructor 
 | try apply local_True_right; entailer!
 | reflexivity
 | prove_local2ptree | repeat constructor 
 | reflexivity | reflexivity
 | Forall_pTree_from_elements
 | Forall_pTree_from_elements
 | unfold fold_right at 1 2; cancel
 | cbv beta; extensionality rho; 
   repeat rewrite exp_uncurry;
   try rewrite no_post_exists; repeat rewrite exp_unfold;
   apply exp_congr; intros ?vret; reflexivity
 | intros; try match goal with  |- extract_trivial_liftx ?A _ =>
        (has_evar A; fail 1) || (repeat constructor)
     end
 | repeat constructor; auto with closed
 | unify_postcondition_exps
 | unfold fold_right_and; repeat rewrite and_True; auto
 ].
(*I thought an alternative sth like this might help with the "cut" in LENBfwd_call' below*)
(*Ltac LENBforward_call_id1_wow witness :=
let Frame := fresh "Frame" in
 evar (Frame: list (mpred));
 eapply (LENBsemax_call_id1_wow witness Frame);
 [ first [ reflexivity | fail 4 "SC1" ]
 | first [ reflexivity | fail 4 "SC2" ]
 | first [ reflexivity | fail 4 "SC3" ]
 | first [ reflexivity | fail 4 "SC4" ]
 | first [ apply (*LENB: added full identifier, to avoid clash with any hypothesis named "I"*) Coq.Init.Logic.I | fail 4 "SC5" ]
 | first [ reflexivity | fail 4 "SC6" ]
 | first [ prove_local2ptree | fail 4 "SC7" ]
 | first [ repeat constructor | fail 4 "SC8" ]
 | first [ try apply local_True_right; entailer! | fail 4 "SC9" ]
 | first [ reflexivity | fail 4 "SC10" ]
 | first [ prove_local2ptree | repeat constructor  | fail 4 "SC11" ]
 | first [ reflexivity | reflexivity | fail 4 "SC12" ]
 | first [ Forall_pTree_from_elements | fail 4 "SC13" ]
 | first [ Forall_pTree_from_elements | fail 4 "SC14" ]
 | first [ unfold fold_right at 1 2; cancel | fail 4 "SC15" ]
 | first [ cbv beta; extensionality rho; 
   repeat rewrite exp_uncurry;
   try rewrite no_post_exists; repeat rewrite exp_unfold;
   apply exp_congr; intros ?vret; reflexivity | fail 4 "SC16" ]
 | first [ intros; try match goal with  |- extract_trivial_liftx ?A _ =>
        (has_evar A; fail 1) || (repeat constructor)
     end | fail 4 "SC17" ]
 | first [ repeat constructor; auto with closed | fail 4 "SC18" ]
 | unify_postcondition_exps
 | unfold fold_right_and; repeat rewrite and_True; auto
 ].*)
(*Or like this:
Definition SC1 := Stuck.
Definition SC2 := Stuck.
Definition SC3 := Stuck.
Definition SC4 := Stuck.
Definition SC5 := Stuck.
Definition SC6 := Stuck.
Definition SC7 := Stuck.
Definition SC8 := Stuck.
Definition SC9 := Stuck.
Definition SC10 := Stuck.
Definition SC11 := Stuck.
Definition SC12 := Stuck.
Definition SC13 := Stuck.
Definition SC14 := Stuck.
Definition SC15 := Stuck.
Definition SC16 := Stuck.
Definition SC17 := Stuck.
Definition SC18 := Stuck.
Definition SC19 := Stuck.
Definition SC20 := Stuck.

Ltac LENBforward_call_id1_wow witness :=
let Frame := fresh "Frame" in
 evar (Frame: list (mpred));
 eapply (LENBsemax_call_id1_wow witness Frame);
 [ first [ reflexivity | stuckwith SC1 ]
 | first [ reflexivity | stuckwith SC2 ]
 | first [ reflexivity | stuckwith SC3 ]
 | first [ reflexivity | stuckwith SC4 ]
 | first [ apply (*LENB: added full identifier, to avoid clash with any hypothesis named "I"*) Coq.Init.Logic.I | stuckwith SC5 ]
 | first [ reflexivity | stuckwith SC6 ]
 | first [ prove_local2ptree | stuckwith SC7 ]
 | first [ repeat constructor | stuckwith SC8 ]
 | first [ try apply local_True_right; entailer! | stuckwith SC9 ]
 | first [ reflexivity | stuckwith SC10 ]
 | first [ prove_local2ptree | repeat constructor  | stuckwith SC11 ]
 | first [ reflexivity | reflexivity | stuckwith SC12 ]
 | first [ Forall_pTree_from_elements | stuckwith SC13 ]
 | first [ Forall_pTree_from_elements | stuckwith SC14 ]
 | first [ unfold fold_right at 1 2; cancel | stuckwith SC15 ]
 | first [ cbv beta; extensionality rho; 
   repeat rewrite exp_uncurry;
   try rewrite no_post_exists; repeat rewrite exp_unfold;
   apply exp_congr; intros ?vret; reflexivity | stuckwith SC16 ]
 | first [ intros; try match goal with  |- extract_trivial_liftx ?A _ =>
        (has_evar A; fail 1) || (repeat constructor)
     end | stuckwith SC17 ]
 | first [ repeat constructor; auto with closed | stuckwith SC18 ]
 | first [ unify_postcondition_exps | stuckwith SC19 ]
 | first [ unfold fold_right_and; repeat rewrite and_True; auto | stuckwith SC20 ]
 ].
*)
Ltac LENBfwd_call' witness :=
 try match goal with
      | |- semax _ _ (Scall _ _ _) _ => rewrite -> semax_seq_skip
      end;
 first [
     revert witness; 
     match goal with |- let _ := ?A in _ => intro; LENBfwd_call' A 
     end
   | eapply semax_seq';
     [first [LENBforward_call_id1_wow witness 
           | fail 1 "Other cases" (*LENB: this is clearly wrong, but currently necessary to prevent 
              any of the 3 next lines to apply. What we really want is probably a Prolog-style cut,
              in case that semax_call_id1_wow indeed got past the eapply*)
           | forward_call_id1_x_wow witness
           | forward_call_id1_y_wow witness
           | forward_call_id01_wow witness ]
     | after_forward_call
     ]
  |  eapply semax_seq'; [forward_call_id00_wow witness 
          | after_forward_call ]
  | rewrite <- seq_assoc; LENBfwd_call' witness
  ].

Tactic Notation "LENBforward_call" constr(witness) simple_intropattern_list(v) :=
    check_canonical_call;
    check_Delta;
    LENBfwd_call' witness;
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

    LENBforward_call ((Vptr cb (Int.add coff (Int.repr (4 * i)))),
                      Select16Q C i) pat. 
Opaque core_spec. Opaque ld32_spec. Opaque L32_spec. Opaque st32_spec.
Opaque crypto_core_salsa20_spec. Opaque crypto_core_hsalsa20_spec.

(***********If we use the original forward_call, the following works
      forward_call ((Vptr cb (Int.add coff (Int.repr (4 * i)))),
                      Select16Q C i) pat.
Opaque core_spec. Opaque ld32_spec. Opaque L32_spec. Opaque st32_spec.
Opaque crypto_core_salsa20_spec. Opaque crypto_core_hsalsa20_spec.
(*Looking at how we want LOCAL in goal 3 to look like we can guess the instanitiation:*)
   instantiate (1:= [ lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out;
   temp _c (Vptr cb coff); temp _k k; temp _h (Vint (Int.repr h))]). admit. admit. 
(* Old Frame:     { assert (FR: Frame = [`(Unselect_at tuchar Tsh (QuadChunks2ValList Front)
                            (QuadChunks2ValList [Select16Q C i]) (QuadChunks2ValList BACK) c);
                             `(SByte Nonce nonce); `(ThirtyTwoByte K k);
                             `(data_at Tsh (tarray tuint 16) (map Vint
                               (hPosLoop2 (Z.to_nat i) intsums C Nonce)) x);
                             `(data_at Tsh (tarray tuint 16) (map Vint ys) y);
                             `(data_at_ Tsh (tarray tuint 4) t); `(data_at_ Tsh (tarray tuint 16) w);
                             `(data_at Tsh (tarray tuchar 64) OUT out)]).
          subst Frame. reflexivity.
        subst Frame; clear FR. entailer. rewrite app_nil_r. cancel. }
      { repeat econstructor. }
      after_call.*)
      simpl. 
**************************************************) 
      subst pat.
      assert (PL2length: forall n, (0<=n<4)%nat -> Zlength (hPosLoop2 n intsums C Nonce) = 16).
        clear - SL.
        induction n; simpl; intros. trivial.
        repeat rewrite upd_Znth_in_list_Zlength. apply IHn; omega. omega. 
          rewrite IHn; omega. 
          rewrite IHn; omega. 
      assert (PL2Zlength: Zlength (hPosLoop2 (Z.to_nat i) intsums C Nonce) = 16).
         apply PL2length. split; try omega. apply (Z2Nat.inj_lt _ 4); omega.
        
      destruct (Znth_mapVint (hPosLoop2 (Z.to_nat i) intsums C Nonce) (5*i) Vundef) as [vj Vj].
      rewrite PL2Zlength; omega. 
      forward v1.
(*before change to LENB forward_call above, we needed this here:
          { entailer. rewrite ZtoNat_Zlength in Vj; rewrite Vj. apply prop_right; trivial. }
      rewrite Vj.*)

(*Now, we need to remove Zlength Front = i here :*) clear FL.
      forward.
(*And, we need similar 2 lines as above, but one instruction later:*)
         { entailer. simpl in *. rewrite Vj. apply prop_right; trivial. }

      unfold SByte. rewrite data_at_isptr with (p:=nonce). normalize.
      apply isptrD in Pnonce. destruct Pnonce as [nb [noff NC]]. rewrite NC in *.
      forward.

      assert_PROP (field_compatible (Tarray tuchar 16 noattr) [] (Vptr nb noff)). entailer.
      rename H into FCN.
      assert (N16:= SixteenByte2ValList_Zlength Nonce).
      remember (SplitSelect16Q Nonce i) as FBN; destruct FBN as (FrontN, BACKN).
      specialize (Select_SplitSelect16Q Nonce i _ _ HeqFBN); intros NNN.
      unfold SByte.
      destruct (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFBN I) as [FN BN].
      erewrite Select_Unselect_Tarray_at; try reflexivity; try assumption.
      2: rewrite NNN; reflexivity.
      2: rewrite <- NNN, <- N16; trivial.
      2: rewrite <- NNN, <- N16; cbv; trivial.
      unfold Select_at. repeat rewrite QuadChunk2ValList_ZLength. rewrite Zmult_1_r, FN.
      simpl. rewrite app_nil_r. simpl. 
      normalize. rewrite Vj.
Transparent core_spec. Transparent ld32_spec. Transparent L32_spec. Transparent st32_spec.
Transparent crypto_core_salsa20_spec. Transparent crypto_core_hsalsa20_spec.
      (*TODO: same issue with delete_temps here. But calling LENBforward_call results in Coq 
       crash that's not about memory exhaustion, but: 
      "Unable to communicate with coqtop, restarting coqtop.
       Error was: Invalid argument"*)
          
      forward_call (Vptr nb (Int.add noff (Int.repr (4 * i))),
                     Select16Q Nonce i) pat.
Opaque core_spec. Opaque ld32_spec. Opaque L32_spec. Opaque st32_spec.
Opaque crypto_core_salsa20_spec. Opaque crypto_core_hsalsa20_spec.
      instantiate (1:= [temp _aux (Vint (littleendian (Select16Q C i)));
             lvar _t (tarray tuint 4) t;
             lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
             lvar _w (tarray tuint 16) w; temp _in (Vptr nb noff); temp _out out;
             temp _c (Vptr cb coff); temp _k k; temp _h (Vint (Int.repr h))]). admit. admit.
(*      { assert (FR: Frame = [`(Unselect_at tuchar Tsh (QuadChunks2ValList FrontN)
                               (QuadChunks2ValList [Select16Q Nonce i]) (QuadChunks2ValList BACKN) nonce);
                             `(QByte (Select16Q C i) (offset_val (Int.repr (4 * i)) c));
                             `(Unselect_at tuchar Tsh (QuadChunks2ValList Front)
                                  (QuadByte2ValList (Select16Q C i)) (QuadChunks2ValList BACK) c);
                             `(data_at Tsh (tarray tuint 16)
                                  (upd_reptype_array tuint (5 * i) (map Vint (hPosLoop2 (Z.to_nat i) intsums C Nonce)) (*l*)
                                  (Vint (Int.sub vj (littleendian (Select16Q C i))))) x);
                             `(ThirtyTwoByte K k);
                             `(data_at Tsh (tarray tuint 16) (map Vint ys) y);
                             `(data_at_ Tsh (tarray tuint 4) t); `(data_at_ Tsh (tarray tuint 16) w);
                             `(data_at Tsh (tarray tuchar 64) OUT out)]).
          subst Frame. reflexivity.
        subst Frame; clear FR. entailer. rewrite app_nil_r. cancel. }
      { repeat econstructor. }
   
      after_call.*) 

     subst pat. simpl. 
     destruct (Znth_mapVint (hPosLoop2 (Z.to_nat i) intsums C Nonce) (6+i) Vundef) as [uj Uj].
      rewrite PL2Zlength; omega.
     forward v3.
     { entailer. rewrite ZtoNat_Zlength in Uj, PL2Zlength.
           rewrite upd_Znth_diff. rewrite Uj. apply prop_right; trivial.
           rewrite Zlength_map, PL2Zlength; simpl; omega.
           rewrite Zlength_map, PL2Zlength; simpl; omega.
           omega. } 
     subst v3.
     rewrite upd_Znth_diff. 
       2: rewrite Zlength_map, PL2Zlength; simpl; omega. 
       2: rewrite Zlength_map, PL2Zlength; simpl; omega. 
       2: omega.
     forward.
(*Issue: substitution in entailer is a bit too eager here. Without the following assert (FLN: ...) ... destruct FLN,
  the two hypotheses are simply combined to Zlength Front = Zlength FrontN by entailer (and again by the inv H0) *)
     assert (FLN: Zlength Front = i /\ Zlength FrontN = i). split; assumption. clear FL FN.
     entailer. 
     rewrite Uj in H0. symmetry in H0; inv H0.
     destruct FLN as [FL FLN].

     rewrite Uj. simpl.
     cancel.
     repeat rewrite <- sepcon_assoc.
     apply sepcon_derives.
     + unfold SByte.
       erewrite Select_Unselect_Tarray_at; try reflexivity; try assumption.
       2: rewrite NNN; reflexivity.
       erewrite Select_Unselect_Tarray_at; try reflexivity; try assumption.
       2: rewrite SSS; reflexivity. 
       unfold Select_at. repeat rewrite QuadChunk2ValList_ZLength. rewrite FL, FLN.
        rewrite Zmult_1_r. simpl. 
        unfold QByte. repeat rewrite app_nil_r. cancel.
       rewrite <- SSS, <- C16; trivial.
       rewrite <- SSS, <- C16. cbv; trivial.
       rewrite <- NNN, <- N16; trivial.
       rewrite <- NNN, <- N16. cbv; trivial.
     + rewrite field_at_isptr. normalize. apply isptrD in Px. destruct Px as [xb [xoff XP]]. rewrite XP in *.
       rewrite field_at_data_at. unfold tarray, field_address; simpl. if_tac; try contradiction.
       rewrite Int.add_zero. 
       apply data_at_ext.
       rewrite (Zplus_comm i 1), Z2Nat.inj_add; simpl; try omega.
       rewrite Z2Nat.id.
       rewrite upd_Znth_in_list_ints.
       rewrite upd_Znth_in_list_ints. 
       unfold upd_Znth_in_list.
       assert (VJeq: vj = Znth (5 * i) intsums Int.zero). 
       { clear - Vj SL PL2length I.
         rewrite (Znth_map _ _ (5 * i) Vint) with (d':=Int.zero) in Vj. inv Vj.
         2: rewrite PL2length; try omega. Focus 2. split. apply (Z2Nat.inj_le 0); omega. apply (Z2Nat.inj_lt _ 4); omega.        
         destruct (zeq i 0); subst; simpl. trivial.
         destruct (zeq i 1); subst; simpl.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_in_list_Zlength; try omega.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_in_list_Zlength; try omega. trivial.
         destruct (zeq i 2); subst; simpl.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_in_list_Zlength; try omega.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_in_list_Zlength; try omega. 
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_in_list_Zlength; try omega.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_in_list_Zlength; try omega. trivial.
         destruct (zeq i 3); subst; simpl.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_in_list_Zlength; try omega.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_in_list_Zlength; try omega. 
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_in_list_Zlength; try omega.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_in_list_Zlength; try omega. 
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_in_list_Zlength; try omega.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_in_list_Zlength; try omega. trivial.
         omega. } 
       rewrite <- VJeq, Zlength_map. trivial.
       assert (UJeq: uj = Znth (6 + i) intsums Int.zero).
       { clear - Uj SL PL2length I.
         rewrite (Znth_map _ _ (6 + i) Vint) with (d':=Int.zero) in Uj. inv Uj.
         2: rewrite PL2length; try omega. Focus 2. split. apply (Z2Nat.inj_le 0); omega. apply (Z2Nat.inj_lt _ 4); omega.        
         destruct (zeq i 0); subst; simpl. trivial.
         destruct (zeq i 1); subst; simpl.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_in_list_Zlength; try omega.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_in_list_Zlength; try omega. trivial.
         destruct (zeq i 2); subst; simpl.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_in_list_Zlength; try omega.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_in_list_Zlength; try omega. 
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_in_list_Zlength; try omega.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_in_list_Zlength; try omega. trivial.
         destruct (zeq i 3); subst; simpl.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_in_list_Zlength; try omega.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_in_list_Zlength; try omega. 
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_in_list_Zlength; try omega.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_in_list_Zlength; try omega. 
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_in_list_Zlength; try omega.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_in_list_Zlength; try omega. trivial.
         omega. }
       rewrite <- UJeq, Zlength_map, H1. reflexivity. apply I. }
  entailer. 
Qed.

Definition UpdateOut (l: list val) (i:Z) (xi:int) :=
         (sublist 0 i l) ++ QuadByte2ValList (littleendian_invert xi) ++ sublist (i+4) (Zlength l) l.

Lemma UpdateOut_Zlength l i xi: 0<=i -> i + 4 <= Zlength l -> Zlength (UpdateOut l i xi) = Zlength l.
Proof. intros. unfold UpdateOut. repeat rewrite Zlength_app.
  repeat rewrite Zlength_sublist; try omega.
  rewrite <- QuadByteValList_ZLength. omega.
Qed. 

Fixpoint hPosLoop3 (n:nat) (xlist: list int) (old: list val): list val :=
    match n with 
      O => old
    | S m => let j:= Z.of_nat m in
                let s := hPosLoop3 m xlist old in
                let five := Znth (5*j) xlist Int.zero in
                let six := Znth (6+j) xlist Int.zero in
                UpdateOut (UpdateOut s (4*j) five) (16+4*j) six
       end.

Lemma hposLoop3_length xlist old: forall n, (16+4*Z.of_nat n<Zlength old) ->
        Zlength (hPosLoop3 n xlist old) = Zlength old. 
  Proof. induction n; simpl; intros. trivial.
    rewrite Zpos_P_of_succ_nat in H.
    repeat rewrite UpdateOut_Zlength.
      apply IHn. omega.
    omega. 
    simpl. rewrite IHn. omega. omega.
    omega. 
    simpl. rewrite IHn. omega. omega.
    omega. 
    simpl. rewrite IHn. omega. omega. 
  Qed.

Lemma HTrue_loop3 Espec t y x w nonce out c k h OUT xs ys Nonce C K:
@semax CompSpecs Espec 
  (initialized_list [_i] (func_tycontext f_core SalsaVarSpecs SalsaFunSpecs))
  (PROP  ()
   LOCAL  (lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(SByte Nonce nonce); `(SByte C c);
   `(ThirtyTwoByte K k);
   `(data_at Tsh (tarray tuint 16) (map Vint xs) x);
   `(data_at Tsh (tarray tuint 16) (map Vint ys) y);
   `(data_at_ Tsh (tarray tuint 4) t); `(data_at_ Tsh (tarray tuint 16) w);
   `(data_at Tsh (tarray tuchar 64) OUT out)))
  (Sfor (Sset _i (Econst_int (Int.repr 0) tint))
     (Ebinop Olt (Etempvar _i tint) (Econst_int (Int.repr 4) tint) tint)
     (Ssequence
        (Sset _aux
           (Ederef
              (Ebinop Oadd (Evar _x (tarray tuint 16))
                 (Ebinop Omul (Econst_int (Int.repr 5) tint)
                    (Etempvar _i tint) tint) (tptr tuint)) tuint))
        (Ssequence
           (Sset _u8_aux
              (Ebinop Oadd (Etempvar _out (tptr tuchar))
                 (Ebinop Omul (Econst_int (Int.repr 4) tint)
                    (Etempvar _i tint) tint) (tptr tuchar)))
           (Ssequence
              (Scall None
                 (Evar _st32
                    (Tfunction (Tcons (tptr tuchar) (Tcons tuint Tnil)) tvoid
                       cc_default))
                 [Etempvar _u8_aux (tptr tuchar); Etempvar _aux tuint])
              (Ssequence
                 (Sset _aux
                    (Ederef
                       (Ebinop Oadd (Evar _x (tarray tuint 16))
                          (Ebinop Oadd (Econst_int (Int.repr 6) tint)
                             (Etempvar _i tint) tint) (tptr tuint)) tuint))
                 (Ssequence
                    (Sset _u8_aux
                       (Ebinop Oadd
                          (Ebinop Oadd (Etempvar _out (tptr tuchar))
                             (Econst_int (Int.repr 16) tint) (tptr tuchar))
                          (Ebinop Omul (Econst_int (Int.repr 4) tint)
                             (Etempvar _i tint) tint) (tptr tuchar)))
                    (Scall None
                       (Evar _st32
                          (Tfunction (Tcons (tptr tuchar) (Tcons tuint Tnil))
                             tvoid cc_default))
                       [Etempvar _u8_aux (tptr tuchar); Etempvar _aux tuint]))))))
     (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint)))
(normal_ret_assert (
  PROP  ()
  LOCAL  (lvar _t (tarray tuint 4) t;
          lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
          lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
          temp _k k; temp _h (Vint (Int.repr h)))
  SEP (`(SByte Nonce nonce); `(SByte C c); `(ThirtyTwoByte K k);
       `(data_at Tsh (tarray tuint 16) (map Vint xs) x);
       `(data_at Tsh (tarray tuint 16) (map Vint ys) y);
       `(data_at_ Tsh (tarray tuint 4) t); `(data_at_ Tsh (tarray tuint 16) w);
       `(data_at Tsh (tarray tuchar 64) (hPosLoop3 4 xs OUT) out)))).
Proof. intros. abbreviate_semax.
 assert_PROP (Zlength (map Vint xs) = 16). entailer. rename H into ZL_X; rewrite Zlength_map in ZL_X.
 assert_PROP (Zlength OUT = 64). entailer. rename H into OL.
 LENBforward_for_simple_bound 4 (EX i:Z, 
  (PROP  ()
   LOCAL  (lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
   lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w; temp _in nonce;
   temp _out out; temp _c c; temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(SByte Nonce nonce); `(SByte C c); `(ThirtyTwoByte K k);
   `(data_at Tsh (tarray tuint 16) (map Vint xs) x);
   `(data_at Tsh (tarray tuint 16) (map Vint ys) y);
   `(data_at_ Tsh (tarray tuint 4) t); `(data_at_ Tsh (tarray tuint 16) w);
   `(data_at Tsh (tarray tuchar 64) (hPosLoop3 (Z.to_nat i) xs OUT) out)))).
    { entailer. }
  { rename H into I. 

    assert (P3_Zlength: Zlength (hPosLoop3 (Z.to_nat i) xs OUT) = 64).
      rewrite hposLoop3_length. assumption. rewrite OL, Z2Nat.id; omega.
    assert (P3_length: length (hPosLoop3 (Z.to_nat i) xs OUT) = 64%nat).
      rewrite <- ZtoNat_Zlength, P3_Zlength; reflexivity.
    remember (hPosLoop3 (Z.to_nat i) xs OUT) as ll. (*clear Heqll.*)
      
    destruct (Znth_mapVint xs (5 * i) Vundef) as [xi Xi]. omega.
    forward v.
    { entailer. rewrite Xi. entailer. }
    rewrite Xi.
    rewrite data_at_isptr with (p:=out). normalize.
    apply isptrD in Pout. destruct Pout as [ob [ooff OC]]. rewrite OC in *.
    forward v2. 
    assert_PROP(field_compatible (Tarray tuchar 64 noattr) [] (Vptr ob ooff)). entailer.
    rename H into FCO.
    rewrite <- P3_Zlength.
    rewrite (split3_data_at_Tarray_at_tuchar Tsh (Zlength ll) (4 *i) 4); try rewrite P3_Zlength; trivial; try omega. 
    unfold at_offset at 1.
    normalize.
Transparent core_spec. Transparent ld32_spec. Transparent L32_spec. Transparent st32_spec.
Transparent crypto_core_salsa20_spec. Transparent crypto_core_hsalsa20_spec.
    forward_call (offset_val (Int.repr (4 * i)) (Vptr ob ooff), xi).
Opaque core_spec. Opaque ld32_spec. Opaque L32_spec. Opaque st32_spec.
Opaque crypto_core_salsa20_spec. Opaque crypto_core_hsalsa20_spec.
    { entailer.
      apply (exp_right (sublist (4 * i) (4 + 4 * i) ll)).
      entailer. cancel. }
    normalize. Opaque mult. 
    assert (Upd_ll_Zlength: Zlength (UpdateOut ll (4 * i) xi) = 64).
      rewrite UpdateOut_Zlength; trivial. omega. omega.
    apply semax_pre with (P':=
  (PROP  ()
   LOCAL  (temp _u8_aux (Vptr ob (Int.add ooff (Int.repr (4 * i))));
   temp _aux (Vint xi); temp _i (Vint (Int.repr i));
   lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
   lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w; temp _in nonce;
   temp _out (Vptr ob ooff); temp _c c; temp _k k;
   temp _h (Vint (Int.repr h)))
   SEP 
   (`(data_at Tsh (tarray tuchar 64) (UpdateOut ll (4*i) xi) (Vptr ob ooff));
   `(SByte Nonce nonce); `(SByte C c); `(ThirtyTwoByte K k);
   `(data_at Tsh (tarray tuint 16) (map Vint xs) x);
   `(data_at Tsh (tarray tuint 16) (map Vint ys) y);
   `(data_at_ Tsh (tarray tuint 4) t); `(data_at_ Tsh (tarray tuint 16) w)))).
    { clear Heqll. Opaque Zminus. entailer. cancel. unfold QByte.
      rewrite <- Upd_ll_Zlength.
      erewrite (append_split3_data_at_Tarray_at_tuchar' Tsh  (UpdateOut ll (4 * i) _id0)); try rewrite UpdateOut_Zlength, P3_Zlength; try omega.
       2: reflexivity.
       2: cbv; trivial.
       2: assumption.
      unfold at_offset.
      rewrite <- QuadByteValList_ZLength. repeat rewrite Zlength_sublist; try omega.
      rewrite P3_Zlength, Zminus_0_r, (Zplus_comm 4).  cancel. }
 
    destruct (Znth_mapVint xs (6+i) Vundef) as [zi Zi]. omega.
    forward u.
    { entailer. rewrite Zi. apply prop_right; trivial. }
    rewrite Zi.
    forward u2. 
    erewrite (split3_data_at_Tarray_at_tuchar Tsh 64 (16 + 4 *i) 4); trivial; try omega.
    unfold at_offset at 1. 
Transparent core_spec. Transparent ld32_spec. Transparent L32_spec. Transparent st32_spec.
Transparent crypto_core_salsa20_spec. Transparent crypto_core_hsalsa20_spec.
    forward_call (offset_val (Int.repr (16 + 4 * i)) (Vptr ob ooff), zi).
Opaque core_spec. Opaque ld32_spec. Opaque L32_spec. Opaque st32_spec.
Opaque crypto_core_salsa20_spec. Opaque crypto_core_hsalsa20_spec.
    { entailer. 
      apply (exp_right (sublist (16 + 4 * i) (4 + (16 + 4 * i)) (UpdateOut ll (4 * i) xi))).
      entailer. cancel. }
    normalize. entailer. cancel.
    assert (AA:  Z.to_nat (i + 1) = S (Z.to_nat i)).
      rewrite (Z.add_comm _ 1), Z2Nat.inj_add. simpl. apply NPeano.Nat.add_1_l. omega. omega.
    rewrite AA. simpl. 
    clear H10 H13 TC TC0 TC1 TC2 TC3 H7.
    remember (hPosLoop3 (Z.to_nat i) xs OUT) as ll; clear Heqll.
    assert (XXi: xi = Znth (5 * i) xs Int.zero).
      rewrite Znth_map' with (d':=Int.zero) in Xi; try omega. clear -Xi. inv Xi. trivial.
    assert (ZZi: _id0 = Znth (6 + i) xs Int.zero).
      rewrite Znth_map' with (d':=Int.zero) in Zi; try omega. clear -Zi. inv Zi. trivial.
    rewrite Z2Nat.id, <- XXi, <- ZZi; try omega; clear XXi ZZi.
    unfold QByte.
    remember (UpdateOut ll (4 * i) xi) as l.
    assert (ZLU: Zlength(UpdateOut l (16 + 4 * i) _id0) = 64).
      rewrite UpdateOut_Zlength; trivial. omega. omega.
    rewrite <- ZLU.
    erewrite (append_split3_data_at_Tarray_at_tuchar' Tsh  (UpdateOut l (16 + 4 * i) _id0)); 
      try rewrite ZLU; try rewrite P3_Zlength; try omega; try reflexivity; trivial.
    unfold at_offset.
    repeat rewrite Zlength_sublist; try omega. 
    rewrite <- QuadByteValList_ZLength, Upd_ll_Zlength, Zminus_0_r, (Zplus_comm 4). cancel. }
entailer. (*With temp _i (Vint (Int.repr 4)) in LOCAL of HTruePostCondL apply derives_refl.*)
Qed.

Lemma hposLoop2_Zlength16 C N l (L:Zlength l = 16): forall n, 
      5 * Z.of_nat n < 16-> 6+ Z.of_nat n < 16 -> Zlength (hPosLoop2 (S n) l C N) = 16.
Proof. intros. simpl. 
  induction n; simpl; intros; trivial.
  rewrite upd_Znth_in_list_Zlength; rewrite upd_Znth_in_list_Zlength; omega. 
  rewrite Nat2Z.inj_succ in *.
  rewrite upd_Znth_in_list_Zlength; rewrite upd_Znth_in_list_Zlength; rewrite IHn; simpl; try omega. 
  rewrite Zpos_P_of_succ_nat. omega.
  rewrite Zpos_P_of_succ_nat. omega.
  rewrite Zpos_P_of_succ_nat. omega.
Qed.

Definition HTruePostCond t y x w nonce out c k h (xs:list int) ys Nonce C K OUT := 
(EX intsums:_,
  PROP (Zlength intsums = 16 /\
        (forall j, 0 <= j < 16 -> 
           exists xj, exists yj, 
           Znth j (map Vint xs) Vundef = Vint xj /\
           Znth j (map Vint ys) Vundef = Vint yj /\
           Znth j (map Vint intsums) Vundef = Vint (Int.add yj xj)))
  LOCAL (lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
  SEP (`(SByte Nonce nonce); `(SByte C c);
       `(ThirtyTwoByte K k);
       `(data_at Tsh (tarray tuint 16)
         (map Vint (hPosLoop2 4 intsums C Nonce)) x);
       `(data_at Tsh (tarray tuint 16) (map Vint ys) y);
       `(data_at_ Tsh (tarray tuint 4) t); `(data_at_ Tsh (tarray tuint 16) w);
       `(data_at Tsh (tarray tuchar 64)
          (hPosLoop3 4 (hPosLoop2 4 intsums C Nonce) OUT) out))).

Lemma verif_fcore_epilogue_htrue Espec t y x w nonce out c k h OUT xs ys Nonce C K:
@semax CompSpecs Espec
  (initialized_list [_i] (func_tycontext f_core SalsaVarSpecs SalsaFunSpecs))
  (PROP  ()
   LOCAL  (temp _i (Vint (Int.repr 20)); lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(data_at Tsh (tarray tuint 16) (map Vint xs) x);
   `(data_at Tsh (tarray tuint 16) (map Vint ys) y);
   `(data_at_ Tsh (tarray tuint 4) t); `(data_at_ Tsh (tarray tuint 16) w);
   `(CoreInSEP (Nonce, C, K) (nonce, c, k)); `(data_at Tsh (tarray tuchar 64) OUT out)))
        (Ssequence
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
                      (Ebinop Oadd (Evar _y (tarray tuint 16))
                        (Etempvar _i tint) (tptr tuint)) tuint))
                  (Ssequence
                    (Sset _aux1
                      (Ederef
                        (Ebinop Oadd (Evar _x (tarray tuint 16))
                          (Etempvar _i tint) (tptr tuint)) tuint))
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Evar _x (tarray tuint 16))
                          (Etempvar _i tint) (tptr tuint)) tuint)
                      (Ebinop Oadd (Etempvar _aux tuint)
                        (Etempvar _aux1 tuint) tuint)))))
              (Sset _i
                (Ebinop Oadd (Etempvar _i tint)
                  (Econst_int (Int.repr 1) tint) tint))))
          (Ssequence
            (Ssequence
              (Sset _i (Econst_int (Int.repr 0) tint))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                 (Econst_int (Int.repr 4) tint) tint)
                    Sskip
                    Sbreak)
                  (Ssequence
                    (Sset _u8_aux
                      (Ebinop Oadd (Etempvar _c (tptr tuchar))
                        (Ebinop Omul (Econst_int (Int.repr 4) tint)
                          (Etempvar _i tint) tint) (tptr tuchar)))
                    (Ssequence
                      (Ssequence
                        (Scall (Some 185%positive)
                          (Evar _ld32 (Tfunction (Tcons (tptr tuchar) Tnil)
                                        tuint cc_default))
                          ((Etempvar _u8_aux (tptr tuchar)) :: nil))
                        (Sset _aux (Etempvar 185%positive tuint)))
                      (Ssequence
                        (Sset _aux1
                          (Ederef
                            (Ebinop Oadd (Evar _x (tarray tuint 16))
                              (Ebinop Omul (Econst_int (Int.repr 5) tint)
                                (Etempvar _i tint) tint) (tptr tuint)) tuint))
                        (Ssequence
                          (Sassign
                            (Ederef
                              (Ebinop Oadd (Evar _x (tarray tuint 16))
                                (Ebinop Omul (Econst_int (Int.repr 5) tint)
                                  (Etempvar _i tint) tint) (tptr tuint))
                              tuint)
                            (Ebinop Osub (Etempvar _aux1 tuint)
                              (Etempvar _aux tuint) tuint))
                          (Ssequence
                            (Sset _u8_aux
                              (Ebinop Oadd (Etempvar _in (tptr tuchar))
                                (Ebinop Omul (Econst_int (Int.repr 4) tint)
                                  (Etempvar _i tint) tint) (tptr tuchar)))
                            (Ssequence
                              (Ssequence
                                (Scall (Some 186%positive)
                                  (Evar _ld32 (Tfunction
                                                (Tcons (tptr tuchar) Tnil)
                                                tuint cc_default))
                                  ((Etempvar _u8_aux (tptr tuchar)) :: nil))
                                (Sset _aux (Etempvar 186%positive tuint)))
                              (Ssequence
                                (Sset _aux1
                                  (Ederef
                                    (Ebinop Oadd (Evar _x (tarray tuint 16))
                                      (Ebinop Oadd
                                        (Econst_int (Int.repr 6) tint)
                                        (Etempvar _i tint) tint)
                                      (tptr tuint)) tuint))
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd (Evar _x (tarray tuint 16))
                                      (Ebinop Oadd
                                        (Econst_int (Int.repr 6) tint)
                                        (Etempvar _i tint) tint)
                                      (tptr tuint)) tuint)
                                  (Ebinop Osub (Etempvar _aux1 tuint)
                                    (Etempvar _aux tuint) tuint))))))))))
                (Sset _i
                  (Ebinop Oadd (Etempvar _i tint)
                    (Econst_int (Int.repr 1) tint) tint))))
            (Ssequence
              (Sset _i (Econst_int (Int.repr 0) tint))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                 (Econst_int (Int.repr 4) tint) tint)
                    Sskip
                    Sbreak)
                  (Ssequence
                    (Sset _aux
                      (Ederef
                        (Ebinop Oadd (Evar _x (tarray tuint 16))
                          (Ebinop Omul (Econst_int (Int.repr 5) tint)
                            (Etempvar _i tint) tint) (tptr tuint)) tuint))
                    (Ssequence
                      (Sset _u8_aux
                        (Ebinop Oadd (Etempvar _out (tptr tuchar))
                          (Ebinop Omul (Econst_int (Int.repr 4) tint)
                            (Etempvar _i tint) tint) (tptr tuchar)))
                      (Ssequence
                        (Scall None
                          (Evar _st32 (Tfunction
                                        (Tcons (tptr tuchar)
                                          (Tcons tuint Tnil)) tvoid
                                        cc_default))
                          ((Etempvar _u8_aux (tptr tuchar)) ::
                           (Etempvar _aux tuint) :: nil))
                        (Ssequence
                          (Sset _aux
                            (Ederef
                              (Ebinop Oadd (Evar _x (tarray tuint 16))
                                (Ebinop Oadd (Econst_int (Int.repr 6) tint)
                                  (Etempvar _i tint) tint) (tptr tuint))
                              tuint))
                          (Ssequence
                            (Sset _u8_aux
                              (Ebinop Oadd
                                (Ebinop Oadd (Etempvar _out (tptr tuchar))
                                  (Econst_int (Int.repr 16) tint)
                                  (tptr tuchar))
                                (Ebinop Omul (Econst_int (Int.repr 4) tint)
                                  (Etempvar _i tint) tint) (tptr tuchar)))
                            (Scall None
                              (Evar _st32 (Tfunction
                                            (Tcons (tptr tuchar)
                                              (Tcons tuint Tnil)) tvoid
                                            cc_default))
                              ((Etempvar _u8_aux (tptr tuchar)) ::
                               (Etempvar _aux tuint) :: nil))))))))
                (Sset _i
                  (Ebinop Oadd (Etempvar _i tint)
                    (Econst_int (Int.repr 1) tint) tint))))))
(normal_ret_assert (HTruePostCond t y x w nonce out c k h xs ys Nonce C K OUT)).
Proof. intros.
forward_seq. apply HTrue_loop1; trivial.
apply extract_exists_pre; intros sums. normalize. 
destruct H as [SL [intsums [? HSums1]]]; subst sums. rewrite Zlength_map in SL.
forward_seq.
  eapply semax_pre. 
   2: apply (HTrue_loop2 Espec t y x w nonce out c k h OUT ys intsums Nonce C K); assumption.
   entailer. 
eapply semax_pre_post.
  Focus 3. apply (HTrue_loop3 Espec t y x w nonce out c k h OUT 
            (hPosLoop2 4 intsums C Nonce) ys Nonce C K); try assumption.
  entailer. 
unfold POSTCONDITION, abbreviate, HTruePostCond. Opaque ThirtyTwoByte. Opaque hPosLoop2. Opaque hPosLoop3.
intros. entailer. simpl. apply normal_ret_assert_derives.
apply (exp_right intsums). entailer.
apply prop_right. clear - HSums1 SL. intros.
  destruct (HSums1 _ H) as [xj [Xj [X _]]].
  destruct X as [yj [Yi Sj]]. apply H.
  exists xj, yj. auto.
Qed.