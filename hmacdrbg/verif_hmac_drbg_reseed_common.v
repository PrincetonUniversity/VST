Require Import VST.floyd.proofauto.
Import ListNotations.
Local Open Scope logic.

Require Import sha.general_lemmas.
Require Import hmacdrbg.entropy.
Require Import hmacdrbg.entropy_lemmas.
Require Import hmacdrbg.hmac_drbg.
Require Import hmacdrbg.DRBG_functions.
Require Import hmacdrbg.HMAC_DRBG_algorithms.
Require Import hmacdrbg.spec_hmac_drbg.
Require Import hmacdrbg.spec_hmac_drbg_pure_lemmas.
Require Import hmacdrbg.HMAC_DRBG_common_lemmas.

Definition my_fold_right {A B} (f : B -> A -> A) (a : A):=
fix my_fold_right (l : list B) : A :=
  match l with
  | [] => a
  | b :: t => f b (my_fold_right t)
  end.
Lemma my_fold_right_eq {A B} (f : B -> A -> A) a: my_fold_right f a = fold_right f a.
Proof. extensionality l. induction l; auto. Qed.


Lemma FRZL_ax' ps: FRZL ps = my_fold_right sepcon emp ps.
Proof. rewrite FRZL_ax. rewrite my_fold_right_eq. trivial. Qed.

(*Tactic requires the resulting goal to be normalized manually.*)
Ltac my_thaw' name :=
  rewrite (FRZL_ax' name); unfold name, abbreviate; clear name.

(*add simplification of the list operations inside the freezer,
   flatten the sepcon, and eliminate the emp term*)
Ltac my_thaw name :=
  my_thaw' name; simpl Z.to_nat; unfold my_delete_nth, my_nth, my_fold_right;
  repeat flatten_sepcon_in_SEP; repeat flatten_emp.

Lemma isptrD v: isptr v -> exists b ofs, v = Vptr b ofs.
Proof. intros. destruct v; try contradiction. eexists; eexists; reflexivity. Qed.

Lemma reseed_REST: forall (Espec : OracleKind) (contents : list byte) additional (sha: share) add_len ctx
  (md_ctx': mdstate) reseed_counter' entropy_len' prediction_resistance' reseed_interval'
  key (V: list byte) reseed_counter entropy_len prediction_resistance reseed_interval gv
  info_contents (s : ENTROPY.stream)
  seed
  (XH : 0 <= add_len <= Int.max_unsigned)
  (XH0 : Zlength V = 32)
  (XH1 : add_len = Zlength contents)
  (contents' : list byte)
  (Heqcontents' : contents' = contents_with_add additional add_len contents)
  (ELc' : 0 < entropy_len + Zlength contents' (* <= 384*))
  (XH6 : Vint (Int.repr reseed_counter) = reseed_counter')
  (XH7 : Vint (Int.repr entropy_len) = entropy_len')
  (XH8 : Vint (Int.repr reseed_interval) = reseed_interval')
  (XH9 : bool2val prediction_resistance = prediction_resistance')
  (PNadditional : is_pointer_or_null additional)
  (Pctx : isptr ctx) (shc: share)
  (ELnonneg : 0 <= entropy_len)
  (ZLc' : Zlength contents' = 0 \/ Zlength contents' = Zlength contents)
  (Hfield : field_compatible (tarray tuchar 384) [] seed)
  (AL256 : (add_len >? 256) = false)
  (EAL384 : (entropy_len + add_len >? 384) = false)
  (entropy_bytes : list byte)
  (s0 : ENTROPY.stream)
  (Heqentropy_result : ENTROPY.success entropy_bytes s0 = ENTROPY.get_bytes (Z.to_nat entropy_len) s)
  (Hsha: readable_share sha)
  (Hshc: writable_share shc),
@semax hmac_drbg_compspecs.CompSpecs Espec
  (func_tycontext f_mbedtls_hmac_drbg_reseed HmacDrbgVarSpecs
        HmacDrbgFunSpecs nil)
  (PROP ( )
   LOCAL (temp _entropy_len (Vint (Int.repr entropy_len));
   lvar _seed (tarray tuchar 384) seed; gvars gv; temp _ctx ctx; temp _additional additional;
   temp _len (Vint (Int.repr add_len)))
   SEP (Stream (get_stream_result (get_entropy 0 entropy_len entropy_len false s));
   data_at Tsh (tarray tuchar entropy_len) (map Vubyte entropy_bytes) seed;
   data_at Tsh (tarray tuchar (384 - entropy_len))
     (repeat (Vint Int.zero) (Z.to_nat (384 - entropy_len)))
     (offset_val entropy_len seed);
   da_emp sha (tarray tuchar add_len) (map Vubyte contents) additional;
   md_full key md_ctx';
   data_at shc t_struct_mbedtls_md_info info_contents
     (hmac256drbgstate_md_info_pointer
        (md_ctx',
        (map Vubyte V, (reseed_counter', (entropy_len', (prediction_resistance', reseed_interval'))))));
   spec_sha.K_vector gv;
   data_at shc t_struct_hmac256drbg_context_st
     (md_ctx',
     (map Vubyte V, (reseed_counter', (entropy_len', (prediction_resistance', reseed_interval')))))
     ctx))
  (Ssequence (Sset _seedlen (Etempvar _entropy_len tuint))
     (Ssequence
        (Ssequence
           (Sifthenelse
              (Ebinop Cop.One (Etempvar _additional (tptr tuchar))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
              (Sset _t'3
                 (Ecast
                    (Ebinop Cop.One (Etempvar _len tuint) (Econst_int (Int.repr 0) tint) tint)
                    tbool)) (Sset _t'3 (Econst_int (Int.repr 0) tint)))
           (Sifthenelse (Etempvar _t'3 tint)
              (Ssequence
                 (Scall None
                    (Evar _memcpy
                       (Tfunction [tptr tvoid; tptr tvoid; tuint]
                          (tptr tvoid) cc_default))
                    [Ebinop Oadd (Evar _seed (tarray tuchar 384))
                       (Etempvar _seedlen tuint) (tptr tuchar);
                    Etempvar _additional (tptr tuchar); Etempvar _len tuint])
                 (Sset _seedlen
                    (Ebinop Oadd (Etempvar _seedlen tuint) (Etempvar _len tuint) tuint)))
              Sskip))
        (Ssequence
           (Scall None
              (Evar _mbedtls_hmac_drbg_update
                 (Tfunction [tptr (Tstruct _mbedtls_hmac_drbg_context noattr);
                             tptr tuchar; tuint] tvoid cc_default))
              [Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr));
              Evar _seed (tarray tuchar 384); Etempvar _seedlen tuint])
           (Ssequence
              (Sassign
                 (Efield
                    (Ederef
                       (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                       (Tstruct _mbedtls_hmac_drbg_context noattr)) _reseed_counter tint)
                 (Econst_int (Int.repr 1) tint))
              (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))
 (frame_ret_assert
     (function_body_ret_assert tint
       (EX x : val,
         (PROP ( )
          LOCAL (temp ret_temp x)
          SEP (reseedPOST x contents additional sha add_len s
                 (HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance reseed_interval) ctx shc
                 info_contents gv
                 (md_ctx',
                 (map Vubyte V, (reseed_counter', (entropy_len', (prediction_resistance', reseed_interval')))))))))
     (stackframe_of f_mbedtls_hmac_drbg_reseed)).
Proof.
  intros.
  assert (ZLbytes: Zlength entropy_bytes = entropy_len).
    { eapply get_bytes_Zlength. lia. eassumption. }
  apply Zgt_is_gt_bool_f in EAL384.
  abbreviate_semax.
  freeze [0;(*2;*)4;5;6;7] FR6. freeze [1;2] SEED.

  replace_SEP 0 (data_at Tsh (tarray tuchar 384)
         ((map Vubyte entropy_bytes) ++ (repeat (Vint Int.zero) (Z.to_nat (384 - entropy_len)))) seed).
  {
    entailer!. thaw SEED; clear FR6. (*subst entropy_len.*) rewrite ?sepcon_emp.
    apply derives_refl'. symmetry.
    apply data_at_complete_split; repeat rewrite Zlength_map;
    try rewrite (*Hentropy_bytes_length,*) Zlength_repeat; try rewrite Zplus_minus; trivial; lia.
  }

  (* seedlen = entropy_len; *)
  clear SEED. freeze [0;1] FR7.
  forward.
(*  remember (if eq_dec additional nullval then false else if eq_dec add_len 0 then false else true) as non_empty_additional.*)
  remember (andb (negb (eq_dec additional nullval)) (negb (eq_dec add_len 0))) as non_empty_additional.

  forward_if (
      PROP  ()
      LOCAL  (temp _seedlen (Vint (Int.repr (entropy_len)));
      temp _entropy_len (Vint (Int.repr entropy_len));
      lvar _seed (tarray tuchar 384) seed; temp _ctx ctx;
      temp _additional additional; temp _len (Vint (Int.repr add_len));
      temp _t'3 (bool2val non_empty_additional);
      gvars gv)
      SEP  (FRZL FR7; da_emp sha (tarray tuchar add_len) (map Vubyte contents) additional)).
  { destruct additional; simpl in PNadditional; try contradiction.
    + subst i. rewrite da_emp_null. entailer. reflexivity.
    + rewrite da_emp_ptr. normalize.
      eapply denote_tc_test_eq_split; auto 50 with valid_pointer. }
  { (*nonnull additional*)
    destruct additional; simpl in PNadditional; try contradiction. subst i. elim H; trivial. clear H.
    forward. entailer!.
 (* all this stuff was needed in Coq 8.16 and before? 
     simpl.
    destruct (EqDec_Z (Zlength contents) 0).
    + rewrite e. simpl. reflexivity.
    + simpl in *.
        rewrite Int.eq_false; simpl. reflexivity.
        contradict n.
        apply repr_inj_unsigned; auto. lia.
*)
  }
  { (*nullval additional*)
    rewrite H in *.
    forward. entailer!.
  }
  thaw FR7.
(*  freeze [1;2] FR8.*) (*my_thaw FR6.*)
  forward_if (
      PROP  ()
      LOCAL  (temp _seedlen (Vint (Int.repr (entropy_len + Zlength contents')));
      temp _entropy_len (Vint (Int.repr entropy_len));
      lvar _seed (tarray tuchar 384) seed; temp _ctx ctx;
      temp _additional additional; temp _len (Vint (Int.repr add_len));
      gvars gv)
      SEP (data_at Tsh (tarray tuchar 384)
         (map Vubyte entropy_bytes ++ (map Vubyte (*contents*)contents') ++
          repeat (Vint Int.zero) (Z.to_nat (384 - entropy_len - Zlength (*contents*)contents'))) seed;
           (*FRZL FR8*)FRZL FR6;
       da_emp sha (tarray tuchar add_len) (map Vubyte contents) additional)).
  + rewrite H in Heqnon_empty_additional. rename H into NEA.
    destruct additional; simpl in PNadditional; try contradiction.
    - subst i; simpl in *; discriminate.
    - destruct (eq_dec add_len 0); try discriminate.
      subst non_empty_additional; clear Heqnon_empty_additional.
    rename b into bb. rename i into ii.
    rewrite da_emp_ptr. Intros. rename H into addlen_pos.
    assert (contents' = contents).
    { subst contents'. unfold contents_with_add. simpl.
        destruct (EqDec_Z add_len 0). lia. reflexivity. }
    clear Heqcontents'; subst contents'. clear ZLc'.
    replace_SEP 0 ((data_at Tsh (tarray tuchar entropy_len)
         (map Vubyte entropy_bytes) seed) * (data_at Tsh (tarray tuchar (384 - entropy_len))
         (repeat (Vint Int.zero) (Z.to_nat (384 - entropy_len))) (offset_val entropy_len seed))).
    {
      entailer!.
      apply derives_refl'; apply data_at_complete_split; trivial; try lia.
      rewrite Zlength_app in H0; rewrite H0; trivial.
      repeat rewrite Zlength_map; trivial.
      rewrite Zlength_repeat; lia.
    }
    flatten_sepcon_in_SEP. rewrite data_at_isptr with (p:=seed); Intros.
    apply isptrD in Pseed; destruct Pseed as [b [i SEED]]; rewrite SEED in *.
    change (offset_val entropy_len (Vptr b i)) with (Vptr b (Ptrofs.add i (Ptrofs.repr entropy_len))).
    assert_PROP (field_compatible (Tarray tuchar (384 - entropy_len) noattr)
          [] (Vptr b (Ptrofs.add i (Ptrofs.repr entropy_len)))) as FC_el by entailer!.
    simpl in *.
    replace_SEP 1 (
      (data_at Tsh (tarray tuchar (Zlength contents))
         (repeat (Vint Int.zero) (Z.to_nat (Zlength contents))) (Vptr b (Ptrofs.add i (Ptrofs.repr entropy_len)))) *
      (data_at Tsh (tarray tuchar (384 - entropy_len - Zlength contents))
         (repeat (Vint Int.zero) (Z.to_nat (384 - entropy_len - Zlength contents))) (offset_val (Zlength contents) (Vptr b (Ptrofs.add i (Ptrofs.repr entropy_len)))))).
    { 
      remember (Vptr b (Ptrofs.add i (Ptrofs.repr entropy_len))) as seed'.
      clear Heqseed'.
      (*entailer!*) go_lower.
      apply derives_refl'.
      apply data_at_complete_split; try rewrite Zlength_repeat; try lia; auto.
      + rewrite Zlength_repeat.
        replace (Zlength contents + (384 - entropy_len - Zlength contents)) with (384 - entropy_len); trivial; lia.
        lia.
      + rewrite <- repeat_app, <- Z2Nat.inj_add.
        replace (Zlength contents + (384 - entropy_len - Zlength contents)) with (384 - entropy_len); trivial; lia.
        lia. lia.
    }

    flatten_sepcon_in_SEP.
    replace_SEP 1 (memory_block Tsh (Zlength contents) (Vptr b (Ptrofs.add i (Ptrofs.repr entropy_len)))).
    { entailer!. replace (Zlength contents) with (sizeof (*cenv_cs*) (tarray tuchar (Zlength contents))) at 2.
      apply data_at_memory_block. simpl. rewrite Zmax0r; lia.
    }
    forward_call ((sha, Tsh), (Vptr b (Ptrofs.add i (Ptrofs.repr entropy_len))), (*additional*)Vptr bb ii, Zlength contents, map Int.repr (map Byte.unsigned contents)).
    {
      (* match up function parameter *)
      rewrite XH1; simpl. normalize.
    }
    {
      (* match up SEP clauses *)
      (*change (@data_at spec_sha.CompSpecs Tsh (tarray tuchar (@Zlength Z contents))
         (@map int val Vint (@map Z int Int.repr contents)) additional) with (@data_at hmac_drbg_compspecs.CompSpecs Tsh (tarray tuchar (@Zlength Z contents))
         (@map int val Vint (@map Z int Int.repr contents)) additional).*)
      cancel. my_thaw FR6.
      replace (map Vint (map Int.repr (map Byte.unsigned contents))) 
       with (map Vubyte contents).
      rewrite XH1; cancel.
      unfold Vubyte. rewrite !map_map. reflexivity.
    }
    (*Intros memcpy_vret. subst memcpy_vret.*)
    forward.
    rewrite XH1, SEED.
    go_lower. simpl. normalize.
    apply andp_right. apply prop_right. repeat split; auto.


    thaw FR6. rewrite (*H1,*) da_emp_ptr. normalize.
    apply andp_right. apply prop_right. simpl. (*specialize (Zlength_nonneg contents).*) subst add_len; lia.
    cancel.

    erewrite data_at_complete_split with
     (A:=map Vubyte entropy_bytes)
     (p:=Vptr b i)(*(offset:=entropy_len)*)
     (AB:= (map Vubyte entropy_bytes ++
       map Vubyte contents ++
       repeat (Vbyte Byte.zero) (Z.to_nat (384 - entropy_len - Zlength contents)))).
    7: solve[reflexivity].
    cancel.
    6: solve[reflexivity].
    3: solve [repeat rewrite Zlength_map; lia].

    3: solve [reflexivity].
    3: solve [rewrite Zlength_app, Zlength_repeat; repeat rewrite Zlength_map; try lia].

    2:{ rewrite Zlength_app, (* <- H17, *) Zlength_repeat; try lia.
             repeat rewrite Zlength_map. rewrite ZLbytes(*, H2*).
             assert (X: entropy_len + (Zlength contents + (384 - entropy_len - Zlength contents)) = 384) by lia.
             rewrite X; assumption.
    }
    rewrite Zlength_app; repeat rewrite Zlength_map; rewrite Zlength_repeat.
    assert (X: Zlength contents + (384 - entropy_len - Zlength contents) = 384 - entropy_len) by lia.
    rewrite X.
    erewrite data_at_complete_split with (AB:=map Vubyte contents ++
       repeat (Vubyte Byte.zero) (Z.to_nat (384 - entropy_len - Zlength contents)))
      (p:=(Vptr b (Ptrofs.add i (Ptrofs.repr entropy_len))))
      (A:= map Vubyte contents).
    7: reflexivity. 3: reflexivity. 5: reflexivity.
    3: reflexivity. 3: solve [rewrite Zlength_repeat; repeat rewrite Zlength_map; try lia].

    unfold offset_val. rewrite Ptrofs.add_assoc, ptrofs_add_repr. repeat rewrite Zlength_map. cancel. (*apply derives_refl.*)
    repeat rewrite Zlength_map. rewrite Zlength_repeat; try lia.
    unfold Vubyte. rewrite !map_map. cancel.
    rewrite Zlength_repeat; repeat rewrite Zlength_map; try lia. rewrite X; assumption.

    lia.

  + rewrite H in Heqnon_empty_additional; clear H.
    forward.
    go_lower. simpl. normalize.
    assert (contents' = nil).
    { subst contents'. unfold contents_with_add.
      destruct (eq_dec add_len 0); simpl in *.
      + rewrite e in *. rewrite andb_false_r; trivial.
      + destruct (EqDec_val additional nullval); simpl in *; trivial; discriminate. }
    clear Heqcontents'; subst contents'.
    rewrite Zlength_nil, Zplus_0_r.
    apply andp_right.
    apply prop_right. repeat split; trivial.
    rewrite map_nil. rewrite app_nil_l, Zminus_0_r. cancel.

  + (*continuation after conditional*)

  replace_SEP 0 (
    (data_at Tsh (tarray tuchar (entropy_len + Zlength contents')) (map Vubyte entropy_bytes ++
            map Vubyte contents') seed) *
    (data_at Tsh (tarray tuchar (384 - (entropy_len + Zlength contents'))) (repeat (Vbyte Byte.zero) (Z.to_nat (384 - entropy_len - Zlength contents'))) 
        (offset_val (entropy_len + Zlength contents') seed))
      ).
  {
    clear Heqcontents'.
    rewrite app_assoc.
    entailer!.
    autorewrite with sublist in H0.
    apply derives_refl'.
    apply data_at_complete_split; try list_solve.
  }
  flatten_sepcon_in_SEP.

  rewrite <- map_app.
  rewrite <- map_map.
  thaw FR6.
  rewrite data_at_isptr with (p:=seed). Intros.

  (*mbedtls_hmac_drbg_update( ctx, seed, seedlen )*)
  freeze [1;2;7] FR9.
  remember (entropy_len + Zlength contents') as ll.
  repeat rewrite Zlength_map in Hentropy_bytes_length.
  forward_call (entropy_bytes ++ contents', seed, Tsh, ll,
                ctx, shc,
                (md_ctx',
                 (map Vubyte V,
                 (Vint (Int.repr reseed_counter),
                 (Vint (Int.repr entropy_len),
                 (bool2val prediction_resistance, Vint (Int.repr reseed_interval)))))),
                (HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance reseed_interval),
                info_contents, gv).
  {
    (* prove the SEP clauses match up *)
    destruct seed; simpl in Pseed; try contradiction.
    rewrite da_emp_ptr.
    rewrite Zlength_app.
    rewrite ZLbytes. simpl.
    normalize. apply andp_right. apply prop_right. repeat split; trivial.
      { lia. }
    rewrite <- Heqll, XH6, XH7, XH8, XH9. rewrite map_id. cancel.
  }
  {
    (* prove the PROP clauses *)
    left; rewrite Zlength_app, ZLbytes; trivial.
  }
  unfold hmac256drbgabs_common_mpreds.
  repeat flatten_sepcon_in_SEP.
  thaw FR9.
  freeze [1;2;4;6;7] FR10.
  freeze [0;1] FR11.
  gather_SEP 1 2.
  replace_SEP 0 (data_at Tsh (tarray tuchar 384) ((map Vubyte entropy_bytes)
        ++ (map Vubyte contents' ++
       repeat (Vbyte Byte.zero) (Z.to_nat (384 - entropy_len - Zlength contents')))) seed).
  { rewrite app_assoc.
    rewrite map_app.
(*    replace (map (fun x : Z => Vint (Int.repr x)) contents') with (map Vint (map Int.repr contents')) by (rewrite map_map; auto). *)
    clear Heqcontents'.
    rewrite Zlength_app, ZLbytes.
    entailer!.
    destruct seed; simpl in Pseed; try contradiction.
    rewrite da_emp_ptr. Intros.
    apply derives_refl'; symmetry; apply data_at_complete_split;
     repeat rewrite Zlength_repeat; try lia; auto; try rewrite Zlength_app;
     try rewrite ZLbytes; repeat rewrite Zlength_map; auto.
     replace (Zlength entropy_bytes + Zlength contents' +
      (384 - Zlength entropy_bytes - Zlength contents')) with 384 by lia.
     assumption.
  }
  (* ctx->reseed_counter = 1; *)
  thaw FR11.
  freeze [0;1] FR12. rewrite XH6, XH7, XH8, XH9.
  unfold hmac256drbgabs_to_state. simpl.
  remember (HMAC256_DRBG_functional_prog.HMAC256_DRBG_update
            (contents_with_add seed ll
               (entropy_bytes ++ contents')) key V).
  destruct p.
  simpl. normalize. rewrite XH6, XH7, XH8, XH9. deadvars!.
  subst contents'.
  Time forward.

  (* return 0 *)
  idtac "Timing a forward (goal: 5secs)". Time forward. (*5 secs*)
  Exists (Vint (Int.repr 0)). normalize.
  entailer!.

  assert (ZL1: Zlength (contents_with_add additional (Zlength contents) contents) >? 256 = false).
  { clear - ZLc' AL256. destruct ZLc' as [ZLc' | ZLc']; rewrite ZLc'; trivial. }

  apply Zgt_is_gt_bool_f in AL256.
  assert (Z: (zlt 256 (Zlength contents)
       || zlt 384
            (hmac256drbgabs_entropy_len
               (HMAC256DRBGabs key V reseed_counter (Zlength entropy_bytes) prediction_resistance
                  reseed_interval) + Zlength contents))%bool = false).
  { destruct (zlt 256 (Zlength contents)); simpl; try lia.
    destruct (zlt 384 (Zlength entropy_bytes + Zlength contents)); simpl; trivial. lia.
  }
  unfold reseedPOST. rewrite Z.
  entailer!.
  { unfold return_value_relate_result. simpl.
    rewrite andb_negb_r, ZL1.
    unfold get_entropy. rewrite <- Heqentropy_result. trivial. }
  simpl.
  rewrite andb_negb_r, ZL1.
  unfold get_entropy. rewrite <- Heqentropy_result.
  remember (HMAC_DRBG_update HMAC256_functional_prog.HMAC256
              (entropy_bytes ++ contents_with_add additional (Zlength contents) contents) key V) as q.
  destruct q. normalize.
  thaw FR12. thaw FR10.
  simpl. rewrite <- Heqp.
  unfold  hmac256drbgabs_common_mpreds.
  unfold get_entropy; rewrite <- Heqentropy_result. simpl.
  assert (l2 = l0). {
    unfold HMAC256_DRBG_functional_prog.HMAC256_DRBG_update in Heqp.
    destruct seed; simpl in Pseed; try contradiction.
    unfold contents_with_add in Heqp at 1. simpl in Heqp.
    destruct (EqDec_Z (Zlength entropy_bytes +
                 Zlength (contents_with_add additional (Zlength contents) contents)) 0); simpl in Heqp.
    specialize (Zlength_nonneg (contents_with_add additional (Zlength contents) contents)).
    intros; lia.
    rewrite <- Heqp in *. inv Heqq; auto.
  }
  subst l2. 
  set (sd := _ ++ _ ++ _).
  (* THE NEXT LINE (sep_apply) should not be necessary!  But without it,
     the "cancel" part of entailer!! blows up.  *)
  sep_apply (data_at_data_at_ Tsh (tarray tuchar 384) sd seed).
  entailer!!.
  unfold HMAC256_DRBG_functional_prog.HMAC256_DRBG_update in Heqp.
  destruct seed; simpl in Pseed; try contradiction.
  unfold contents_with_add in Heqp at 1. simpl in Heqp.
  destruct (EqDec_Z (Zlength entropy_bytes +
                 Zlength (contents_with_add additional (Zlength contents) contents)) 0); simpl in Heqp.
  specialize (Zlength_nonneg (contents_with_add additional (Zlength contents) contents)).
  intros; lia.
  rewrite <- Heqp in *. inv Heqq. 
  idtac "Timing the Qed of REST (goal: 25secs)". 
  cancel.
Time Qed. (*Coq 8.10.1: 3s;
          Coq8.6 May23rd: 23s
          Feb 23 2017: 216.218 secs (135.625u,0.046s) (successful)*)
         (*was: Coq8.5pl2: 44secs*)