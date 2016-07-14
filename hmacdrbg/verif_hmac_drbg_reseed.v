Require Import floyd.proofauto.
Import ListNotations.
Local Open Scope logic.

Require Import hmacdrbg.hmac_drbg.
Require Import hmacdrbg.spec_hmac_drbg.
Require Import hmacdrbg.spec_hmac_drbg_pure_lemmas.
Require Import hmacdrbg.DRBG_functions.
Require Import hmacdrbg.HMAC_DRBG_algorithms.
Require Import hmacdrbg.entropy.
Require Import hmacdrbg.entropy_lemmas.
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
Proof. rewrite FRZL_ax. rewrite <- my_fold_right_eq. trivial. Qed.

(*Tactic requires the resulting goal to be normalized manually.*)
Ltac my_thaw' name :=
  rewrite (FRZL_ax' name); unfold name, abbreviate; clear name.

(*add simplification of the list operations inside the freezer,
   flatten the sepcon, and eliminate the emp term*)
Ltac my_thaw name :=
  my_thaw' name; simpl nat_of_Z; unfold my_delete_nth, my_nth, my_fold_right; 
  repeat flatten_sepcon_in_SEP; repeat flatten_emp.

Lemma isptrD v: isptr v -> exists b ofs, v = Vptr b ofs.
Proof. intros. destruct v; try contradiction. eexists; eexists; reflexivity. Qed. 

Lemma body_hmac_drbg_reseed_TAIL Espec contents additional add_len ctx md_ctx' V' reseed_counter' entropy_len'
       prediction_resistance' reseed_interval' key V reseed_counter entropy_len
       prediction_resistance reseed_interval kv info_contents (s : ENTROPY.stream)
       (*Delta_specs := abbreviate : PTree.t funspec*)
       (seed : val): forall
(H : 0 <= Zlength contents <= Int.max_unsigned)
(H0 : Zlength
       (hmac256drbgabs_value
          (HMAC256DRBGabs key V reseed_counter entropy_len
             prediction_resistance reseed_interval)) =
     Z.of_nat HMAC256_functional_prog.SHA256.DigestLength)
(H1 : add_len = Zlength contents)
(H2 : entropy_len = 32)
(H3 : Forall general_lemmas.isbyteZ
       (hmac256drbgabs_value
          (HMAC256DRBGabs key V reseed_counter entropy_len
             prediction_resistance reseed_interval)))
(H4 : Forall general_lemmas.isbyteZ contents)
(H5 : map Vint (map Int.repr V) = V')
(H6 : Vint (Int.repr reseed_counter) = reseed_counter')
(H7 : Vint (Int.repr entropy_len) = entropy_len')
(H8 : Vint (Int.repr reseed_interval) = reseed_interval')
(H9 : Val.of_bool prediction_resistance = prediction_resistance')
(H10 : 256 >= Zlength contents)
(Hfield : field_compatible (tarray tuchar 384) [] seed)
(vret : val)
(entropy_bytes : list Z)
(s0 : ENTROPY.stream)
(ENT : return_value_relate_result (ENTROPY.success entropy_bytes s0) vret)
(Heqentropy_result : ENTROPY.success entropy_bytes s0 =
                    ENTROPY.get_bytes (Z.to_nat entropy_len) s)
(Hentropy_bytes_length : Zlength (map Vint (map Int.repr entropy_bytes)) = 32),
@semax hmac_drbg_compspecs.CompSpecs Espec
  (initialized_list [_entropy_len; 232%positive; 231%positive]
     (func_tycontext f_mbedtls_hmac_drbg_reseed HmacDrbgVarSpecs
        HmacDrbgFunSpecs))
  (PROP  (vret = Vzero)
   LOCAL  (temp 232%positive vret;
   temp _entropy_len (Vint (Int.repr entropy_len));
   lvar _seed (tarray tuchar 384) seed; temp _ctx ctx;
   temp _additional additional; temp _len (Vint (Int.repr add_len));
   gvar sha._K256 kv)
   SEP 
   (Stream
      (get_stream_result (get_entropy 0 entropy_len entropy_len false s));
   data_at Tsh (tarray tuchar entropy_len)
     (map Vint (map Int.repr entropy_bytes)) seed;
   data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
     additional; md_full key md_ctx';
   data_at Tsh t_struct_mbedtls_md_info info_contents
     (hmac256drbgstate_md_info_pointer
        (md_ctx',
        (V',
        (reseed_counter',
        (entropy_len', (prediction_resistance', reseed_interval'))))));
   spec_sha.K_vector kv;
   data_at Tsh t_struct_hmac256drbg_context_st
     (md_ctx',
     (V',
     (reseed_counter',
     (entropy_len', (prediction_resistance', reseed_interval'))))) ctx;
   data_at Tsh (tarray tuchar (384 - entropy_len))
     (list_repeat (Z.to_nat (384 - entropy_len)) (Vint Int.zero))
     (offset_val entropy_len seed)))
  (Ssequence (Sset _seedlen (Etempvar _entropy_len tuint))
     (Ssequence
        (Ssequence
           (Sifthenelse
              (Ebinop One (Etempvar _additional (tptr tuchar))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
              (Sset 233%positive
                 (Ecast
                    (Ebinop One (Etempvar _len tuint)
                       (Econst_int (Int.repr 0) tint) tint) tbool))
              (Sset 233%positive (Econst_int (Int.repr 0) tint)))
           (Sifthenelse (Etempvar 233%positive tint)
              (Ssequence
                 (Scall None
                    (Evar _memcpy
                       (Tfunction
                          (Tcons (tptr tvoid)
                             (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                          (tptr tvoid) cc_default))
                    [Ebinop Oadd (Evar _seed (tarray tuchar 384))
                       (Etempvar _seedlen tuint) (tptr tuchar);
                    Etempvar _additional (tptr tuchar); Etempvar _len tuint])
                 (Sset _seedlen
                    (Ebinop Oadd (Etempvar _seedlen tuint)
                       (Etempvar _len tuint) tuint))) Sskip))
        (Ssequence
           (Scall None
              (Evar _mbedtls_hmac_drbg_update
                 (Tfunction
                    (Tcons (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))
                       (Tcons (tptr tuchar) (Tcons tuint Tnil))) tvoid
                    cc_default))
              [Etempvar _ctx
                 (tptr (Tstruct _mbedtls_hmac_drbg_context noattr));
              Evar _seed (tarray tuchar 384); Etempvar _seedlen tuint])
           (Ssequence
              (Sassign
                 (Efield
                    (Ederef
                       (Etempvar _ctx
                          (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                       (Tstruct _mbedtls_hmac_drbg_context noattr))
                    _reseed_counter tint) (Econst_int (Int.repr 1) tint))
              (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))
  (frame_ret_assert
     (function_body_ret_assert tint
        (EX  ret_value : val,
         PROP 
         (return_value_relate_result
            (mbedtls_HMAC256_DRBG_reseed_function s
               (HMAC256DRBGabs key V reseed_counter entropy_len
                  prediction_resistance reseed_interval) contents) ret_value)
         
         LOCAL  (temp ret_temp ret_value)
         SEP 
         (hmac256drbgabs_common_mpreds
            (hmac256drbgabs_reseed
               (HMAC256DRBGabs key V reseed_counter entropy_len
                  prediction_resistance reseed_interval) s contents)
            (md_ctx',
            (V',
            (reseed_counter',
            (entropy_len', (prediction_resistance', reseed_interval'))))) ctx
            info_contents;
         data_at Tsh (tarray tuchar add_len)
           (map Vint (map Int.repr contents)) additional;
         Stream
           (get_stream_result
              (mbedtls_HMAC256_DRBG_reseed_function s
                 (HMAC256DRBGabs key V reseed_counter entropy_len
                    prediction_resistance reseed_interval) contents));
         spec_sha.K_vector kv))%assert)
     (EX  v : val,
      local (locald_denote (lvar _seed (tarray tuchar 384) v)) &&
      `(data_at_ Tsh (tarray tuchar 384) v))%assert).
Proof.
  intros. abbreviate_semax.
  Intros.
  freeze [0;2;3;4;5;6] FR6. freeze [1;2] GATHER.
(*  gather_SEP 1 7.*)
  
  replace_SEP 0 (data_at Tsh (tarray tuchar 384)
         ((map Vint
            (map Int.repr entropy_bytes)) ++ (list_repeat (Z.to_nat (384 - entropy_len)) (Vint Int.zero))) seed).
  {
    entailer!. my_thaw GATHER; clear FR6. (*subst entropy_len.*) rewrite sepcon_emp.
    apply derives_refl'. symmetry. 
    apply data_at_complete_split; auto.
    rewrite Hentropy_bytes_length, Zlength_list_repeat; auto.
  }

  (* seedlen = entropy_len; *)
  clear GATHER. freeze [0;1] FR7.
  forward.

  remember (if eq_dec additional nullval then false else if eq_dec add_len 0 then false else true) as non_empty_additional.

  (* if additional != null *)
  forward_if (
      PROP  ()
      LOCAL  (temp _seedlen (Vint (Int.repr entropy_len));
      temp _entropy_len (Vint (Int.repr entropy_len));
      lvar _seed (tarray tuchar 384) seed; temp _ctx ctx;
      temp _additional additional; temp _len (Vint (Int.repr add_len));
(*      temp 148%positive (Val.of_bool non_empty_additional);*)
      temp 233%positive (Val.of_bool non_empty_additional);
      gvar sha._K256 kv)
      SEP  (FRZL FR7)
  ).
  {
    (* TODO this should be easy with weakly valid pointer *)
    unfold denote_tc_comparable.
    assert (Hsize_of: sizeof (*cenv_cs*) (tarray tuchar (Zlength contents)) >= 0).
    {
      pose proof (Zlength_nonneg contents).
      simpl.
      rewrite Z.mul_1_l.
      rewrite Zmax0r by omega.
      omega.
    }
    red in PNadditional. destruct additional; try contradiction.
    rewrite PNadditional. clear. apply andp_right; apply prop_right; trivial.
    apply andp_right.  apply prop_right; trivial.
    clear H11; my_thaw FR7; my_thaw FR6.
    apply sepcon_weak_valid_pointer2. 
    apply sepcon_weak_valid_pointer1. 
    apply sepcon_weak_valid_pointer2.
    apply sepcon_weak_valid_pointer1.
    apply data_at_weak_valid_ptr.
    apply top_share_nonidentity. simpl. (*rewrite H1.*) rewrite Z.max_r; omega.
  }
  { rewrite if_false in Heqnon_empty_additional; trivial.
    
    forward.
    entailer!. (*rewrite H1.*)
    unfold Int.eq. rewrite Int.unsigned_repr. rewrite Int.unsigned_repr.
        destruct (zeq (Zlength contents) 0). simpl. rewrite e; reflexivity. 
        rewrite if_false; trivial. 
        omega. omega. 
  }
  {
    forward.
    entailer!.
    (*rewrite if_true; trivial.*)
  }
  my_thaw FR7. (*my_thaw FR6.*)
  forward_if (
      PROP  ()
      LOCAL  (temp _seedlen (Vint (Int.repr (entropy_len + Zlength contents)));
      temp _entropy_len (Vint (Int.repr entropy_len));
      lvar _seed (tarray tuchar 384) seed; temp _ctx ctx;
      temp _additional additional; temp _len (Vint (Int.repr add_len));
      gvar sha._K256 kv)
      SEP (data_at Tsh (tarray tuchar 384)
         (map Vint
            (map Int.repr entropy_bytes) ++ (map Vint (map Int.repr contents)) ++
          list_repeat (Z.to_nat (384 - entropy_len - Zlength contents)) (Vint Int.zero)) seed;
           FRZL FR6)). 
  {
    rewrite H11 in Heqnon_empty_additional.
    destruct (eq_dec additional nullval); try discriminate.
    destruct (eq_dec add_len 0); try discriminate. rewrite H11. clear Heqnon_empty_additional H11 non_empty_additional.
    replace_SEP 0 ((data_at Tsh (tarray tuchar entropy_len)
         (map Vint
            (map Int.repr entropy_bytes)) seed) * (data_at Tsh (tarray tuchar (384 - entropy_len))
         (list_repeat (Z.to_nat (384 - entropy_len)) (Vint Int.zero)) (offset_val entropy_len seed))).
    {
      entailer!.
      replace (384 - 32) with 352 by omega.
      apply derives_refl'; apply data_at_complete_split; auto.
      rewrite Hentropy_bytes_length.
      auto.
    } 
    flatten_sepcon_in_SEP.
    assert_PROP (isptr seed) as Hisptr by entailer!.
    apply isptrD in Hisptr; destruct Hisptr as [b [i SEED]]; rewrite SEED in *.
    change (offset_val entropy_len (Vptr b i)) with (Vptr b (Int.add i (Int.repr entropy_len))).
    assert_PROP (field_compatible (Tarray tuchar (384 - entropy_len) noattr) 
          [] (Vptr b (Int.add i (Int.repr entropy_len)))).
    { (*rewrite (data_at_data_at' Tsh (tarray tuchar (384 - entropy_len))
        (list_repeat (Z.to_nat (384 - entropy_len)) (Vint Int.zero))
        (Vptr b (Int.add i (Int.repr entropy_len)))).*) entailer!.  } 
    replace_SEP 1 ((data_at Tsh (tarray tuchar (Zlength contents))
         (list_repeat (Z.to_nat (Zlength contents)) (Vint Int.zero)) (Vptr b (Int.add i (Int.repr entropy_len)))) * (data_at Tsh (tarray tuchar (384 - entropy_len - Zlength contents))
         (list_repeat (Z.to_nat (384 - entropy_len - Zlength contents)) (Vint Int.zero)) (offset_val (Zlength contents) (Vptr b (Int.add i (Int.repr entropy_len)))))).
    {
      subst entropy_len.
      replace (384 - 32) with 352 by omega.
      remember (Vptr b (Int.add i (Int.repr 32))) as seed'.
      clear Heqseed'.
      entailer!.
      replace (length contents) with (Z.to_nat (Zlength contents)) by
        (rewrite Zlength_correct; apply Nat2Z.id).
      apply derives_refl'; apply data_at_complete_split; repeat rewrite Zlength_list_repeat; try omega; auto.
      {
        replace (Zlength contents + (352 - Zlength contents)) with (384 - 32) by omega.
        assumption.
      }
      {
        rewrite list_repeat_app.
        rewrite <- Z2Nat.inj_add; try omega.
        replace (Zlength contents + (352 - Zlength contents)) with 352 by omega.
        reflexivity.
      }
    }
    flatten_sepcon_in_SEP.
    replace_SEP 1 (memory_block Tsh (Zlength contents) (Vptr b (Int.add i (Int.repr entropy_len)))).
    { entailer!. replace (Zlength contents) with (sizeof (*cenv_cs*) (tarray tuchar (Zlength contents))) at 2.
      apply data_at_memory_block. simpl. rewrite Zmax0r; omega.
    }
    forward_call ((Tsh, Tsh), (Vptr b (Int.add i (Int.repr entropy_len))), additional, Zlength contents, map Int.repr contents).
    {
      (* type checking *)
      red in LV.
      unfold eval_var. destruct (Map.get (ve_of rho) _seed); try contradiction.
      destruct p; destruct LV  as [LV1 LV2]; inversion LV2. subst b0 i t; simpl; trivial.
    }      
    {
      (* match up function parameter *)
      rewrite H1; simpl.
      apply prop_right; trivial.
    }
    {
      (* match up SEP clauses *)
      change (fst (Tsh, Tsh)) with Tsh;
      change (snd (Tsh, Tsh)) with Tsh.
      (*change (@data_at spec_sha.CompSpecs Tsh (tarray tuchar (@Zlength Z contents))
         (@map int val Vint (@map Z int Int.repr contents)) additional) with (@data_at hmac_drbg_compspecs.CompSpecs Tsh (tarray tuchar (@Zlength Z contents))
         (@map int val Vint (@map Z int Int.repr contents)) additional).*)
      clear POSTCONDITION. my_thaw FR6. rewrite H1; cancel.
    }(*
    {
      (* prove the PROP clauses *)
      repeat split; auto; omega.
    }*)
    (*Intros memcpy_vret. subst memcpy_vret.*)
    forward.
    change (fst (Tsh, Tsh)) with Tsh;
    change (snd (Tsh, Tsh)) with Tsh.
    (*change (@data_at spec_sha.CompSpecs Tsh (tarray tuchar (@Zlength Z contents))
         (@map int val Vint (@map Z int Int.repr contents)) additional) with (@data_at hmac_drbg_compspecs.CompSpecs Tsh (tarray tuchar (@Zlength Z contents))
         (@map int val Vint (@map Z int Int.repr contents)) additional).*)
    rewrite H1, SEED. Time entailer!. (*8.5pl2: 1230secs*) 
    my_thaw FR6. (*rewrite H1;*) cancel.
    erewrite data_at_complete_split with (A:=map Vint (map Int.repr entropy_bytes))
     (p:=Vptr b i)(*(offset:=entropy_len)*)
     (AB:= (map Vint (map Int.repr entropy_bytes) ++
       map Vint (map Int.repr contents) ++
       list_repeat (Z.to_nat (384 - 32(*entropy_len*) - Zlength contents))
         (Vint Int.zero))). 
    7: reflexivity.
    cancel.
    6: reflexivity.
    3: symmetry; assumption. 
    3: rewrite Zlength_app; rewrite Zlength_list_repeat; try reflexivity; try omega.
    3: repeat rewrite Zlength_map; omega.
    Focus 2. rewrite Zlength_app, <- H17, Zlength_list_repeat; try omega.
             repeat rewrite Zlength_map.
             assert (X: Zlength entropy_bytes + (Zlength contents + (384 - Zlength entropy_bytes - Zlength contents)) = 384) by omega.
             rewrite X; assumption.
    erewrite data_at_complete_split with (AB:=map Vint (map Int.repr contents) ++
       list_repeat (Z.to_nat (384 - 32 (*entropy_len*) - Zlength contents))
         (Vint Int.zero))
      (p:=(Vptr b (Int.add i (Int.repr 32(*entropy_len*)))))
      (A:= map Vint (map Int.repr contents)).
    7: reflexivity. 3: reflexivity. 5: reflexivity. 4: reflexivity.
    3: rewrite Zlength_list_repeat; trivial; omega.
    unfold offset_val. rewrite Int.add_assoc, add_repr.  repeat rewrite Zlength_map; apply derives_refl.
    repeat rewrite Zlength_map. rewrite Zlength_list_repeat; try omega.
    assert (X:Zlength contents + (384 - 32(*entropy_len*) - Zlength contents) = 384 - 32(*entropy_len*)) by omega.
    rewrite X; assumption. 
  }
  {
    rewrite H11 in Heqnon_empty_additional; clear H11.
    forward.
    my_thaw FR6. 
    assert_PROP (isptr additional). { Time entailer!. (*8.5pl2: 1265secs *) }
    assert_PROP (contents = []).
    {
      destruct (eq_dec additional nullval); try discriminate. rewrite e in H11.
      apply isptrD in H11. destruct H11 as [? [? HH]]; discriminate.
      destruct (eq_dec add_len 0); try discriminate.
      rewrite H1 in e. apply Zlength_nil_inv in e. apply prop_right; assumption.
    }
    apply andp_left2; rewrite H12, Zlength_nil, Zplus_0_r. 
    replace (384 - entropy_len - 0) with (384 - entropy_len) by omega.
    old_go_lower. Time entailer!. (*8.5pl2: 1240secs *) 
  }

  replace_SEP 0 (
    (data_at Tsh (tarray tuchar (entropy_len + Zlength contents)) (map Vint
            (map Int.repr entropy_bytes) ++
            map Vint (map Int.repr contents)) seed) *
    (data_at Tsh (tarray tuchar (384 - (entropy_len + Zlength contents))) (list_repeat (Z.to_nat (384 - entropy_len - Zlength contents))
            (Vint Int.zero)) (offset_val (entropy_len + Zlength contents) seed))
      ).
  {
    rewrite H2.
    replace (384 - (32 + Zlength contents)) with (352 - Zlength contents) by omega.
    replace (384 - 32) with 352 by omega.
    rewrite app_assoc.
    entailer!.
    apply derives_refl'; apply data_at_complete_split; repeat rewrite Zlength_list_repeat; try omega; auto; rewrite Zlength_app; rewrite Hentropy_bytes_length; repeat rewrite Zlength_map; auto.
    replace (32 + Zlength contents + (352 - Zlength contents)) with 384 by omega.
    assumption.
  }
  flatten_sepcon_in_SEP.

  do 2 rewrite map_map.
  rewrite <- map_app.
  rewrite <- map_map.

  forward_call ((entropy_bytes ++ contents), seed, (entropy_len + Zlength contents), ctx, (md_ctx',
        (map Vint (map Int.repr V),
        (Vint (Int.repr reseed_counter),
        (Vint (Int.repr entropy_len),
        (Val.of_bool prediction_resistance, Vint (Int.repr reseed_interval)))))), (HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance reseed_interval), kv, info_contents).
  {
    (* prove the SEP clauses match up *)
    unfold hmac256drbg_relate. rewrite H5, H6, H7, H8, H9. entailer!. my_thaw FR6. cancel. 
  }
  {
    (* prove the PROP clauses *)
    rewrite H2 in *; rewrite int_max_unsigned_eq.
    repeat split; try omega.
    { rewrite H0. reflexivity.
(*      rewrite Zlength_app.
      repeat rewrite Zlength_map in Hentropy_bytes_length. simpl.
      rewrite Hentropy_bytes_length.
      change (Z.of_nat (Z.to_nat 32)) with 32.
      reflexivity.*)
    }
    {
      rewrite Zlength_app.
      repeat rewrite Zlength_map in Hentropy_bytes_length. 
      rewrite Hentropy_bytes_length. reflexivity.
    }
    { assumption. }
    { apply isbyteZ_app; try assumption. 
      eapply get_bytes_isbyteZ; eauto. 
    }
  }
  unfold hmac256drbgabs_common_mpreds. 
  repeat flatten_sepcon_in_SEP.
  freeze [1;2;4;6;7] FR7.
  freeze [0;1] FR8.
  gather_SEP 1 2.
  replace_SEP 0 (data_at Tsh (tarray tuchar 384) ((map Vint
         (map Int.repr entropy_bytes)) ++ (map Vint (map Int.repr contents) ++
       list_repeat (Z.to_nat (384 - entropy_len - Zlength contents))
         (Vint Int.zero))) seed).
  {
    subst entropy_len.
    replace (384 - 32) with 352 by omega.
    replace (384 - (32 + Zlength contents)) with (352 - Zlength contents) by omega.
    rewrite app_assoc.
    rewrite map_map.
    rewrite map_app.
    rewrite <- map_map.
    replace (map (fun x : Z => Vint (Int.repr x)) contents) with (map Vint (map Int.repr contents)) by (rewrite map_map; auto).
    entailer!.
    apply derives_refl'; symmetry; apply data_at_complete_split; repeat rewrite Zlength_list_repeat; try omega; auto; rewrite Zlength_app; rewrite Hentropy_bytes_length; repeat rewrite Zlength_map; auto.
    replace (32 + Zlength contents + (352 - Zlength contents)) with 384 by omega.
    assumption.
  }
  
  (* ctx->reseed_counter = 1; *)
  my_thaw FR8.
  freeze [0;1] FR9. rewrite H5, H6, H7, H8, H9. 
  unfold hmac256drbgabs_to_state. simpl.
  remember (HMAC256_DRBG_functional_prog.HMAC256_DRBG_update
              (entropy_bytes ++ contents) key V).
  destruct p.  
  simpl. normalize. Time forward.
    (*Coq8.5pl2: 1118.203 secs (247.609u,0.781s)*)
    (*takes 3597secs if HMAC256_DRBG_functional_prog.HMAC256_DRBG_update is opaque*)
    (*in VST1.6, this forward takes 1968.182 secs, without allocating a single KB of memory ;-) *)
    (*Coq8.5pl1: 1100secs*)
  (* return 0 *)
  Time forward. (*8 secs*)

  my_thaw FR9. my_thaw FR7.
  unfold hmac256drbgabs_common_mpreds.
  unfold hmac256drbgabs_to_state.
  Exists seed (Vint (Int.repr 0)).
  rewrite andb_negb_r.
  assert (HcontentsLength: Zlength contents >? 256 = false).
  {
    rewrite Z.gtb_ltb.
    apply Z.ltb_nlt.
    omega.
  }
  rewrite HcontentsLength.
  unfold HMAC_DRBG_update.
  idtac.
  replace (map (fun x : Z => Vint (Int.repr x)) contents) with (map Vint (map Int.repr contents)) by (rewrite map_map; auto).
  unfold hmac256drbg_relate.
  unfold get_stream_result.
  unfold entropy.get_entropy.
  rewrite <- Heqentropy_result.
  assert (Hnonempty_seed: exists hdSeed tlSeed, (entropy_bytes ++ contents) = hdSeed::tlSeed).
  {
    remember (entropy_bytes ++ contents) as seedContents.
    destruct seedContents as [|hdSeed tlSeed].
    {
      (* this case can't be true. case: seedContents = [] *)
(*      simpl in H2; subst entropy_len.*)
      assert (contra: Zlength (entropy_bytes ++ contents) = 0) by (rewrite <- HeqseedContents; reflexivity).
      rewrite Zlength_app in contra.
      repeat rewrite Zlength_map in Hentropy_bytes_length; rewrite Hentropy_bytes_length in contra.
      omega.
    }
    exists hdSeed. exists tlSeed.
    reflexivity.
  }
  destruct Hnonempty_seed as [hdSeed [tlSeed Hnonempty_seed]];
  rewrite Hnonempty_seed in *.
  unfold hmac256drbgabs_hmac_drbg_update. rewrite <- Heqp.
  unfold HMAC256_DRBG_functional_prog.HMAC256_DRBG_update, HMAC_DRBG_update in Heqp.
  Time inv Heqp. (*6secs*)
  Time entailer!. (*28secs; Coq8.5pl2: 1173secs Coq8.5pl1: 1100secs*) apply derives_refl.
Time Qed. (*Coq8.5pl2: 64secs*)

Lemma body_hmac_drbg_reseed: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs 
       f_mbedtls_hmac_drbg_reseed hmac_drbg_reseed_spec.
Proof.
  start_function.
  rename lvar0 into seed.
  destruct initial_state_abs.
  destruct initial_state as [md_ctx' [V' [reseed_counter' [entropy_len' [prediction_resistance' reseed_interval']]]]].
  unfold hmac256drbg_relate.
  Intros.

  (* entropy_len = ctx->entropy_len *)
  simpl in H2.
  freeze [0;1;3;4;5;6] FR1.
  forward. (*{ rewrite <- H7; entailer!. }*)

  remember (if zlt 256 add_len then true else false) as add_len_too_high.

  (* if (len > MBEDTLS_HMAC_DRBG_MAX_INPUT ||
        entropy_len + len > MBEDTLS_HMAC_DRBG_MAX_SEED_INPUT) *)
  freeze [0;1] FR2.
  forward_if (PROP  ()
      LOCAL  (temp _entropy_len (Vint (Int.repr entropy_len));
      lvar _seed (tarray tuchar 384) seed; temp _ctx ctx;
      temp _additional additional; temp _len (Vint (Int.repr add_len));
(*      temp 146%positive (Val.of_bool add_len_too_high);*)
      temp 231%positive (Val.of_bool add_len_too_high);
      gvar sha._K256 kv)
      SEP  (FRZL FR2)). 
  {
    rewrite zlt_true in Heqadd_len_too_high by assumption.
    forward.
    entailer!.    
  }
  {
    rewrite zlt_false in Heqadd_len_too_high by assumption.
    forward.
    entailer!. clear FR2 FR1.
      subst. 
      unfold Int.ltu; simpl.
      rewrite add_repr.
      destruct (zlt (Int.unsigned (Int.repr 384))
                    (Int.unsigned (Int.repr (32 + Zlength contents)))); try reflexivity.
      exfalso. 
      rewrite Int.unsigned_repr_eq in l.
      rewrite Zmod_small in l by auto.
      rewrite Int.unsigned_repr_eq, Zmod_small in l.
      omega.
      rewrite hmac_pure_lemmas.IntModulus32.
      change (2 ^ 32) with 4294967296.
      omega.
  }

  forward_if (PROP  (add_len_too_high = false)
      LOCAL  (temp _entropy_len (Vint (Int.repr entropy_len));
      lvar _seed (tarray tuchar 384) seed; temp _ctx ctx;
      temp _additional additional; temp _len (Vint (Int.repr add_len));
      gvar sha._K256 kv)
      SEP (FRZL FR2)
  ).
  { rewrite H10 in *. if_tac in Heqadd_len_too_high; try discriminate.
    rewrite H1 in *. clear Heqadd_len_too_high H10 H1.
    forward.
    unfold hmac256drbgabs_common_mpreds, get_stream_result, hmac256drbg_relate.
    Exists seed (Vint (Int.neg (Int.repr 5))).
    rewrite andb_negb_r. thaw FR2; thaw FR1.
    destruct (zlt 256 (Zlength contents)). 2: omega.
    rewrite Z.gtb_ltb.
    assert (Hlt: 256 <? Zlength contents = true) by (apply Z.ltb_lt; assumption).
    rewrite Hlt. simpl.
    unfold hmac256drbgabs_to_state.
    Time entailer!. (*Coq8.5pl2: 1220secs*)
  }
  {
    forward.
    entailer!.
  }
  Intros. rewrite H10 in *; clear H10 add_len_too_high.
  if_tac in Heqadd_len_too_high; try discriminate. 
  rewrite H1 in *; clear Heqadd_len_too_high.

  (* memset( seed, 0, MBEDTLS_HMAC_DRBG_MAX_SEED_INPUT ); *)
  forward_call (Tsh, seed, 384, Int.zero).
  { 
   my_thaw FR2. my_thaw FR1.
    rewrite data_at__memory_block.
    change (sizeof (*cenv_cs*) (tarray tuchar 384)) with 384. 
    Time entailer!. (*Coq8.5pl2:1257 secs; Coq8.5pl1:1100 secs*)
  }

  freeze [1;2;3;4;5;6] FR3.
  assert_PROP (field_compatible (tarray tuchar 384) [] seed) as Hfield by entailer!.
  replace_SEP 1 ((data_at Tsh (tarray tuchar entropy_len)
         (list_repeat (Z.to_nat entropy_len) (Vint Int.zero)) seed) * (data_at Tsh (tarray tuchar (384 - entropy_len))
         (list_repeat (Z.to_nat (384 - entropy_len)) (Vint Int.zero)) (offset_val entropy_len seed))).
  {
    subst entropy_len.
    erewrite <- data_at_complete_split with (length:=384)(AB:=list_repeat (Z.to_nat 384) (Vint Int.zero)); trivial.
    go_lower. apply derives_refl. 
  }
  flatten_sepcon_in_SEP.
  
  replace_SEP 1 (memory_block Tsh entropy_len seed).
  {
    subst entropy_len.
    go_lower. apply data_at_memory_block.
  }

  (* get_entropy(seed, entropy_len ) *)
  my_thaw FR3. freeze [0;1;2;4;5;7] FR4.
  forward_call (Tsh, s, seed, entropy_len).
  { clear Frame FR4.
    subst entropy_len.
    auto.
  }
  Intros vret. rename H11 into ENT.

  (* if( get_entropy(seed, entropy_len ) != 0 ) *)
  freeze [0;1;2] FR5.
  forward_if (
      PROP  (vret=Vzero)
      LOCAL  (temp 232%positive vret;
      temp _entropy_len (Vint (Int.repr entropy_len));
      lvar _seed (tarray tuchar 384) seed; temp _ctx ctx;
      temp _additional additional; temp _len (Vint (Int.repr add_len));
      gvar sha._K256 kv)
      SEP (FRZL FR5)
  ).
  {
    (* != 0 case *)
    forward.
    unfold hmac256drbgabs_common_mpreds.
    Exists seed (Vint (Int.neg (Int.repr (9)))).
    unfold entropy.get_entropy in *.
    destruct (ENTROPY.get_bytes (Z.to_nat 32) s).
    {
      (* contradiction. cannot be a success *)
      exfalso. hnf in ENT. inversion ENT; subst vret; simpl in *. discriminate.
    }
    rewrite andb_negb_r.
    rewrite Z.gtb_ltb.
    destruct (Z.ltb_ge 256 (Zlength contents)) as [_ Y]; rewrite Y. 2: omega.
    entailer!.
    my_thaw FR5. my_thaw FR4. simpl. Time entailer!. (*Coq8.5pl2:1260secs; Coq8.5pl1: 20mins or so*)
    rewrite data_at__memory_block. entailer!. clear FR2 FR1. 
    destruct seed; inv Pseed. unfold offset_val.
    rewrite <- repr_unsigned with (i:=i).
    change (sizeof (tarray tuchar 384)) with (32 + (384 - 32)).
    rewrite (memory_block_split Tsh b (Int.unsigned i) 32 (384 - 32)), add_repr; try omega.
    cancel. apply data_at_memory_block. 
    cbv; trivial.
    assert (Int.unsigned i >= 0) by (pose proof (Int.unsigned_range i); omega).
    split. omega.
    clear - Hfield. red in Hfield; simpl in Hfield. omega.
  }
  {
    forward. clear FR2 FR1.
    entailer!. clear FR4 FR5. (*subst add_len.*)
    apply negb_false_iff in H11. symmetry in H11; apply binop_lemmas2.int_eq_true in H11. 
    subst vret; split; trivial.  
  }

  (* now that we know entropy call succeeded, use that fact to simplify the SEP clause *)
  remember (entropy.ENTROPY.get_bytes (Z.to_nat entropy_len) s) as entropy_result.
  unfold entropy.get_entropy in ENT;
  rewrite <- Heqentropy_result in ENT;
  destruct entropy_result; [|
  normalize;
  simpl in ENT; destruct e; [inversion ENT |
  assert (contra: False) by (apply ENT; reflexivity); inversion contra]
  ].

  rename l into entropy_bytes.

  assert (Hentropy_bytes_length: Zlength (map Vint (map Int.repr entropy_bytes)) = 32).
  {
    repeat rewrite Zlength_map.
    eapply get_bytes_Zlength.
    omega.
    subst entropy_len.
    eassumption.
  }
  my_thaw FR5. my_thaw FR4.
  rewrite H9, H5, <- H1.

  apply body_hmac_drbg_reseed_TAIL with (s0:=s0); try assumption.
Time Qed. (*62secs; Coq85pl2:40secs*)
