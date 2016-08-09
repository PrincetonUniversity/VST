Require Import floyd.proofauto.
Import ListNotations.
Local Open Scope logic.

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

Lemma REST: forall (Espec : OracleKind) (contents : list Z) additional add_len ctx 
  md_ctx' V' reseed_counter' entropy_len' prediction_resistance' reseed_interval'
  key V reseed_counter entropy_len prediction_resistance reseed_interval kv
  info_contents (s : ENTROPY.stream)
(*Delta_specs := abbreviate : PTree.t funspec*)
  seed
  (H : 0 <= add_len <= Int.max_unsigned)
  (H0 : Zlength V = 32)
  (H1 : add_len = Zlength contents)
  (contents' : list Z)
  (Heqcontents' : contents' = contents_with_add additional add_len contents)
  (ELc' : 0 < entropy_len + Zlength contents' (* <= 384*))
(*  (ELc' : 0 < entropy_len + Zlength contents (* <= 384*))*)
  (H3 : Forall general_lemmas.isbyteZ V)
  (H4 : Forall general_lemmas.isbyteZ contents)
  (H5 : map Vint (map Int.repr V) = V')
  (H6 : Vint (Int.repr reseed_counter) = reseed_counter')
  (H7 : Vint (Int.repr entropy_len) = entropy_len')
  (H8 : Vint (Int.repr reseed_interval) = reseed_interval')
  (H9 : Val.of_bool prediction_resistance = prediction_resistance')
  (PNadditional : is_pointer_or_null additional)
  (Pctx : isptr ctx)
  (ELnonneg : 0 <= entropy_len)
  (ZLc' : Zlength contents' = 0 \/ Zlength contents' = Zlength contents)
  (*(H10 : zlt 256 add_len = false)
  (H11 : zlt 384 (entropy_len + add_len) = false)*)
  (Hfield : field_compatible (tarray tuchar 384) [] seed)
  (AL256 : (add_len >? 256) = false)
  (EAL384 : (entropy_len + add_len >? 384) = false)
  (entropy_bytes : list Z)
  (s0 : ENTROPY.stream)
  (Heqentropy_result : ENTROPY.success entropy_bytes s0 = ENTROPY.get_bytes (Z.to_nat entropy_len) s),
(*
  (H : 0 <= Zlength contents <= Int.max_unsigned)
  (H0 : Zlength V = 32)
  (H1 : add_len = Zlength contents)
  (H2 : (*32 <=*) 0 < entropy_len + Zlength (contents_with_add additional add_len contents) <= 384)
  (H3 : Forall general_lemmas.isbyteZ V)
  (H4 : Forall general_lemmas.isbyteZ contents)
  (H5 : map Vint (map Int.repr V) = V')
  (H6 : Vint (Int.repr reseed_counter) = reseed_counter')
  (H7 : Vint (Int.repr entropy_len) = entropy_len')
  (H8 : Vint (Int.repr reseed_interval) = reseed_interval')
  (H9 : Val.of_bool prediction_resistance = prediction_resistance')
  (PNadditional : is_pointer_or_null additional)
  (Pctx : isptr ctx)
  (H10 : 256 >= Zlength contents)
  (Hfield : field_compatible (tarray tuchar 384) [] seed)
  (entropy_bytes : list Z)
  (s0 : ENTROPY.stream)
  (Heqentropy_result : ENTROPY.success entropy_bytes s0 =
                    ENTROPY.get_bytes (Z.to_nat entropy_len) s)
(*Delta := abbreviate : tycontext
POSTCONDITION := abbreviate : ret_assert
MORE_COMMANDS := abbreviate : statement*)
  (Hentropy_bytes_length : Zlength (map Vint (map Int.repr entropy_bytes)) = entropy_len),*)
@semax hmac_drbg_compspecs.CompSpecs Espec
  (initialized_list [_entropy_len; 232%positive; 231%positive]
     (func_tycontext f_mbedtls_hmac_drbg_reseed HmacDrbgVarSpecs
        HmacDrbgFunSpecs))
  (PROP ( )
   LOCAL (temp 232%positive Vzero; temp _entropy_len (Vint (Int.repr entropy_len));
   lvar _seed (tarray tuchar 384) seed; temp _ctx ctx; temp _additional additional;
   temp _len (Vint (Int.repr add_len)); gvar sha._K256 kv)
   SEP (Stream (get_stream_result (get_entropy 0 entropy_len entropy_len false s));
   data_at Tsh (tarray tuchar entropy_len) (map Vint (map Int.repr entropy_bytes)) seed;
   data_at Tsh (tarray tuchar (384 - entropy_len))
     (list_repeat (Z.to_nat (384 - entropy_len)) (Vint Int.zero))
     (offset_val entropy_len seed);
   da_emp Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents)) additional;
   md_full key md_ctx';
   data_at Tsh t_struct_mbedtls_md_info info_contents
     (hmac256drbgstate_md_info_pointer
        (md_ctx',
        (V', (reseed_counter', (entropy_len', (prediction_resistance', reseed_interval'))))));
   spec_sha.K_vector kv;
   data_at Tsh t_struct_hmac256drbg_context_st
     (md_ctx',
     (V', (reseed_counter', (entropy_len', (prediction_resistance', reseed_interval')))))
     ctx))
  (Ssequence (Sset _seedlen (Etempvar _entropy_len tuint))
     (Ssequence
        (Ssequence
           (Sifthenelse
              (Ebinop Cop.One (Etempvar _additional (tptr tuchar))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
              (Sset 233%positive
                 (Ecast
                    (Ebinop Cop.One (Etempvar _len tuint) (Econst_int (Int.repr 0) tint) tint)
                    tbool)) (Sset 233%positive (Econst_int (Int.repr 0) tint)))
           (Sifthenelse (Etempvar 233%positive tint)
              (Ssequence
                 (Scall None
                    (Evar _memcpy
                       (Tfunction
                          (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tuint Tnil)))
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
                 (Tfunction
                    (Tcons (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))
                       (Tcons (tptr tuchar) (Tcons tuint Tnil))) tvoid cc_default))
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
        (fun a : environ =>
         EX x : val,
         (PROP ( )
          LOCAL (temp ret_temp x)
          SEP (reseedPOST x contents additional add_len s
                 (HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance reseed_interval) ctx
                 info_contents kv
                 (md_ctx',
                 (V', (reseed_counter', (entropy_len', (prediction_resistance', reseed_interval'))))))) a))
     (fun a : environ =>
      EX x : val,
      local (lvar_denote _seed (tarray tuchar 384) x) a && ` (data_at_ Tsh (tarray tuchar 384) x) a)).
Proof.
  intros. 
  assert (ZLbytes: Zlength entropy_bytes = entropy_len).
    { eapply get_bytes_Zlength. omega. eassumption. } 
  apply Zgt_is_gt_bool_f in EAL384. 
  abbreviate_semax. 
(*  remember (contents_with_add additional add_len contents) as contents'.
  assert (ZLc': Zlength contents' = 0 \/ Zlength contents' = Zlength contents).
    { subst contents'. unfold contents_with_add.
      destruct (eq_dec add_len 0); simpl.
        rewrite andb_false_r. left; apply Zlength_nil. 
        destruct (base.EqDec_val additional nullval); simpl. left; apply Zlength_nil.
        right; trivial.
    } 
*)
  freeze [0;(*2;*)4;5;6;7] FR6. freeze [1;2] SEED.
  
 replace_SEP 0 (data_at Tsh (tarray tuchar 384)
         ((map Vint
            (map Int.repr entropy_bytes)) ++ (list_repeat (Z.to_nat (384 - entropy_len)) (Vint Int.zero))) seed).
  {
    entailer!. thaw SEED; clear FR6. (*subst entropy_len.*) rewrite sepcon_emp.
    apply derives_refl'. symmetry. 
    apply data_at_complete_split; repeat rewrite Zlength_map;
    try rewrite (*Hentropy_bytes_length,*) Zlength_list_repeat; try rewrite Zplus_minus; trivial; omega.
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
(*      temp 148%positive (Val.of_bool non_empty_additional);*)
      temp 233%positive (Val.of_bool non_empty_additional);
      gvar sha._K256 kv)
      SEP  (FRZL FR7; da_emp Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents)) additional)).
  { destruct additional; simpl in PNadditional; try contradiction.
    + subst i. rewrite da_emp_null. entailer. reflexivity.
    + rewrite da_emp_ptr. normalize.
      apply denote_tc_comparable_split; auto 50 with valid_pointer.
      (* TODO regression, this should have solved it *) 
      apply sepcon_valid_pointer2.
      apply data_at_valid_ptr; auto. }
  { (*nonnull additional*) 
    destruct additional; simpl in PNadditional; try contradiction. subst i. elim H2; trivial. clear H2.
    forward. entailer!. simpl. unfold  contents_with_add; simpl.
    destruct (initial_world.EqDec_Z (Zlength contents) 0).
    + rewrite e. simpl. split; reflexivity.
    + simpl. rewrite Int.eq_false; simpl. split; try reflexivity. intros N.
       assert (Int.unsigned (Int.repr (Zlength contents)) = Int.unsigned (Int.repr 0)). rewrite N; trivial.
       clear N. rewrite Int.unsigned_repr in H1. 2: omega. rewrite Int.unsigned_repr in H1; omega. 
  }
  { (*nullval additional*) 
    rewrite H2 in *. 
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
      gvar sha._K256 kv)
      SEP (data_at Tsh (tarray tuchar 384)
         (map Vint
            (map Int.repr entropy_bytes) ++ (map Vint (map Int.repr (*contents*)contents')) ++
          list_repeat (Z.to_nat (384 - entropy_len - Zlength (*contents*)contents')) (Vint Int.zero)) seed;
           (*FRZL FR8*)FRZL FR6;
       da_emp Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents)) additional)). 
  +
    rewrite H2 in Heqnon_empty_additional.
    destruct additional; simpl in PNadditional; try contradiction.
    - subst i; simpl in *; discriminate.
    - destruct (eq_dec add_len 0); try discriminate. 
      subst non_empty_additional; clear Heqnon_empty_additional. 
    rename b into bb. rename i into ii.
    rewrite da_emp_ptr. normalize. 
    assert (contents' = contents).
    { subst contents'. unfold contents_with_add. simpl.
        destruct (initial_world.EqDec_Z add_len 0). omega. reflexivity. }
    clear Heqcontents'; subst contents'. clear ZLc'. 
    replace_SEP 0 ((data_at Tsh (tarray tuchar entropy_len)
         (map Vint
            (map Int.repr entropy_bytes)) seed) * (data_at Tsh (tarray tuchar (384 - entropy_len))
         (list_repeat (Z.to_nat (384 - entropy_len)) (Vint Int.zero)) (offset_val entropy_len seed))).
    {
      entailer!.
      apply derives_refl'; apply data_at_complete_split; trivial; try omega.
      rewrite Zlength_app in H10; rewrite H10; trivial.
      repeat rewrite Zlength_map; trivial.
      rewrite Zlength_list_repeat; omega. 
    } 
    flatten_sepcon_in_SEP. rewrite data_at_isptr with (p:=seed); Intros.
    apply isptrD in Pseed; destruct Pseed as [b [i SEED]]; rewrite SEED in *.
    change (offset_val entropy_len (Vptr b i)) with (Vptr b (Int.add i (Int.repr entropy_len))).
    assert_PROP (field_compatible (Tarray tuchar (384 - entropy_len) noattr) 
          [] (Vptr b (Int.add i (Int.repr entropy_len)))) as FC_el by entailer!. 
    simpl in *.
    replace_SEP 1 (
      (data_at Tsh (tarray tuchar (Zlength contents))
         (list_repeat (Z.to_nat (Zlength contents)) (Vint Int.zero)) (Vptr b (Int.add i (Int.repr entropy_len)))) * 
      (data_at Tsh (tarray tuchar (384 - entropy_len - Zlength contents))
         (list_repeat (Z.to_nat (384 - entropy_len - Zlength contents)) (Vint Int.zero)) (offset_val (Zlength contents) (Vptr b (Int.add i (Int.repr entropy_len)))))).
    { (*
      subst entropy_len.
      replace (384 - 32) with 352 by omega.
      remember (Vptr b (Int.add i (Int.repr 32))) as seed'.
      clear Heqseed'.
      (*entailer!*) go_lower.
      replace (length contents) with (Z.to_nat (Zlength contents)) by
        (rewrite Zlength_correct; apply Nat2Z.id).      
      apply derives_refl'; apply data_at_complete_split; repeat rewrite Zlength_list_repeat; try omega; auto.
      {
        (*replace (Zlength contents + (352 - Zlength contents')) with (384 - 32) by omega.*)
        replace (Zlength contents + (352 - Zlength contents)) with 352 by omega.
        replace (384-32) with 352 in H11 by omega. 
        assumption.
      }
      {
        rewrite list_repeat_app.
        rewrite <- Z2Nat.inj_add; try omega.
        replace (Zlength contents + (352 - Zlength contents)) with 352 by omega.
        reflexivity.
      }*) 
      remember (Vptr b (Int.add i (Int.repr entropy_len))) as seed'.
      clear Heqseed'.
      (*entailer!*) go_lower.   
      apply derives_refl'. 
      apply data_at_complete_split; try rewrite Zlength_list_repeat; try omega; auto.
      + rewrite Zlength_list_repeat.
        replace (Zlength contents + (384 - entropy_len - Zlength contents)) with (384 - entropy_len); trivial; omega.
        omega.
      + rewrite list_repeat_app, <- Z2Nat.inj_add. 
        replace (Zlength contents + (384 - entropy_len - Zlength contents)) with (384 - entropy_len); trivial; omega.
        omega. omega.
    }

    flatten_sepcon_in_SEP.
    replace_SEP 1 (memory_block Tsh (Zlength contents) (Vptr b (Int.add i (Int.repr entropy_len)))).
    { entailer!. replace (Zlength contents) with (sizeof (*cenv_cs*) (tarray tuchar (Zlength contents))) at 2.
      apply data_at_memory_block. simpl. rewrite Zmax0r; omega.
    }
    forward_call ((Tsh, Tsh), (Vptr b (Int.add i (Int.repr entropy_len))), (*additional*)Vptr bb ii, Zlength contents, map Int.repr contents).
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
      clear POSTCONDITION. cancel. my_thaw FR6.
      rewrite H1; cancel.
    }
    {
      (* prove the PROP clauses *)
      repeat split; auto; omega.
    }
    (*Intros memcpy_vret. subst memcpy_vret.*)
    forward.
    change (fst (Tsh, Tsh)) with Tsh;
    change (snd (Tsh, Tsh)) with Tsh.
    rewrite H1, SEED.

    (* Time entailer!. (*8.5pl2: 1230secs*) *)
    go_lower. normalize. 
    apply andp_right. apply prop_right. repeat split; auto.
    

    thaw FR6. rewrite (*H1,*) da_emp_ptr. normalize.
    apply andp_right. apply prop_right. simpl. (*specialize (Zlength_nonneg contents).*) subst add_len; omega.
    cancel.
    erewrite data_at_complete_split with 
     (A:=map Vint (map Int.repr entropy_bytes))
     (p:=Vptr b i)(*(offset:=entropy_len)*)
     (AB:= (map Vint (map Int.repr entropy_bytes) ++
       map Vint (map Int.repr contents) ++
       list_repeat (Z.to_nat (384 - entropy_len - Zlength contents))
         (Vint Int.zero))). 
    7: solve[reflexivity].
    cancel.
    6: solve[reflexivity].
    3: solve [repeat rewrite Zlength_map; omega].

    3: solve [reflexivity].
    3: solve [rewrite Zlength_app, Zlength_list_repeat; repeat rewrite Zlength_map; try omega].

    Focus 2. rewrite Zlength_app, (* <- H17, *) Zlength_list_repeat; try omega.
             repeat rewrite Zlength_map. rewrite ZLbytes(*, H2*).
             assert (X: entropy_len + (Zlength contents + (384 - entropy_len - Zlength contents)) = 384) by omega.
             rewrite X; assumption.

    rewrite Zlength_app; repeat rewrite Zlength_map; rewrite Zlength_list_repeat.
    assert (X: Zlength contents + (384 - entropy_len - Zlength contents) = 384 - entropy_len) by omega.
    rewrite X.
    erewrite data_at_complete_split with (AB:=map Vint (map Int.repr contents) ++
       list_repeat (Z.to_nat (384 - entropy_len - Zlength contents))
         (Vint Int.zero))
      (p:=(Vptr b (Int.add i (Int.repr entropy_len))))
      (A:= map Vint (map Int.repr contents)).
    7: reflexivity. 3: reflexivity. 5: reflexivity. 
    3: reflexivity. 3: solve [rewrite Zlength_list_repeat; repeat rewrite Zlength_map; try omega].

    unfold offset_val. rewrite Int.add_assoc, add_repr. repeat rewrite Zlength_map. cancel. (*apply derives_refl.*)
    repeat rewrite Zlength_map. rewrite Zlength_list_repeat; try omega.
    apply derives_refl. 
    rewrite Zlength_list_repeat; repeat rewrite Zlength_map; try omega. rewrite X; assumption.

    omega.

  + rewrite H2 in Heqnon_empty_additional; clear H2.
    forward.
    go_lower. normalize.
    assert (contents' = nil).
    { subst contents'. unfold contents_with_add.
      destruct (eq_dec add_len 0); simpl in *.
      + rewrite e in *. rewrite andb_false_r; trivial.
      + destruct (base.EqDec_val additional nullval); simpl in *; trivial; discriminate. }
    clear Heqcontents'; subst contents'.
    rewrite Zlength_nil, Zplus_0_r. 
    apply andp_right.
    apply prop_right. repeat split; trivial.
    do 2 rewrite map_nil. rewrite app_nil_l, Zminus_0_r. cancel.

  + (*contiuation after conditional*)  

  replace_SEP 0 (
    (data_at Tsh (tarray tuchar (entropy_len + Zlength contents')) (map Vint
            (map Int.repr entropy_bytes) ++
            map Vint (map Int.repr contents')) seed) *
    (data_at Tsh (tarray tuchar (384 - (entropy_len + Zlength contents'))) (list_repeat (Z.to_nat (384 - entropy_len - Zlength contents'))
            (Vint Int.zero)) (offset_val (entropy_len + Zlength contents') seed))
      ).
  { 
    clear Heqcontents'.
    rewrite app_assoc.
    entailer!.
    rewrite Zlength_app, Zlength_list_repeat in H2; try omega.
    apply derives_refl'.
    apply data_at_complete_split; repeat rewrite Zlength_list_repeat; try omega; auto;
      (* rewrite Zlength_app;*)try rewrite H2; try rewrite Hentropy_bytes_length; repeat rewrite Zlength_map; auto.
  }
  flatten_sepcon_in_SEP.

  do 2 rewrite map_map.
  rewrite <- map_app.
  rewrite <- map_map.
  thaw FR6.
  rewrite data_at_isptr with (p:=seed). Intros. 

  (*mbedtls_hmac_drbg_update( ctx, seed, seedlen )*)
  freeze [1;2;7] FR9.
  remember (entropy_len + Zlength contents') as ll.
  repeat rewrite Zlength_map in Hentropy_bytes_length.
  forward_call (entropy_bytes ++ contents', seed, ll,
                ctx, 
                (md_ctx',
                 (map Vint (map Int.repr V),
                 (Vint (Int.repr reseed_counter),
                 (Vint (Int.repr entropy_len),
                 (Val.of_bool prediction_resistance, Vint (Int.repr reseed_interval)))))), 
                (HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance reseed_interval), 
                kv, info_contents).
  { 
    (* prove the SEP clauses match up *)
    destruct seed; simpl in Pseed; try contradiction.
    rewrite da_emp_ptr.
    rewrite Zlength_app. 
    rewrite ZLbytes. simpl. 
    normalize. apply andp_right. apply prop_right. repeat split; trivial.
      { omega. (*subst contents' add_len. unfold contents_with_add.
        destruct (eq_dec (Zlength contents) 0); simpl in *.
        + rewrite andb_false_r, Zlength_nil. rewrite e, Zplus_0_r in *.
          destruct ZL
          rewrite Z.max_r; omega.
        + rewrite andb_true_r.
          destruct (base.EqDec_val additional nullval); simpl in *. right. omega.*) }
    rewrite <- Heqll, H5, H6, H7, H8, H9. cancel.
  }
  {
    (* prove the PROP clauses *)
    simpl in *. repeat split; trivial; try omega. (*
    rewrite H2 in *;*) rewrite int_max_unsigned_eq. omega.
    left; rewrite Zlength_app, ZLbytes; trivial.
    { apply isbyteZ_app; try assumption. 
      eapply get_bytes_isbyteZ; eauto. 
      subst contents'; unfold contents_with_add.
      destruct (eq_dec add_len 0); simpl.
        rewrite andb_false_r. constructor. 
      destruct (base.EqDec_val additional nullval); simpl. constructor. 
      trivial.
    }
  }
  unfold hmac256drbgabs_common_mpreds. 
  repeat flatten_sepcon_in_SEP.
  thaw FR9.
  freeze [1;2;4;6;7] FR10.
  freeze [0;1] FR11.
  gather_SEP 1 2.
  replace_SEP 0 (data_at Tsh (tarray tuchar 384) ((map Vint
         (map Int.repr entropy_bytes)) ++ (map Vint (map Int.repr contents') ++
       list_repeat (Z.to_nat (384 - entropy_len - Zlength contents'))
         (Vint Int.zero))) seed).
  { (*
    subst entropy_len.
    replace (384 - 32) with 352 by omega.
    replace (384 - (32 + Zlength contents')) with (352 - Zlength contents') by omega.*)
    rewrite app_assoc.
    rewrite map_map.
    rewrite map_app.
    rewrite <- map_map.
    replace (map (fun x : Z => Vint (Int.repr x)) contents') with (map Vint (map Int.repr contents')) by (rewrite map_map; auto).
    clear Heqcontents'. 
    rewrite Zlength_app, ZLbytes.
    entailer!.
    destruct seed; simpl in Pseed; try contradiction.
    rewrite da_emp_ptr. Intros.
    apply derives_refl'; symmetry; apply data_at_complete_split;
     repeat rewrite Zlength_list_repeat; try omega; auto; try rewrite Zlength_app; 
     try rewrite ZLbytes; repeat rewrite Zlength_map; auto.
     replace (Zlength entropy_bytes + Zlength contents' +
      (384 - Zlength entropy_bytes - Zlength contents')) with 384 by omega.
     assumption.
  }
  
  (* ctx->reseed_counter = 1; *)
  my_thaw FR11.
  freeze [0;1] FR12. rewrite H5, H6, H7, H8, H9. 
  unfold hmac256drbgabs_to_state. simpl.
  remember (HMAC256_DRBG_functional_prog.HMAC256_DRBG_update
            (contents_with_add seed ll
               (entropy_bytes ++ contents')) key V).
  destruct p.  
  simpl. normalize. rewrite H6, H7, H8, H9. drop_LOCAL 0%nat. drop_LOCAL 0%nat.
  subst contents'.
  unfold_data_at 1%nat. (*crucial: doing the field assignment without unfolding data_at results in the forward taking 1200secs*)
(*  freeze [0;1;2;4;5;6] FIELDS. optional wrt performance*)
  Time forward.
(* Opaque HMAC_DRBG_update. Opaque HMAC256_functional_prog.HMAC256.
   Opaque HMAC256_DRBG_functional_prog.HMAC256_DRBG_update.
   clear Heqnon_empty_additional non_empty_additional.
   subst V' reseed_counter' entropy_len' reseed_interval' prediction_resistance'.
   clear - Heqp Heqentropy_result H10 H1 H2 H H0 H3 H4.
   freeze [1] FR13. thaw FR13.
  Time forward. *)(*preceding forward with (an informaion-losing clear reduces time to 1100secs*)
    (*Coq8.5pl2: 1210.094 secs (336.421u,0.687s) *)
    (*takes 3597secs if HMAC256_DRBG_functional_prog.HMAC256_DRBG_update is opaque*)
    (*in VST1.6, this forward takes 1968.182 secs, without allocating a single KB of memory ;-) *)
    (*Coq8.5pl1: 1100secs*)
(*yields a filed_at ctx*)

  (* return 0 *)
  Time forward. (*5 secs*)
  Exists seed (Vint (Int.repr 0)). normalize.
  entailer!.

  assert (ZL1: Zlength (contents_with_add additional (Zlength contents) contents) >? 256 = false). 
  { clear - ZLc' AL256. destruct ZLc' as [ZLc' | ZLc']; rewrite ZLc'; trivial. }

  apply Zgt_is_gt_bool_f in AL256.
(*  apply Zgt_is_gt_bool_f in EAL384.*)
  assert (Z: (zlt 256 (Zlength contents)
       || zlt 384
            (hmac256drbgabs_entropy_len
               (HMAC256DRBGabs key V reseed_counter (Zlength entropy_bytes) prediction_resistance
                  reseed_interval) + Zlength contents))%bool = false).
  { destruct (zlt 256 (Zlength contents)); simpl; try omega.
    destruct (zlt 384 (Zlength entropy_bytes + Zlength contents)); simpl; trivial. omega.
  } 
  unfold reseedPOST. rewrite Z.
(*  assert (ZL: Zlength contents >? 256 = false).
  { clear -  H10. apply Zge_is_le_bool in H10.
    unfold Z.gtb. unfold Z.leb in H10. destruct (Zlength contents ?= 256); trivial. discriminate.
  }*)
  entailer!.
  { unfold return_value_relate_result. simpl.
    rewrite andb_negb_r, ZL1.
    unfold get_entropy. rewrite <- Heqentropy_result. trivial. }
(*  remember (mbedtls_HMAC256_DRBG_reseed_function s
            (HMAC256DRBGabs key V reseed_counter (Zlength entropy_bytes) prediction_resistance reseed_interval)
            (contents_with_add additional (Zlength contents) contents)).*)
  simpl.
  rewrite andb_negb_r, ZL1.
  unfold get_entropy. rewrite <- Heqentropy_result.
  remember (HMAC_DRBG_update HMAC256_functional_prog.HMAC256
              (entropy_bytes ++ contents_with_add additional (Zlength contents) contents) key V) as q.
  destruct q. normalize. 
  thaw FR12. thaw FR10. cancel. simpl. rewrite <- Heqp.
  unfold  hmac256drbgabs_common_mpreds. cancel.
  unfold get_entropy; rewrite <- Heqentropy_result. simpl. normalize. entailer!.
  { simpl in *. unfold HMAC_DRBG_update in Heqq.
    destruct (entropy_bytes ++
         contents_with_add additional (Zlength contents) contents); inv Heqq.
    + split. apply hmac_common_lemmas.HMAC_Zlength. apply hmac_common_lemmas.isbyte_hmac.
    + split. apply hmac_common_lemmas.HMAC_Zlength. apply hmac_common_lemmas.isbyte_hmac.
  }
  unfold_data_at 1%nat. cancel.
  unfold HMAC256_DRBG_functional_prog.HMAC256_DRBG_update in Heqp.
  destruct seed; simpl in Pseed; try contradiction.
  unfold contents_with_add in Heqp at 1. simpl in Heqp.
  destruct (initial_world.EqDec_Z (Zlength entropy_bytes +
                 Zlength (contents_with_add additional (Zlength contents) contents)) 0); simpl in Heqp. 
  specialize (Zlength_nonneg (contents_with_add additional (Zlength contents) contents)).
  intros; omega.

  rewrite <- Heqp in *. inv Heqq. cancel. 
Time Qed. (*Coq8.5pl2: 44secs*)

Lemma body_hmac_drbg_reseed: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs 
       f_mbedtls_hmac_drbg_reseed hmac_drbg_reseed_spec.
Proof.
  start_function.
  rename lvar0 into seed.
  destruct initial_state_abs.
  destruct initial_state as [md_ctx' [V' [reseed_counter' [entropy_len' [prediction_resistance' reseed_interval']]]]].
  unfold hmac256drbg_relate.
  Intros.
  rewrite da_emp_isptrornull. (*needed later*)
  rewrite data_at_isptr with (p:=ctx).
  Intros. simpl in *. rename H3 into El2. 

  (* entropy_len = ctx->entropy_len *)
  simpl in *.
  remember (contents_with_add additional add_len contents) as contents'.
  assert (ZLc': Zlength contents' = 0 \/ Zlength contents' = Zlength contents).
    { subst contents'. unfold contents_with_add.
      destruct (eq_dec add_len 0); simpl.
        rewrite andb_false_r. left; apply Zlength_nil. 
        destruct (base.EqDec_val additional nullval); simpl. left; apply Zlength_nil.
        right; trivial.
    } 

  freeze [0;1;3;4;5;6] FR1.
  forward. (*{ rewrite <- H7; entailer!. }*)

  remember (orb (zlt 256 add_len) (zlt 384 (entropy_len + add_len))) as add_len_too_high.

  (* if (len > MBEDTLS_HMAC_DRBG_MAX_INPUT ||
        entropy_len + len > MBEDTLS_HMAC_DRBG_MAX_SEED_INPUT) *)
  freeze [0;1] FR2.
  forward_if (PROP  ()
      LOCAL  (temp _entropy_len (Vint (Int.repr entropy_len));
      lvar _seed (tarray tuchar 384) seed; temp _ctx ctx;
      temp _additional additional; temp _len (Vint (Int.repr add_len));
      temp 231%positive (Val.of_bool add_len_too_high);
      gvar sha._K256 kv)
      SEP  (FRZL FR2)). 
  { forward. entailer!. }
  { forward. entailer!. simpl.
      unfold Int.ltu; simpl.
      rewrite add_repr.
      rewrite Int.unsigned_repr. 2: rewrite int_max_unsigned_eq; omega.
      rewrite Int.unsigned_repr_eq, Zmod_small.
      + destruct (zlt 384 (entropy_len + Zlength contents)); simpl; try reflexivity.
      + omega.  (*rewrite hmac_pure_lemmas.IntModulus32.
        change (2 ^ 32) with 4294967296. omega.*)
  }

  forward_if (PROP  (add_len_too_high = false)
      LOCAL  (temp _entropy_len (Vint (Int.repr entropy_len));
      lvar _seed (tarray tuchar 384) seed; temp _ctx ctx;
      temp _additional additional; temp _len (Vint (Int.repr add_len));
      gvar sha._K256 kv)
      SEP (FRZL FR2)
  ).
  { rewrite H3 in *. forward. 
    Exists seed (Vint (Int.neg (Int.repr 5))). normalize. entailer!. 
    unfold reseedPOST. simpl; rewrite <- Heqadd_len_too_high.
    (*remember (zlt 256 (Zlength contents) || zlt 384 (entropy_len + Zlength contents))%bool as c.
    destruct c; simpl in Heqadd_len_too_high; try discriminate.*)
    normalize. apply andp_right. apply prop_right; repeat split; trivial.
    thaw FR2. thaw FR1. cancel.
  }
  {
    forward.
    entailer!.
  }
  Intros. rewrite H3 in *; clear H3 add_len_too_high.
  symmetry in Heqadd_len_too_high; apply orb_false_iff in Heqadd_len_too_high; destruct Heqadd_len_too_high.

(*
  assert (AL256: add_len >? 256 = false).
  { remember (add_len >? 256) as a. symmetry in Heqa.
    destruct a; trivial. apply Zgt_is_gt_bool in Heqa. omega. } 
*)
  thaw FR2. thaw FR1. freeze [1;2;3;4;5;6] FR3.
  (* memset( seed, 0, MBEDTLS_HMAC_DRBG_MAX_SEED_INPUT ); *)
  forward_call (Tsh, seed, 384, Int.zero).
  { 
   (*my_thaw FR2. my_thaw FR1.*)
    rewrite data_at__memory_block.
    change (sizeof (*cenv_cs*) (tarray tuchar 384)) with 384. 
    normalize. cancel.
  } 
  
  assert (AL256: 256 >= add_len).
  { destruct (zlt 256 add_len); try discriminate; trivial. }
  assert (EL384 : 384 >= entropy_len + add_len).
  { destruct ( zlt 384 (entropy_len + add_len)); try discriminate; trivial. }
 
(*
  destruct (zlt 384 (entropy_len + add_len) ); simpl in H11; try discriminate.
  destruct (zlt 256 add_len); simpl in H10; try discriminate. clear H10 H11.*)
  (*freeze [1;2;3;4;5;6] FR3.*)
  assert_PROP (field_compatible (tarray tuchar 384) [] seed) as Hfield by entailer!.
  replace_SEP 0 ((data_at Tsh (tarray tuchar entropy_len)
         (list_repeat (Z.to_nat entropy_len) (Vint Int.zero)) seed) * (data_at Tsh (tarray tuchar (384 - entropy_len))
         (list_repeat (Z.to_nat (384 - entropy_len)) (Vint Int.zero)) (offset_val entropy_len seed))).
  {
    (*subst entropy_len.*)
    erewrite <- data_at_complete_split with (length:=384)(AB:=list_repeat (Z.to_nat 384) (Vint Int.zero)); repeat rewrite Zlength_list_repeat; trivial; try omega.
    go_lower. apply derives_refl. rewrite Zplus_minus. assumption.
    rewrite list_repeat_app. rewrite Z2Nat.inj_sub; try omega. rewrite le_plus_minus_r. trivial. apply Z2Nat.inj_le; try omega. 
  }
  flatten_sepcon_in_SEP.
  
  replace_SEP 0 (memory_block Tsh entropy_len seed).
  {
    (*subst entropy_len.*)
    go_lower. eapply derives_trans. apply data_at_memory_block. simpl. rewrite Z.max_r, Z.mul_1_l. trivial. omega.
  }

  (* get_entropy(seed, entropy_len ) *)
  thaw FR3. (*freeze [0;1;2;4;5;7] FR4.*) freeze [1;2;3;4;6;7] FR4.
  forward_call (Tsh, s, seed, entropy_len).
  { split. split; try omega. rewrite int_max_unsigned_eq. omega.
    apply semax_call.writable_share_top.
(*    
    subst entropy_len; auto.*)
  }
  Intros vret. rename H13 into ENT. 
  assert (AL256': add_len >? 256 = false).
  { remember (add_len >? 256) as d.
    destruct d; symmetry in Heqd; trivial.
    apply Zgt_is_gt_bool in Heqd.
    destruct (zlt 256 add_len); try discriminate; omega.
  }
  assert (EAL256': (entropy_len + add_len)  >? 384 = false).
  { remember (entropy_len + add_len >? 384) as d.
    destruct d; symmetry in Heqd; trivial.
    apply Zgt_is_gt_bool in Heqd.
    destruct (zlt 384 (entropy_len + add_len)); try discriminate; omega.
  }
     

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
    Exists seed (Vint (Int.neg (Int.repr (9)))). normalize. entailer!.
    unfold reseedPOST. 
    remember ((zlt 256 (Zlength contents)
       || zlt 384
            (hmac256drbgabs_entropy_len
               (HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance
                  reseed_interval) + Zlength contents))%bool) as z.
    destruct z.
    { exfalso. simpl in Heqz. rewrite H12, H3 in Heqz. inv Heqz. }
    clear Heqz.
    unfold return_value_relate_result, get_entropy in ENT.
    simpl in ENT.
    remember (ENTROPY.get_bytes (Z.to_nat entropy_len) s) as  GE.
    destruct GE.
    + inv ENT. simpl in H13. discriminate.
    + thaw FR5. unfold get_entropy. rewrite <- HeqGE.
      remember (mbedtls_HMAC256_DRBG_reseed_function s
            (HMAC256DRBGabs key V reseed_counter 32 prediction_resistance
               reseed_interval) (contents_with_add additional (Zlength contents) contents)) as M.
      remember (mbedtls_HMAC256_DRBG_reseed_function s
             (HMAC256DRBGabs key V reseed_counter 32 prediction_resistance
                reseed_interval) contents).
      unfold mbedtls_HMAC256_DRBG_reseed_function, HMAC256_DRBG_functional_prog.HMAC256_DRBG_reseed_function in *.
      unfold DRBG_reseed_function in *. rewrite andb_negb_r in *.
      unfold return_value_relate_result in ENT.
      unfold get_entropy in *; simpl in *. rewrite <- HeqGE in *.
      
      rewrite AL256' in *.
      remember (Zlength (contents_with_add additional (Zlength contents) contents)) as ZLa.
      assert (ZLa256: ZLa >? 256 = false).
      { destruct ZLc' as [PP | PP]; rewrite PP; trivial. } 
      rewrite ZLa256 in *. subst M r. normalize. simpl. cancel.
      unfold get_entropy. simpl. rewrite andb_negb_r, <- HeqGE.
      unfold hmac256drbgabs_common_mpreds. simpl. normalize.
      apply andp_right. apply prop_right. repeat split; trivial.
      thaw FR4. cancel.
      rewrite data_at__memory_block. entailer!. 
      destruct seed; inv Pseed. unfold offset_val.
      rewrite <- repr_unsigned with (i:=i). 
      assert (XX: sizeof (tarray tuchar 384) = entropy_len + (384 - entropy_len)).
      { simpl. omega. }
      rewrite XX.
      rewrite (memory_block_split Tsh b (Int.unsigned i) entropy_len (384 - entropy_len)), add_repr; try omega.
      cancel.
      eapply derives_trans. apply data_at_memory_block.
          simpl. rewrite Z.max_r, Z.mul_1_l; try omega; trivial.
      rewrite Zplus_minus. cbv; trivial.  
      assert (Int.unsigned i >= 0) by (pose proof (Int.unsigned_range i); omega).
      split. omega.
      clear - Hfield. red in Hfield; simpl in Hfield. omega.
  }
  {
    forward.
    entailer!. clear FR4 FR5. (*subst add_len.*)
    apply negb_false_iff in H13. symmetry in H13; apply binop_lemmas2.int_eq_true in H13. 
    subst vret; split; trivial.  
  }
  Intros. subst vret. unfold return_value_relate_result in ENT.
  (* now that we know entropy call succeeded, use that fact to simplify the SEP clause *)
  remember (entropy.ENTROPY.get_bytes (Z.to_nat entropy_len) s) as entropy_result.
  unfold entropy.get_entropy in ENT;
  rewrite <- Heqentropy_result in ENT;
  destruct entropy_result; [|
  normalize;
  simpl in ENT; destruct e; [inversion ENT |
  assert (contra: False) by (apply ENT; reflexivity); inversion contra]
  ].
  clear ENT.

  rename l into entropy_bytes.
  thaw FR5. thaw FR4.
  eapply REST with (s0:=s0)(contents':=contents'); trivial. omega. 
Time Qed. (*Coq8.5pl2: 24secs*)
