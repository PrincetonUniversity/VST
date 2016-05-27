Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.common.AST.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Floats.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.

Require Import ccc26x86.Ctypes. (*for type and access_mode*)
Require Import sepcomp.mem_lemmas. (*needed for definition of valid_block_dec etc*)

Require Import msl.Axioms.
Require Import sepcomp.structured_injections.
Require Import sepcomp.reach. 
Require Import sepcomp.semantics. 
Require Import sepcomp.semantics_lemmas. 
Require Import sepcomp.effect_semantics. 
Require Import sepcomp.effect_properties.
Require Import sepcomp.globalSep.

Require Import ccc26x86.I64Helpers.

Definition memcpy_Effect sz vargs m:=
       match vargs with 
          Vptr b1 ofs1 :: Vptr b2 ofs2 :: nil =>
          fun b z => eq_block b b1 && zle (Int.unsigned ofs1) z &&
                     zlt z (Int.unsigned ofs1 + sz) && valid_block_dec m b
       | _ => fun b z => false
       end.
      
Lemma memcpy_Effect_unchOn: forall m bsrc osrc sz bytes bdst odst m'
        (LD: Mem.loadbytes m bsrc (Int.unsigned osrc) sz = Some bytes)
        (ST: Mem.storebytes m bdst (Int.unsigned odst) bytes = Some m')
        (SZ: sz >= 0),
    Mem.unchanged_on
      (fun b z=> memcpy_Effect sz (Vptr bdst odst :: Vptr bsrc osrc :: nil) 
                 m b z = false) m m'.
Proof. intros.
  split; intros.
    unfold Mem.perm. rewrite (Mem.storebytes_access _ _ _ _ _ ST). intuition.
  unfold memcpy_Effect in H.
    rewrite (Mem.storebytes_mem_contents _ _ _ _ _ ST).
    destruct (valid_block_dec m b); simpl in *. rewrite andb_true_r in H; clear v.
    destruct (eq_block b bdst); subst; simpl in *.
      rewrite PMap.gss. apply Mem.setN_other.
      intros. intros N; subst. 
        rewrite (Mem.loadbytes_length _ _ _ _ _ LD), nat_of_Z_eq in H1; trivial.
          destruct (zle (Int.unsigned odst) ofs); simpl in *.
            destruct (zlt ofs (Int.unsigned odst + sz)). inv H.
            omega. omega.
    clear H. rewrite PMap.gso; trivial.
  elim n. eapply Mem.perm_valid_block; eassumption.
Qed.

Lemma external_call_memcpy_unchOn:
    forall {F V:Type} (ge : Genv.t F V) e m ty b1 ofs1 b2 ofs2 m' a tr vres,
    external_call (EF_memcpy (sizeof e ty) a) ge 
                  (Vptr b1 ofs1 :: Vptr b2 ofs2 :: nil) m tr vres m' -> 
    Mem.unchanged_on
      (fun b z=> memcpy_Effect (sizeof e ty) (Vptr b1 ofs1 :: Vptr b2 ofs2 :: nil) 
                 m b z = false) m m'.
Proof. intros. inv H.
  eapply memcpy_Effect_unchOn; try eassumption.
Qed.
 
Lemma memcpy_Effect_validblock:
    forall {F V:Type} (ge : Genv.t F V) m sz vargs b z,
    memcpy_Effect sz vargs m b z = true ->
    Mem.valid_block m b.
Proof. intros.
 unfold memcpy_Effect in H.  
  destruct vargs; try discriminate.
  destruct v; try discriminate.
  destruct vargs; try discriminate.
  destruct v; try discriminate.
  destruct vargs; try discriminate.
  destruct (valid_block_dec m b); simpl in *. trivial. 
  rewrite andb_false_r in H. inv H. 
Qed.
  
Definition free_Effect vargs m:=
       match vargs with 
          Vptr b1 lo :: nil =>
          match Mem.load Mint32 m b1 (Int.unsigned lo - 4)
          with Some (Vint sz) =>
            fun b z => eq_block b b1 && zlt 0 (Int.unsigned sz) &&
                     zle (Int.unsigned lo - 4) z &&
                     zlt z (Int.unsigned lo + Int.unsigned sz)
          | _ => fun b z => false
          end
       | _ => fun b z => false
       end.

Lemma free_Effect_unchOn: forall {F V : Type} (g : Genv.t F V)
        vargs m t vres m' (FR : external_call EF_free g vargs m t vres m'),
     Mem.unchanged_on (fun b z => free_Effect vargs m b z = false) m m'.
Proof. intros. inv FR. 
  eapply Mem.free_unchanged_on. eassumption.
  intros. unfold free_Effect. rewrite H.
    destruct (eq_block b b); simpl.
      clear e. destruct (zlt 0 (Int.unsigned sz)); simpl; try omega. 
      clear l. destruct (zlt 0 (Int.unsigned sz)); simpl; try omega.
      clear l. destruct (zle (Int.unsigned lo - 4) i); simpl; try omega.
      clear l. destruct (zlt i (Int.unsigned lo + Int.unsigned sz)); simpl; try omega.
      discriminate.
   elim n; trivial.
Qed.

Lemma freeEffect_valid_block vargs m: forall b z 
        (FR: free_Effect vargs m b z = true),
      Mem.valid_block m b.
Proof. intros.
  destruct vargs; inv FR.
  destruct v; inv H0.
  destruct vargs; inv H1.
  remember (Mem.load Mint32 m b0 (Int.unsigned i - 4)) as d.
  destruct d; apply eq_sym in Heqd.
    destruct v; inv H0.
    destruct (eq_block b b0); subst; simpl in *.
      apply Mem.load_valid_access in Heqd.
      eapply Mem.valid_access_valid_block.
      eapply Mem.valid_access_implies; try eassumption. constructor.
    inv H1.
  inv H0.
Qed.

Definition BuiltinEffect  {F V: Type} (ge: Genv.t F V) (ef: external_function)
          (vargs:list val) (m:mem): block -> Z -> bool :=
  match ef with
    EF_malloc => EmptyEffect
  | EF_free => free_Effect vargs m
  | EF_memcpy sz a => memcpy_Effect sz vargs m
  | _ => fun b z => false
  end.

Lemma malloc_Effect_unchOn: forall {F V : Type} (g : Genv.t F V)
         vargs m t vres m' (EF: external_call EF_malloc g vargs m t vres m'),
     Mem.unchanged_on
      (fun b z => BuiltinEffect g EF_malloc vargs m b z = false) m m'.
Proof. intros.
       simpl. inv EF.
       split; intros.
          unfold Mem.perm. rewrite (Mem.store_access _ _ _ _ _ _ H0).
          split; intros. 
            eapply Mem.perm_alloc_1; eassumption. 
            eapply Mem.perm_alloc_4; try eassumption.
              intros N. subst. eapply Mem.fresh_block_alloc; eassumption.
        rewrite <- (AllocContentsOther _ _ _ _ _ H). 
                rewrite (Mem.store_mem_contents _ _ _ _ _ _ H0).
                rewrite PMap.gso. trivial.
                intros N; subst. apply Mem.perm_valid_block in H2.
                    eapply Mem.fresh_block_alloc; eassumption.
              intros N; subst. apply Mem.perm_valid_block in H2.
                    eapply Mem.fresh_block_alloc; eassumption.
Qed.

Section BUILTINS.
Require Import String.
Inductive is_I64_builtinS : String.string -> signature -> Prop :=
  bltin_neglS: is_I64_builtinS "__builtin_negl" sig_l_l
| bltin_addlS: is_I64_builtinS "__builtin_addl" sig_ll_l 
| bltin_sublS: is_I64_builtinS "__builtin_subl" sig_ll_l
| bltin_mullS: is_I64_builtinS "__builtin_mull" sig_ii_l.

Lemma is_I64_builtinS_dec name sg:
 {is_I64_builtinS name sg} + {~is_I64_builtinS name sg} .
Proof.
destruct (signature_eq sg sig_l_l); subst.
{ destruct (String.string_dec name "__builtin_negl").
  + subst; try solve[left; constructor].
  + right; intros N; inv N; intuition. }
destruct (signature_eq sg sig_ll_l); subst.
{ destruct (String.string_dec name "__builtin_addl").
  + subst; try solve[left; constructor].
  + destruct (String.string_dec name "__builtin_subl").
    - subst; try solve[left; constructor].
    - right; intros N; inv N; intuition. }
destruct (signature_eq sg sig_ii_l); subst.
{ destruct (String.string_dec name "__builtin_mull").
  + subst; try solve[left; constructor].
  + right; intros N; inv N; intuition. }
right; intros N; inv N; intuition.
Qed.

Definition observableEF (ef: external_function): Prop :=
  match ef with
    EF_malloc => False (*somewhat arbitrary*)
  | EF_free => False (*somewhat arbitrary*)
  | EF_memcpy _ _ => False
  | EF_builtin name sg => ~is_I64_builtinS name sg
  | EF_external name sg => ~is_I64_helperS name sg
  | _ => True
  end.

Lemma observableEF_dec ef: {observableEF ef} + {~observableEF ef}.
Proof.
destruct ef; simpl; try solve[left; trivial].
  destruct (is_I64_helperS_dec name sg).
    right. intros N. apply (N i). 
    left; trivial. 
  destruct (is_I64_builtinS_dec name sg).
    right. intros N. apply (N i). 
    left; trivial. 
  right; intros N. trivial.
  right; intros N. trivial.
  right; intros N. trivial.
Qed.

Definition EFisHelper ef :=
match ef with 
    EF_builtin name sg => is_I64_builtinS name sg
  | EF_external name sg => is_I64_helperS name sg
  | _ => False
end.

Lemma EFhelpers ef: EFisHelper ef -> ~ observableEF ef.
Proof. unfold observableEF; intros. intros N.
destruct ef; simpl in H; trivial. apply (N H). apply (N H).
Qed. 

Lemma EFhelpersE name sg: 
  ~ observableEF (EF_external name sg) ->
  is_I64_helperS name sg.
Proof. 
unfold observableEF. intros.
destruct (is_I64_helperS_dec name sg). 
  trivial.
  elim (H n). 
Qed. 

Lemma EFhelpersB name sg: 
  ~observableEF (EF_builtin name sg) ->
  is_I64_builtinS name sg.
Proof. 
unfold observableEF. intros.
destruct (is_I64_builtinS_dec name sg). 
  trivial.
  elim (H n). 
Qed. 

Lemma obs_efB name sg : is_I64_builtinS name sg ->
     ~ observableEF (EF_builtin name sg).
Proof. intros. unfold observableEF. 
  intros N. apply (N H).
Qed.

Lemma obs_efE name sg : is_I64_helperS name sg ->
     ~ observableEF (EF_external name sg).
Proof. intros. unfold observableEF. 
  intros N. apply (N H).
Qed.


(** * From SelectLongproof: Axiomatization of the helper functions *)

Definition external_implements (name: string) (sg: signature) (vargs: list val) (vres: val) : Prop :=
  forall F V (ge: Genv.t F V) m,
  external_call (EF_external name sg) ge vargs m E0 vres m
  (*NEW*) /\ (forall E' vres' m', external_call (EF_external name sg) ge vargs m E' vres' m' -> 
                                   m'=m /\ vres'=vres/\E'=E0).

Definition builtin_implements (name: string) (sg: signature) (vargs: list val) (vres: val) : Prop :=
  forall F V (ge: Genv.t F V) m,
  external_call (EF_builtin name sg) ge vargs m E0 vres m
  (*NEW*) /\ (forall E' vres' m', external_call (EF_builtin name sg) ge vargs m E' vres' m' -> 
                                  m'=m /\ vres'=vres/\E'=E0).

Definition i64_helpers_correct: Prop :=
    (forall x z, Val.longoffloat x = Some z -> external_implements "__i64_dtos" sig_f_l (x::nil) z)
 /\ (forall x z, Val.longuoffloat x = Some z -> external_implements "__i64_dtou" sig_f_l (x::nil) z)
 /\ (forall x z, Val.floatoflong x = Some z -> external_implements "__i64_stod" sig_l_f (x::nil) z)
 /\ (forall x z, Val.floatoflongu x = Some z -> external_implements "__i64_utod" sig_l_f (x::nil) z)
 /\ (forall x z, Val.singleoflong x = Some z -> external_implements "__i64_stof" sig_l_s (x::nil) z)
 /\ (forall x z, Val.singleoflongu x = Some z -> external_implements "__i64_utof" sig_l_s (x::nil) z)
 /\ (forall x, builtin_implements "__builtin_negl" sig_l_l (x::nil) (Val.negl x))
 /\ (forall x y, builtin_implements "__builtin_addl" sig_ll_l (x::y::nil) (Val.addl x y))
 /\ (forall x y, builtin_implements "__builtin_subl" sig_ll_l (x::y::nil) (Val.subl x y))
 /\ (forall x y, builtin_implements "__builtin_mull" sig_ii_l (x::y::nil) (Val.mull' x y))
 /\ (forall x y z, Val.divls x y = Some z -> external_implements "__i64_sdiv" sig_ll_l (x::y::nil) z)
 /\ (forall x y z, Val.divlu x y = Some z -> external_implements "__i64_udiv" sig_ll_l (x::y::nil) z)
 /\ (forall x y z, Val.modls x y = Some z -> external_implements "__i64_smod" sig_ll_l (x::y::nil) z)
 /\ (forall x y z, Val.modlu x y = Some z -> external_implements "__i64_umod" sig_ll_l (x::y::nil) z)
 /\ (forall x y, external_implements "__i64_shl" sig_li_l (x::y::nil) (Val.shll x y))
 /\ (forall x y, external_implements "__i64_shr" sig_li_l (x::y::nil) (Val.shrlu x y))
 /\ (forall x y, external_implements "__i64_sar" sig_li_l (x::y::nil) (Val.shrl x y)).

Definition helper_declared {F V: Type} (ge: Genv.t (AST.fundef F) V) (id: ident) (name: string) (sg: signature) : Prop :=
  exists b, Genv.find_symbol ge id = Some b
         /\ Genv.find_funct_ptr ge b = Some (External (EF_external name sg))
         /\ ~observableEF (EF_external name sg). (*ADDED*)

Definition helper_functions_declared {F V: Type} (ge: Genv.t (AST.fundef F) V) (hf: helper_functions) : Prop :=
     helper_declared ge hf.(i64_dtos) "__i64_dtos" sig_f_l
  /\ helper_declared ge hf.(i64_dtou) "__i64_dtou" sig_f_l
  /\ helper_declared ge hf.(i64_stod) "__i64_stod" sig_l_f
  /\ helper_declared ge hf.(i64_utod) "__i64_utod" sig_l_f
  /\ helper_declared ge hf.(i64_stof) "__i64_stof" sig_l_s
  /\ helper_declared ge hf.(i64_utof) "__i64_utof" sig_l_s
  /\ helper_declared ge hf.(i64_sdiv) "__i64_sdiv" sig_ll_l
  /\ helper_declared ge hf.(i64_udiv) "__i64_udiv" sig_ll_l
  /\ helper_declared ge hf.(i64_smod) "__i64_smod" sig_ll_l
  /\ helper_declared ge hf.(i64_umod) "__i64_umod" sig_ll_l
  /\ helper_declared ge hf.(i64_shl) "__i64_shl" sig_li_l
  /\ helper_declared ge hf.(i64_shr) "__i64_shr" sig_li_l
  /\ helper_declared ge hf.(i64_sar) "__i64_sar" sig_li_l.

Context {F V: Type} (ge: Genv.t (AST.fundef F) V).
Variable hf : helper_functions.

Hypothesis HELPERS: helper_functions_declared ge hf.
Hypothesis helpers_correct: i64_helpers_correct.


(** * **********End of SelectLong proof excerpt **************************** *)

Lemma extcall_mem_step g ef vargs m t vres m'
      (NOBS: ~observableEF ef):
      @external_call ef g vargs m t vres m' ->
      mem_step m m'.
Admitted.
(*Proof. 
intros. (* destruct HELPERS as [HLP1 [HLP2 HLP3]].*)
destruct ef. apply EFhelpersE in NOBS.
inv NOBS.
+ destruct helpers_correct as [HLP _]. simpl in HLP.
admit. inv H. simpl in *.
SearchAbout external_functions_sem.
 inv H; try apply mem_step_refl;
    try solve [elim NOBS; trivial].
+ eapply mem_step_trans.
    eapply mem_step_alloc. eassumption.
    eapply mem_step_store; eassumption.
+ eapply mem_step_free; eassumption. 
+ eapply mem_step_storebytes; eassumption.
Qed.
*)
Lemma BuiltinEffect_unchOn:
    forall {F V:Type} ef (g : Genv.t F V) vargs m t vres m'
    (OBS: ~ observableEF ef),
    external_call ef g vargs m t vres m' -> 
    Mem.unchanged_on
      (fun b z=> BuiltinEffect g ef vargs m b z = false) m m'.
Admitted. (*
Proof. intros.
  destruct ef.
    (*EF_external*) inv H. admit. (*TODO
       inv H. apply Mem.unchanged_on_refl.*)
    (*EF_builtin - same proof as previous case*) admit. (*TODO simpl in *.
       inversion H. apply Mem.unchanged_on_refl.*)
    simpl in OBS. intuition.
    simpl in OBS. intuition. 
    simpl in OBS. intuition. 
    simpl in OBS. intuition. 
    (*case EF_malloc*)
       eapply  malloc_Effect_unchOn. eassumption.
    (*case EF_free*)
       eapply free_Effect_unchOn; eassumption.
    (*case EE_memcpy*)
       inv H. clear - H1 H6 H7.
       eapply memcpy_Effect_unchOn; try eassumption. 
    simpl in OBS. intuition.
    simpl in OBS. intuition. 
    simpl in OBS. intuition.
    simpl in OBS. intuition.
Admitted.

Lemma nonobs_extcall_curWR {F V} (g:Genv.t F V) hf ef (vargs:list val) (m:mem) (t:trace) vres (m':mem) 
      (EC: @external_call ef (*F V*) (Genv.to_senv g) vargs m t vres m')
      (NOBS: ~ observableEF hf ef) b z (EFF: BuiltinEffect g ef vargs m b z = true):
     Mem.perm m b z Cur Writable.
Proof.
  destruct ef; simpl in *; try discriminate; clear NOBS; inv EC; simpl in *.
  - destruct (Mem.load Mint32 m b0 (Int.unsigned lo - 4)); inv EFF.
    destruct v; inv H3. inv H.
    apply Mem.free_range_perm in H1.
    destruct (eq_block b b0); try discriminate; subst b0; simpl in *.
    destruct (zlt 0 (Int.unsigned sz)); try discriminate; simpl in *.
    destruct (zle (Int.unsigned lo - 4) z); try discriminate; simpl in *.
    destruct (zlt z (Int.unsigned lo + Int.unsigned sz)); try discriminate; simpl in *.
    eapply Mem.perm_implies. apply H1. omega. constructor.
  - destruct (eq_block b bdst); try discriminate; subst bdst; simpl in *.
    destruct (zle (Int.unsigned odst) z); try discriminate; simpl in *.
    destruct (zlt z (Int.unsigned odst + sz)); try discriminate; simpl in *.
    apply Mem.loadbytes_length in H5.
    eapply Mem.storebytes_range_perm; eauto.
    rewrite H5, nat_of_Z_eq; omega.
Qed.*)

Lemma BuiltinEffect_valid_block:
    forall {F V:Type} ef (g : Genv.t F V) vargs m b z,
     BuiltinEffect g ef vargs m b z = true -> Mem.valid_block m b. 
Proof. intros. unfold BuiltinEffect in H. 
  destruct ef; try discriminate.
    eapply freeEffect_valid_block; eassumption.
    eapply memcpy_Effect_validblock; eassumption.
Qed.
(*
(*takes the role of external_call_mem_inject
  Since inlinables write at most to vis, we use the
  Mem-Unchanged_on condition loc_out_of_reach, rather than
  local_out_of_reach as in external calls.*)
Lemma inlineable_extern_inject: forall {F V TF TV:Type}
       (ge:Genv.t F V) (tge:Genv.t TF TV) (GDE: genvs_domain_eq ge tge) 
       (SymbPres: forall s, Genv.find_symbol tge s = Genv.find_symbol ge s)
       hf ef vargs m t vres m1 mu tm vargs'
       (WD: SM_wd mu) (SMV: sm_valid mu m tm) (RC: REACH_closed m (vis mu))
       (Glob: forall b, isGlobalBlock ge b = true -> 
              frgnBlocksSrc mu b = true)
       (OBS: ~ observableEF hf ef),
       meminj_preserves_globals ge (as_inj mu) ->
       external_call ef ge vargs m t vres m1 ->
       Mem.inject (as_inj mu) m tm ->
       Val.inject_list (restrict (as_inj mu) (vis mu)) vargs vargs' ->
       exists mu' vres' tm1,
         external_call ef tge vargs' tm t vres' tm1 /\
         val_inject (restrict (as_inj mu') (vis mu')) vres vres' /\
         Mem.inject (as_inj mu') m1 tm1 /\
         Mem.unchanged_on (loc_unmapped (restrict (as_inj mu) (vis mu))) m m1 /\
         Mem.unchanged_on (loc_out_of_reach (restrict (as_inj mu) (vis mu)) m) tm tm1 /\
         intern_incr mu mu' /\
         sm_inject_separated mu mu' m tm /\
         globals_separate ge mu mu' /\
         sm_locally_allocated mu mu' m tm m1 tm1 /\
         SM_wd mu' /\ sm_valid mu' m1 tm1 /\
         REACH_closed m1 (vis mu').
Admitted.
(*Proof. intros.
destruct ef; simpl in H0. 
+ (*EFexternal*)
      admit. (*eapply helpers_inject; try eassumption.
      apply EFhelpersE; eassumption. *)
+   (*EF_builtin*)
      admit. (*eapply helpers_inject; try eassumption.
      apply EFhelpersE; eassumption. *)
+   simpl in OBS; intuition.
+   simpl in OBS; intuition.
+  (*case EF_malloc*)
    inv H0. inv H2. inv H8. inv H6. clear OBS.
    exploit alloc_parallel_intern; eauto. apply Zle_refl. apply Zle_refl.
    intros [mu' [tm' [tb [TALLOC [INJ' [INC [AI1 [AI2 [SEP [LOCALLOC [WD' [SMV' RC']]]]]]]]]]]].
    exploit Mem.store_mapped_inject. eexact INJ'. eauto. eauto. 
    instantiate (1 := Vint n). auto.   
    intros [tm1 [ST' INJ1]].
    assert (visb': vis mu' b = true).
        apply sm_locally_allocatedChar in LOCALLOC.
        unfold vis. destruct LOCALLOC as [_ [_ [LOC _]]]. rewrite LOC.
        rewrite (freshloc_alloc _ _ _ _ _ H3).
        destruct (eq_block b b); subst; simpl. intuition. elim n0; trivial.
    exists mu'; exists (Vptr tb Int.zero); exists tm1; intuition.
      econstructor; eauto.
      econstructor. eapply restrictI_Some; eassumption.
      rewrite Int.add_zero. trivial.
    split; unfold loc_unmapped; intros. unfold Mem.perm. 
         rewrite (Mem.store_access _ _ _ _ _ _ H4).
         split; intros.
         eapply Mem.perm_alloc_1; eassumption.
         eapply Mem.perm_alloc_4; try eassumption.
         intros N; subst; eapply (Mem.fresh_block_alloc _ _ _ _ _ H3 H5).
      rewrite (Mem.store_mem_contents _ _ _ _ _ _ H4).
        apply Mem.perm_valid_block in H5.
        rewrite PMap.gso. 
          rewrite (AllocContentsOther1 _ _ _ _ _ H3). trivial. 
          intros N; subst; eapply (Mem.fresh_block_alloc _ _ _ _ _ H3 H5).
        intros N; subst; eapply (Mem.fresh_block_alloc _ _ _ _ _ H3 H5).
    split; unfold loc_out_of_reach; intros.
         unfold Mem.perm. 
         rewrite (Mem.store_access _ _ _ _ _ _ ST').
         split; intros.
         eapply Mem.perm_alloc_1; eassumption.
         eapply Mem.perm_alloc_4; try eassumption.
         intros N; subst. eapply (Mem.fresh_block_alloc _ _ _ _ _ TALLOC H5).
      rewrite (Mem.store_mem_contents _ _ _ _ _ _ ST').
        apply Mem.perm_valid_block in H5.
        rewrite PMap.gso. 
          rewrite (AllocContentsOther1 _ _ _ _ _ TALLOC). trivial. 
          intros N; subst; eapply (Mem.fresh_block_alloc _ _ _ _ _ TALLOC H5).
          intros N; subst; eapply (Mem.fresh_block_alloc _ _ _ _ _ TALLOC H5).
          eapply intern_incr_globals_separate; eauto.
    rewrite sm_locally_allocatedChar.
      rewrite sm_locally_allocatedChar in LOCALLOC.
      destruct LOCALLOC as [LAC1 [LAC2 [LAC3 [LAC4 [LAC5 LOC6]]]]].
      rewrite LAC1, LAC2, LAC3, LAC4, LAC5, LOC6; clear LAC1 LAC2 LAC3 LAC4 LAC5 LOC6.
           repeat split; extensionality bb.
             rewrite (freshloc_alloc _ _ _ _ _ H3).
             rewrite <- (freshloc_trans m m'), (freshloc_alloc _ _ _ _ _ H3), (store_freshloc _ _ _ _ _ _ H4).
             rewrite orb_false_r. trivial.
             eapply alloc_forward; eassumption. eapply store_forward; eassumption.

             rewrite (freshloc_alloc _ _ _ _ _ TALLOC).
             rewrite <- (freshloc_trans tm tm'), (freshloc_alloc _ _ _ _ _ TALLOC), (store_freshloc _ _ _ _ _ _ ST').
             rewrite orb_false_r. trivial.
             eapply alloc_forward; eassumption. eapply store_forward; eassumption.

             rewrite (freshloc_alloc _ _ _ _ _ H3).
             rewrite <- (freshloc_trans m m'), (freshloc_alloc _ _ _ _ _ H3), (store_freshloc _ _ _ _ _ _ H4).
             rewrite orb_false_r. trivial.
             eapply alloc_forward; eassumption. eapply store_forward; eassumption.

             rewrite (freshloc_alloc _ _ _ _ _ TALLOC).
             rewrite <- (freshloc_trans tm tm'), (freshloc_alloc _ _ _ _ _ TALLOC), (store_freshloc _ _ _ _ _ _ ST').
             rewrite orb_false_r. trivial.
             eapply alloc_forward; eassumption. eapply store_forward; eassumption.

        split; intros; eapply store_forward; try eassumption.
          rewrite sm_locally_allocatedChar in LOCALLOC.
          destruct LOCALLOC as [LAC1 _]. unfold DOM in H2; rewrite LAC1 in H2; clear LAC1.
          rewrite (freshloc_alloc _ _ _ _ _ H3) in H2.
          destruct (eq_block b1 b); subst; simpl in *.
            eapply Mem.valid_new_block; eassumption.
          rewrite orb_false_r in H2. 
            eapply Mem.valid_block_alloc; try eassumption.
            eapply SMV; eassumption.

          rewrite sm_locally_allocatedChar in LOCALLOC.
          destruct LOCALLOC as [_ [LAC2 _]]. unfold RNG in H2; rewrite LAC2 in H2; clear LAC2.
          rewrite (freshloc_alloc _ _ _ _ _ TALLOC) in H2.
          destruct (eq_block b2 tb); subst; simpl in *.
            eapply Mem.valid_new_block; eassumption.
          rewrite orb_false_r in H2. 
            eapply Mem.valid_block_alloc; try eassumption.
            eapply SMV; eassumption.
      eapply (REACH_Store m'); try eassumption.
      intros ? getBl. rewrite getBlocks_char in getBl. 
         destruct getBl as [zz [ZZ | ZZ]]; inv ZZ.
+ (*case EF_free*)
    inv H0. inv H2. inv H9. inv H7.
    destruct (restrictD_Some _ _ _ _ _ H6) as [AIb VISb].
    exploit free_parallel_inject; try eassumption.
    intros [tm1 [TFR Inj1]].
    exploit (Mem.load_inject (as_inj mu) m); try eassumption.
    intros [v [TLD Vinj]]. inv Vinj.
    assert (Mem.range_perm m b (Int.unsigned lo - 4) (Int.unsigned lo + Int.unsigned sz) Cur Freeable).
      eapply Mem.free_range_perm; eauto.
    exploit Mem.address_inject. eapply H1. 
      apply Mem.perm_implies with Freeable; auto with mem.
      apply H0. instantiate (1 := lo). omega.
      eassumption. 
    intro EQ.
    assert (Mem.range_perm tm b2 (Int.unsigned lo + delta - 4) (Int.unsigned lo + delta + Int.unsigned sz) Cur Freeable).
      red; intros. 
      replace ofs with ((ofs - delta) + delta) by omega.
      eapply Mem.perm_inject. eassumption. eassumption. eapply H0. omega.
(*    destruct (Mem.range_perm_free _ _ _ _ H2) as [m2' FREE].*)
    exists mu; eexists; exists tm1; split.
      simpl. econstructor.
       rewrite EQ. replace (Int.unsigned lo + delta - 4) with (Int.unsigned lo - 4 + delta) by omega.
       eauto. auto. 
      rewrite EQ. clear - TFR.
        assert (Int.unsigned lo + delta - 4 = Int.unsigned lo - 4 + delta). omega. rewrite H; clear H.
        assert (Int.unsigned lo + delta + Int.unsigned sz = Int.unsigned lo + Int.unsigned sz + delta). omega. rewrite H; clear H.
        assumption.
     intuition.  

     eapply Mem.free_unchanged_on; eauto. 
       unfold loc_unmapped; intros. congruence.

     eapply Mem.free_unchanged_on; eauto.   
       unfold loc_out_of_reach; intros. red; intros. eelim H8; eauto. 
       apply Mem.perm_cur_max. apply Mem.perm_implies with Freeable; auto with mem.
       apply H0. omega.

       apply intern_incr_refl.
       apply sm_inject_separated_same_sminj.
       apply gsep_refl.
     apply sm_locally_allocatedChar.
       repeat split; try extensionality bb; simpl.
       rewrite (freshloc_free _ _ _ _ _ H5). clear. intuition.
       rewrite (freshloc_free _ _ _ _ _ TFR). clear. intuition.
       rewrite (freshloc_free _ _ _ _ _ H5). clear. intuition.
       rewrite (freshloc_free _ _ _ _ _ TFR). clear. intuition.
     split; intros; eapply Mem.valid_block_free_1; try eassumption.
       eapply SMV; assumption. eapply SMV; assumption.
     eapply REACH_closed_free; eassumption.
+ (*memcpy*)
     clear OBS.
     inv H0. 
  exploit Mem.loadbytes_length; eauto. intros LEN.
  assert (RPSRC: Mem.range_perm m bsrc (Int.unsigned osrc) (Int.unsigned osrc + sz) Cur Nonempty).
    eapply Mem.range_perm_implies. eapply Mem.loadbytes_range_perm; eauto. auto with mem.
  assert (RPDST: Mem.range_perm m bdst (Int.unsigned odst) (Int.unsigned odst + sz) Cur Nonempty).
    replace sz with (Z_of_nat (length bytes)).
    eapply Mem.range_perm_implies. eapply Mem.storebytes_range_perm; eauto. auto with mem.
    rewrite LEN. apply nat_of_Z_eq. omega.
  assert (PSRC: Mem.perm m bsrc (Int.unsigned osrc) Cur Nonempty).
    apply RPSRC. admit. (*TODO omega.*)
  assert (PDST: Mem.perm m bdst (Int.unsigned odst) Cur Nonempty).
    apply RPDST. admit. (*omega. TODO*)
  inv H2. inv H12. inv H14. inv H15. inv H12.
  destruct (restrictD_Some _ _ _ _ _ H11).
  destruct (restrictD_Some _ _ _ _ _ H13).
  exploit Mem.address_inject.  eauto. eexact PSRC. eauto. intros EQ1.
  exploit Mem.address_inject.  eauto. eexact PDST. eauto. intros EQ2.
  exploit Mem.loadbytes_inject; eauto. intros [bytes2 [A B]].
  exploit Mem.storebytes_mapped_inject; eauto. intros [m2' [C D]].
  exists mu; exists Vundef; exists m2'.
  split. econstructor; try rewrite EQ1; try rewrite EQ2; eauto. 
  (*new:*)intros.
   eapply Mem.aligned_area_inject with (m := m); eauto.
  (*new:*)intros.
   eapply Mem.aligned_area_inject with (m := m); eauto.
  eapply Mem.disjoint_or_equal_inject with (m := m); eauto.
  apply Mem.range_perm_max with Cur; auto.
  apply Mem.range_perm_max with Cur; auto.
  split. admit. (*new condition -- todo*)
  split. constructor.
  split. auto.
  split. eapply Mem.storebytes_unchanged_on; eauto.
         unfold loc_unmapped; intros. rewrite H11. congruence.
  split. eapply Mem.storebytes_unchanged_on; eauto.
         unfold loc_out_of_reach; intros. red; intros.
         eapply (H16 _ _ H11). 
             apply Mem.perm_cur_max. apply Mem.perm_implies with Writable; auto with mem.
             eapply Mem.storebytes_range_perm; eauto.  
             erewrite list_forall2_length; eauto. 
             omega.
  split. apply intern_incr_refl.
  split. apply sm_inject_separated_same_sminj.
  split. apply gsep_refl.
  split. apply sm_locally_allocatedChar.
       repeat split; try extensionality bb; simpl.
       rewrite (storebytes_freshloc _ _ _ _ _ H10). clear. intuition.
       rewrite (storebytes_freshloc _ _ _ _ _ C). clear. intuition.
       rewrite (storebytes_freshloc _ _ _ _ _ H10). clear. intuition.
       rewrite (storebytes_freshloc _ _ _ _ _ C). clear. intuition.
  split; trivial. 
  split. split; intros.
       eapply storebytes_forward; try eassumption.
          eapply SMV; trivial.
       eapply storebytes_forward; try eassumption.
          eapply SMV; trivial.
  destruct (loadbytes_D _ _ _ _ _ H9); clear A C.
   clear RPSRC RPDST PSRC PDST H8 H11 H3 H5 H6 H7 EQ1 EQ2 B D.  
  intros. eapply REACH_Storebytes; try eassumption.
          intros. eapply RC. subst bytes.
          destruct (in_split _ _ H3) as [bts1 [bts2 Bytes]]; clear H3.
          specialize (getN_range _ _ _ _ _ _ Bytes). intros.
          apply getN_aux in Bytes. 
          eapply REACH_cons. instantiate(1:=bsrc).
            eapply REACH_nil. assumption.
            Focus 2. apply eq_sym. eassumption. 
            eapply H15. clear - H3 H4. 
            split. specialize (Zle_0_nat (length bts1)). intros. omega.
                   apply inj_lt in H3. rewrite nat_of_Z_eq in H3; omega.
    simpl in OBS; intuition.
    simpl in OBS; intuition.
    simpl in OBS; intuition. 
Qed.
*)
*)
Lemma BuiltinEffect_Propagate: forall {F V TF TV:Type}
       (ge:Genv.t F V) (tge:Genv.t TF TV) ef m vargs t vres m'
       (EC : external_call ef ge vargs m t vres m') mu m2 tvargs
       (ArgsInj : Val.inject_list (restrict (as_inj mu) (vis mu)) vargs tvargs)
       (WD : SM_wd mu) (MINJ : Mem.inject (as_inj mu) m m2),
     forall b ofs, BuiltinEffect tge ef tvargs m2 b ofs = true ->
       visTgt mu b = true /\
       (locBlocksTgt mu b = false ->
        exists b1 delta1,
           foreign_of mu b1 = Some (b, delta1) /\
           BuiltinEffect ge ef vargs m b1 (ofs - delta1) = true /\
           Mem.perm m b1 (ofs - delta1) Max Nonempty).
Proof.
 intros. destruct ef; try inv H.
  (*free*)
    simpl in EC. inv EC. 
    inv ArgsInj. inv H7. inv H5.
    rewrite H1. unfold free_Effect in H1.
    destruct (restrictD_Some _ _ _ _ _ H6) as [AIb VISb].
    exploit (Mem.load_inject (as_inj mu) m); try eassumption.
    intros [v [TLD Vinj]]. inv Vinj.
    assert (RP: Mem.range_perm m b0 (Int.unsigned lo - 4) (Int.unsigned lo + Int.unsigned sz) Cur Freeable).
      eapply Mem.free_range_perm; eauto.
    exploit Mem.address_inject. eapply MINJ. 
      apply Mem.perm_implies with Freeable; auto with mem.
      apply RP. instantiate (1 := lo). omega.
      eassumption. 
    intro EQ.
    rewrite EQ in *.
    assert (Arith4: Int.unsigned lo - 4 + delta = Int.unsigned lo + delta - 4) by omega.
    rewrite Arith4, TLD in *.
    destruct (eq_block b b2); subst; simpl in *; try inv H1.
    rewrite H, H4.
    split. eapply visPropagateR; eassumption.
    intros. exists b0, delta.
    rewrite restrict_vis_foreign_local in H6; trivial.
    destruct (joinD_Some _ _ _ _ _ H6) as [FRG | [FRG LOC]]; clear H6.
    Focus 2. destruct (local_DomRng _ WD _ _ _ LOC). rewrite H5 in H1; discriminate.
    split; trivial.
    destruct (eq_block b0 b0); simpl in *.
    Focus 2. elim n; trivial. 
    clear e. 
        destruct (zlt 0 (Int.unsigned sz)); simpl in *; try inv H4.
        destruct (zle (Int.unsigned lo + delta - 4) ofs); simpl in *; try inv H5.
        destruct (zlt ofs (Int.unsigned lo + delta + Int.unsigned sz)); simpl in *; try inv H4.
        destruct (zle (Int.unsigned lo - 4) (ofs - delta)); simpl in *; try omega.
        split. destruct (zlt (ofs - delta) (Int.unsigned lo + Int.unsigned sz)); trivial.
                 omega. 
        eapply Mem.perm_implies. 
          eapply Mem.perm_max. eapply RP. split; trivial. omega.
          constructor. 
     (*memcpy*)
        simpl in EC. inv EC. 
        inv ArgsInj. inv H12. inv H10. inv H11. inv H14. 
        rewrite H1. unfold memcpy_Effect in H1.
        destruct (eq_block b b2); subst; simpl in *; try inv H1.
        destruct (zle (Int.unsigned (Int.add odst (Int.repr delta))) ofs); simpl in *; try inv H9. 
        destruct (zlt ofs (Int.unsigned (Int.add odst (Int.repr delta)) + sz)); simpl in *; try inv H1.
        destruct (valid_block_dec m2 b2); simpl in *; try inv H9.
        split. eapply visPropagateR; eassumption.
        intros. exists bdst, delta.
        destruct (restrictD_Some _ _ _ _ _ H12).
        exploit Mem.address_inject.
           eapply MINJ.
           eapply Mem.storebytes_range_perm. eassumption.
           split. apply Z.le_refl.
             rewrite (Mem.loadbytes_length _ _ _ _ _ H6).
               rewrite nat_of_Z_eq; omega.
           eassumption.
        intros UNSIG; rewrite UNSIG in *.
        assert (MP: Mem.perm m bdst (ofs - delta) Max Nonempty).
           eapply Mem.perm_implies.
             eapply Mem.perm_max. 
             eapply Mem.storebytes_range_perm. eassumption.
             rewrite (Mem.loadbytes_length _ _ _ _ _ H6).
             rewrite nat_of_Z_eq; omega.
           constructor. 
        rewrite (restrict_vis_foreign_local _ WD) in H12.
        destruct (joinD_Some _ _ _ _ _ H12) as [FRG | [FRG LOC]]; clear H12.
          split; trivial. split; trivial.
          destruct (eq_block bdst bdst); simpl. clear e.
            destruct (zle (Int.unsigned odst) (ofs - delta)); simpl.
              destruct (zlt (ofs - delta) (Int.unsigned odst + sz)); simpl.
                destruct (valid_block_dec m bdst); trivial.
                elim n. eapply Mem.perm_valid_block; eassumption.
              omega.
            omega.
          elim n; trivial.
        destruct (local_DomRng _ WD _ _ _ LOC).
          rewrite H13 in H1. discriminate.
  inv H8.
  inv H8.
Qed.

Lemma BuiltinEffect_Propagate': forall {F V TF TV:Type}
       (ge:Genv.t F V) (tge:Genv.t TF TV) ef m vargs t vres m'
       (EC : external_call' ef ge vargs m t vres m') mu m2 tvargs
       (ArgsInj : Val.inject_list (restrict (as_inj mu) (vis mu)) vargs tvargs)
       (WD : SM_wd mu) (MINJ : Mem.inject (as_inj mu) m m2),
     forall b ofs, BuiltinEffect tge ef tvargs m2 b ofs = true ->
       visTgt mu b = true /\
       (locBlocksTgt mu b = false ->
        exists b1 delta1,
           foreign_of mu b1 = Some (b, delta1) /\
           BuiltinEffect ge ef vargs m b1 (ofs - delta1) = true /\
           Mem.perm m b1 (ofs - delta1) Max Nonempty).
Proof.
 intros. 
 destruct ef; try inv H.
  (*free*)
  { simpl in EC. inv EC. 
    inv ArgsInj. inv H. inv H. inv H0. 
    rewrite H1. unfold free_Effect in H1.
    destruct (restrictD_Some _ _ _ _ _ H7) as [AIb VISb].
    exploit (Mem.load_inject (as_inj mu) m); try eassumption.
    intros [v [TLD Vinj]]. inv Vinj.
    assert (RP: Mem.range_perm m b0 (Int.unsigned lo - 4)
                               (Int.unsigned lo + Int.unsigned sz) Cur Freeable).
    { eapply Mem.free_range_perm; eauto. }
    exploit Mem.address_inject. eapply MINJ. 
    { apply Mem.perm_implies with Freeable; auto with mem.
      apply RP. instantiate (1 := lo). omega. }
    eassumption. 
    intro EQ.
    rewrite EQ in *.
    assert (Arith4: Int.unsigned lo - 4 + delta = Int.unsigned lo + delta - 4) by omega.
    rewrite Arith4, TLD in *.
    destruct (eq_block b b2); subst; simpl in *; try inv H1.
    { rewrite H0,H4.
      split. eapply visPropagateR; eassumption.
      intros. exists b0, delta.
      rewrite restrict_vis_foreign_local in H7; trivial.
      destruct (joinD_Some _ _ _ _ _ H7) as [FRG | [FRG LOC]]; clear H7.
      Focus 2. destruct (local_DomRng _ WD _ _ _ LOC). solve[rewrite H3 in H; discriminate].
      split; trivial.
      inv H2.
      destruct (eq_block b0 b0); simpl in *.
      Focus 2. elim n; trivial. 
      clear e.
      rewrite !andb_true_iff in H0.
      destruct H0 as [[[? ?] ?] ?].
      destruct (zlt 0 (Int.unsigned sz)); simpl in *; try inv H1.
      destruct (zle (Int.unsigned lo + delta - 4) ofs); simpl in *; try inv H2.
      destruct (zlt ofs (Int.unsigned lo + delta + Int.unsigned sz)); simpl in *; try inv H3.
      destruct (zle (Int.unsigned lo - 4) (ofs - delta)); simpl in *; try omega.
      split. destruct (zlt (ofs - delta) (Int.unsigned lo + Int.unsigned sz)); trivial.
      omega. 
      eapply Mem.perm_implies. 
      eapply Mem.perm_max. eapply RP. split; trivial. omega.
      constructor. 
      congruence. }
    { (*b<>b2*)
      destruct vl'; try congruence.
      rewrite !andb_true_iff in H0.
      destruct H0 as [[[? ?] ?] ?].
      destruct (eq_block b b2). subst. congruence. simpl in H. congruence. }}
  { (*memcpy*)
    simpl in EC. inv EC.
    inv ArgsInj. inv H. inv H2. inv H. 
    rewrite H1. unfold memcpy_Effect in H1. inv H.
    inv H0; try congruence. 
    inv H3; try congruence.
    inv H4; try congruence.
    destruct (eq_block b b2); subst; simpl in *; try inv H1.
    destruct (zle (Int.unsigned (Int.add odst (Int.repr delta))) ofs); simpl in *; try inv H4. 
    destruct (zlt ofs (Int.unsigned (Int.add odst (Int.repr delta)) + sz)); simpl in *; try inv H3.
    destruct (valid_block_dec m2 b2); simpl in *; try inv H4.
    split. eapply visPropagateR; eassumption.
    intros. exists bdst, delta.
    destruct (restrictD_Some _ _ _ _ _ H5).
    exploit Mem.address_inject.
    eapply MINJ.
    eapply Mem.storebytes_range_perm; eauto.
    split. apply Z.le_refl.
    rewrite (Mem.loadbytes_length _ _ _ _ _ H12).
    rewrite nat_of_Z_eq; omega. 
    eassumption.
    intros UNSIG; rewrite UNSIG in *.
    assert (MP: Mem.perm m bdst (ofs - delta) Max Nonempty).
    { eapply Mem.perm_implies.
      eapply Mem.perm_max. 
      eapply Mem.storebytes_range_perm. eassumption.
      rewrite (Mem.loadbytes_length _ _ _ _ _ H12).
      rewrite nat_of_Z_eq; omega.
      constructor. }
    rewrite (restrict_vis_foreign_local _ WD) in H5.
    destruct (joinD_Some _ _ _ _ _ H5) as [FRG | [FRG LOC]]; clear H5.
    split; trivial. split; trivial.
    destruct (eq_block bdst bdst); simpl. clear e.
    destruct (zle (Int.unsigned odst) (ofs - delta)); simpl.
    destruct (zlt (ofs - delta) (Int.unsigned odst + sz)); simpl.
    destruct (valid_block_dec m bdst); trivial.
    elim n. eapply Mem.perm_valid_block; eassumption.
    omega.
    omega.
    elim n; trivial.
    destruct (local_DomRng _ WD _ _ _ LOC).
    rewrite H5 in H. discriminate.
  inv H8.
  congruence.
  congruence.
  congruence. }
Qed.
(*
Lemma helpers_EmptyEffect: forall {F V:Type} (ge: Genv.t F V) 
   hf ef args m,
   EFisHelper hf ef -> (BuiltinEffect ge ef args m = EmptyEffect).
Proof. intros.
destruct ef; simpl in *; try reflexivity.
contradiction. contradiction.
Qed.
*)
Require Import ccc26x86.Conventions.
Lemma BuiltinEffect_decode: forall F V (ge: Genv.t F V) ef tls,
 BuiltinEffect ge ef (map tls (loc_arguments (ef_sig ef))) =
 BuiltinEffect ge ef (decode_longs (sig_args (ef_sig ef))
           (map tls (loc_arguments (ef_sig ef)))).
Proof. intros.
  unfold BuiltinEffect. extensionality m. 
  destruct ef; trivial.
Qed.

Section EC_DET.
(*
Context (hf : helper_functions) 
        {F V : Type} (ge : Genv.t F V) (t1 t2: trace) (m m1 m2:mem).

Definition is_I64_helper' hf ef :=
  match ef with
    | EF_external nm sg => is_I64_helper hf (string2ident nm) sg
    | EF_builtin nm sg => is_I64_helper hf (string2ident nm) sg
    | _ => False
  end.

Lemma is_I64_helper'_dec ef : {is_I64_helper' hf ef}+{~is_I64_helper' hf ef}.
Proof.
destruct ef; simpl; auto.
destruct (is_I64_helper_dec hf (string2ident name) sg); auto.
destruct (is_I64_helper_dec hf (string2ident name) sg); auto.
Qed.

Lemma EC'_determ: forall ef args res1 res2,  
      external_call' ef ge args m t1 res1 m1 ->
      external_call' ef ge args m t2 res2 m2 ->
      ~ is_I64_helper' hf ef -> 
      ~ observableEF hf ef -> t1=t2.
Proof. intros.
destruct ef; simpl in H2; intuition.
(*EF_malloc*)
inv H; inv H0. simpl in *. destruct args. inv H; inv H2.
    inv H; inv H3. trivial.
(*EF_free*)
inv H; inv H0. simpl in *. destruct args. inv H; inv H2.
    inv H; inv H3. trivial.
(*EF_memcpy*)
inv H; inv H0. simpl in *. destruct args. inv H; inv H2.
   destruct args. inv H; inv H2. inv H; inv H3. trivial.
Qed.

(** i64_helpers_correct axiomatizes the helpers with empty trace (E0).
  Elsewhere in standard CompCert, these functions are give the
  Event_syscall trace (by extcall_io_sem). Here, we just impose
  determinism on the traces (which is consistent with the E0
  axiomatization used, e.g., in Selectlongproof.v). *)

Axiom EC'_i64_helper_determ: forall ef args res1 res2,  (*SEE NOTE ABOVE*)
      external_call' ef ge args m t1 res1 m1 ->
      external_call' ef ge args m t2 res2 m2 ->
      is_I64_helper' hf ef -> 
      ~ observableEF hf ef -> t1=t2.
*)
End EC_DET.
End BUILTINS. 