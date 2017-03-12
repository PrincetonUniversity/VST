Require Export Axioms.
Require Import Errors.
Require Import Events.
Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import compcert.common.Values.
Require Import Memory.
Require Import Globalenvs.
Require Export Maps.

Require Import Csharpminor.
Require Import Cminor.
Require Import Cminorgen.
Require Import sepcomp.mem_lemmas.
Require Import sepcomp.core_semantics.
Require Import sepcomp.Cminor_coop.
Require Import sepcomp.Csharpminor_coop.
Require Import sepcomp.CminorgenproofRestructured.

Require Import Coq.Program.Equality.

Lemma allocvars_blocks_valid: forall vars E m e m1,
 alloc_variables E m vars e m1 ->
 forall b, Mem.valid_block m b -> Mem.valid_block m1 b.
Proof.
  intros. induction H; simpl in *.  assumption.
  apply IHalloc_variables. eapply Mem.valid_block_alloc; eauto.
Qed.

Lemma storev_valid_block_1:
forall ch m addr v m',
Mem.storev ch m addr v = Some m' ->
(forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof. intros. destruct addr; inv H. eapply Mem.store_valid_block_1; eauto. Qed.

Lemma storev_valid_block_2:
forall ch m addr v m',
Mem.storev ch m addr v = Some m' ->
(forall b, Mem.valid_block m' b -> Mem.valid_block m b).
Proof. intros. destruct addr; inv H. eapply Mem.store_valid_block_2; eauto. Qed.

(*auxiliary lemmas regarding init_mem and genv*)
Lemma add_global_find_symbol: forall {F V} (g: Genv.t F V) m0 m x
    (G: Genv.alloc_global (Genv.add_global g x) m0 x = Some m)
    (N: Genv.genv_next g = Mem.nextblock m0)
    b (VB: Mem.valid_block m b),
    Mem.valid_block m0 b \/
    exists id, Genv.find_symbol (Genv.add_global g x) id = Some b.
Proof. intros.
unfold Genv.alloc_global in G.
destruct x. destruct g0.
   remember (Mem.alloc m0 0 1) as d.
   destruct d; inv G. apply eq_sym in Heqd.
   apply (Mem.drop_perm_valid_block_2 _ _ _ _ _ _ H0) in VB. clear H0.
   apply (Mem.valid_block_alloc_inv _ _ _ _ _ Heqd) in VB.
   destruct VB; subst; try (left; assumption).
     right. unfold Genv.add_global; simpl.
     unfold Genv.find_symbol; simpl.
     rewrite N. apply Mem.alloc_result in Heqd. subst.
     exists i. apply PTree.gss.
remember (Mem.alloc m0 0 (Genv.init_data_list_size (gvar_init v))) as d.
  destruct d; inv G. apply eq_sym in Heqd.
  remember (store_zeros m1 b0 0 (Genv.init_data_list_size (gvar_init v))) as q.
  destruct q; inv H0. apply eq_sym in Heqq.
  remember (Genv.store_init_data_list (Genv.add_global g (i, Gvar v)) m2 b0 0
         (gvar_init v)) as w.
  destruct w; inv H1. apply eq_sym in Heqw.
  apply (Mem.drop_perm_valid_block_2 _ _ _ _ _ _ H0) in VB. clear H0.
  assert (VB2: Mem.valid_block m2 b). unfold Mem.valid_block.
    rewrite <- (@Genv.store_init_data_list_nextblock _ _ _ _ _ _ _ _ Heqw).
    apply VB.
  clear VB Heqw.
  assert (VB1: Mem.valid_block m1 b). unfold Mem.valid_block.
    rewrite <- (@Genv.store_zeros_nextblock _ _ _ _ _ Heqq).
    apply VB2.
  clear VB2 Heqq.
  apply (Mem.valid_block_alloc_inv _ _ _ _ _ Heqd) in VB1.
   destruct VB1; subst; try (left; assumption).
     right. unfold Genv.add_global; simpl.
     unfold Genv.find_symbol; simpl.
     rewrite N. apply Mem.alloc_result in Heqd. subst.
     exists i. apply PTree.gss.
Qed.

Lemma genv_find_add_global_fresh: forall {F V} (g:Genv.t F V) i i0 v0
   (I:i0 <> i),
   Genv.find_symbol (Genv.add_global g (i0, v0)) i =
   Genv.find_symbol g i.
Proof. intros.
    unfold Genv.find_symbol, Genv.genv_symb. simpl. rewrite PTree.gso. reflexivity.
    intros N. apply I; subst; trivial.
Qed.

Lemma genv_find_add_globals_fresh: forall {F V} defs (g:Genv.t F V) i
  (G: ~ In i (map fst defs)),
  Genv.find_symbol (Genv.add_globals g defs) i =  Genv.find_symbol g i.
Proof. intros F V defs.
  induction defs; simpl; intros. trivial.
  destruct a.
  rewrite IHdefs.
    unfold Genv.find_symbol, Genv.genv_symb. simpl. rewrite PTree.gso. reflexivity.
    intros N. apply G; left. subst; simpl; trivial.
  intros N. apply G; right; trivial.
Qed.

Lemma add_globals_find_symbol: forall {F V} (defs : list (ident * globdef F V))
    (R: list_norepet (map fst defs)) (g: Genv.t F V) m0 m
    (G: Genv.alloc_globals (Genv.add_globals g defs) m0 defs = Some m)
    (N: Genv.genv_next g = Mem.nextblock m0)
    b (VB: Mem.valid_block m b),
    Mem.valid_block m0 b \/
    exists id, Genv.find_symbol (Genv.add_globals g defs) id = Some b.
Proof. intros F V defs.
induction defs; simpl; intros.
  inv G. left; trivial.
remember (Genv.alloc_global (Genv.add_globals (Genv.add_global g a) defs) m0 a) as d.
  destruct d; inv G. apply eq_sym in Heqd.
  inv R.
  specialize (IHdefs H3 _ _ _ H0). simpl in *.
  rewrite N in *.
  assert (P: Pos.succ (Mem.nextblock m0) = Mem.nextblock m1).
    clear IHdefs N VB H0.
    rewrite (@Genv.alloc_global_nextblock _ _ _ _ _ _ Heqd). trivial.
  destruct (IHdefs P _ VB); try (right; assumption).
  clear IHdefs P VB H0.
  destruct a. destruct g0. simpl in Heqd.
   remember (Mem.alloc m0 0 1) as t.
   destruct t; inv Heqd. apply eq_sym in Heqt.
   apply (Mem.drop_perm_valid_block_2 _ _ _ _ _ _ H1) in H. clear H1.
   apply (Mem.valid_block_alloc_inv _ _ _ _ _ Heqt) in H.
   destruct H; subst; try (left; assumption).
     right. apply Mem.alloc_result in Heqt. subst.
     exists i. rewrite genv_find_add_globals_fresh; trivial.
     unfold Genv.find_symbol, Genv.genv_symb. simpl.
     rewrite PTree.gss. rewrite N. trivial.
simpl in *.
  remember (Mem.alloc m0 0 (Genv.init_data_list_size (gvar_init v))) as t.
  destruct t; inv Heqd. apply eq_sym in Heqt.
  remember (store_zeros m2 b0 0 (Genv.init_data_list_size (gvar_init v))) as q.
  destruct q; inv H1. apply eq_sym in Heqq.
  remember (Genv.store_init_data_list
         (Genv.add_globals (Genv.add_global g (i, Gvar v)) defs) m3 b0 0
         (gvar_init v)) as w.
  destruct w; inv H4. apply eq_sym in Heqw.
  apply (Mem.drop_perm_valid_block_2 _ _ _ _ _ _ H1) in H. clear H1.
  assert (VB3: Mem.valid_block m3 b). unfold Mem.valid_block.
    rewrite <- (@Genv.store_init_data_list_nextblock _ _ _ _ _ _ _ _ Heqw).
    apply H.
  clear H Heqw.
  assert (VB2: Mem.valid_block m2 b). unfold Mem.valid_block.
    rewrite <- (@Genv.store_zeros_nextblock _ _ _ _ _ Heqq).
    apply VB3.
  clear VB3 Heqq.
  apply (Mem.valid_block_alloc_inv _ _ _ _ _ Heqt) in VB2.
   destruct VB2; subst; try (left; assumption).
     right. apply Mem.alloc_result in Heqt. subst.
     exists i. rewrite genv_find_add_globals_fresh; trivial.
     unfold Genv.find_symbol, Genv.genv_symb. simpl.
     rewrite PTree.gss. rewrite N. trivial.
Qed.

Section TRANSLATION.
Variable prog: Csharpminor.program.
Variable tprog: Cminor.program.
Hypothesis TRANSL: transl_program prog = OK tprog.
Let ge : Csharpminor.genv := Genv.globalenv prog.
(*Let gce : compilenv := build_global_compilenv prog.*)
Let tge: genv := Genv.globalenv tprog.

Let core_data := CSharpMin_core.

(*Lenb -- meminj_preserves_globales is new, and needed since this property is now
    required by the simulation realtions, rather than only at/efterexternal clauses*)
Inductive match_cores: core_data -> meminj -> CSharpMin_core -> mem -> CMin_core -> mem -> Prop :=
  | MC_states:
      forall d fn s k e le m tfn ts tk sp te tm cenv xenv j lo hi cs sz
      (TRF: transl_funbody cenv sz fn = OK tfn)
      (TR: transl_stmt cenv xenv s = OK ts)
      (MINJ: Mem.inject j m tm)
      (MCS: match_callstack prog j m tm
               (Frame cenv tfn e le te sp lo hi :: cs)
               (Mem.nextblock m) (Mem.nextblock tm))
      (MK: match_cont k tk  cenv xenv cs)
      (PG: meminj_preserves_globals ge j),
      match_cores d j (CSharpMin_State fn s k e le) m
                   (CMin_State tfn ts tk (Vptr sp Int.zero) te) tm
  | MC_state_seq:
      forall d fn s1 s2 k e le m tfn ts1 tk sp te tm cenv xenv j lo hi cs sz
      (TRF: transl_funbody cenv sz fn = OK tfn)
      (TR: transl_stmt cenv xenv s1 = OK ts1)
      (MINJ: Mem.inject j m tm)
      (MCS: match_callstack prog j m tm
               (Frame cenv tfn e le te sp lo hi :: cs)
               (Mem.nextblock m) (Mem.nextblock tm))
      (MK: match_cont (Csharpminor.Kseq s2 k) tk cenv xenv cs)
      (PG: meminj_preserves_globals ge j),
      match_cores d j (CSharpMin_State fn (Csharpminor.Sseq s1 s2) k e le) m
                   (CMin_State tfn ts1 tk (Vptr sp Int.zero) te) tm
  | MC_callstate:
      forall d fd args k m tfd targs tk tm j cs cenv
      (TR: transl_fundef fd = OK tfd)
      (MINJ: Mem.inject j m tm)
      (MCS: match_callstack prog j m tm cs (Mem.nextblock m) (Mem.nextblock tm))
      (MK: match_cont k tk cenv nil cs)
      (ISCC: Csharpminor.is_call_cont k)
      (ARGSINJ: val_list_inject j args targs)
      (PG: meminj_preserves_globals ge j),

      match_cores d j (CSharpMin_Callstate fd args k) m
                   (CMin_Callstate tfd targs tk) tm
  | MC_returnstate:
      forall d v k m tv tk tm j cs cenv
      (MINJ: Mem.inject j m tm)
      (MCS: match_callstack prog j m tm cs (Mem.nextblock m) (Mem.nextblock tm))
      (MK: match_cont k tk cenv nil cs)
      (RESINJ: val_inject j v tv)
      (PG: meminj_preserves_globals ge j),
      match_cores d j (CSharpMin_Returnstate v k) m
                   (CMin_Returnstate tv tk) tm.

(*Lenb -- lemma is new, and needed for the proof of
Theorem transl_program_correct at the end of this file*)
Lemma match_cores_valid:
forall d j c1 m1 c2 m2,  match_cores d j c1 m1 c2 m2 ->
          forall b1 b2 ofs, j b1 = Some(b2,ofs) ->
               (Mem.valid_block m1 b1 /\ Mem.valid_block m2 b2).
Proof.
intros.
inv H.
  split. eapply Mem.valid_block_inject_1; eassumption.
         eapply Mem.valid_block_inject_2; eassumption.
  split. eapply Mem.valid_block_inject_1; eassumption.
         eapply Mem.valid_block_inject_2; eassumption.
  split. eapply Mem.valid_block_inject_1; eassumption.
         eapply Mem.valid_block_inject_2; eassumption.
  split. eapply Mem.valid_block_inject_1; eassumption.
         eapply Mem.valid_block_inject_2; eassumption.
Qed.

Lemma match_cores_genvs:
forall d j c1 m1 c2 m2,  match_cores d j c1 m1 c2 m2 ->
          meminj_preserves_globals ge j.
Proof.
intros.
inv H; trivial.
Qed.

(*-----A variant of CminorgenproofRestructured.match_globalenvs_init,
   used for init_cores---*)
Lemma valid_init_is_global :
  forall (R: list_norepet (map fst (prog_defs prog)))
  m (G: Genv.init_mem prog = Some m)
  b (VB: Mem.valid_block m b),
  exists id, Genv.find_symbol (Genv.globalenv prog) id = Some b.
Proof. intros.
  unfold Genv.init_mem, Genv.globalenv in G. simpl in *.
  destruct (add_globals_find_symbol _ R (@Genv.empty_genv _ _ ) _ _ G (eq_refl _) _ VB)
    as [VBEmpty | X]; trivial.
  exfalso. clear - VBEmpty. unfold Mem.valid_block in VBEmpty.
    rewrite Mem.nextblock_empty in VBEmpty. xomega.
Qed.

Lemma match_globalenvs_init':
  forall (R: list_norepet (map fst (prog_defs prog)))
  m j,
  Genv.init_mem prog = Some m ->
  meminj_preserves_globals ge j ->
  match_globalenvs prog j (Mem.nextblock m).
Proof.
  intros.
  destruct H0 as [A [B C]].
  constructor.
  intros b D. intros [[id E]|[[gv E]|[fptr E]]]; eauto.
  cut (exists id, Genv.find_symbol (Genv.globalenv prog) id = Some b).
  intros [id ID].
  solve[eapply A; eauto].
  eapply valid_init_is_global; eauto.
  intros. symmetry. solve[eapply (C _ _ _ _ H0); eauto].
  intros. eapply Genv.find_symbol_not_fresh; eauto.
  intros. eapply Genv.find_funct_ptr_not_fresh ; eauto.
  intros. eapply Genv.find_var_info_not_fresh; eauto.
Qed.
(*--------------------------------------------------------------------*)

Lemma init_cores: forall (v1 v2 : val) (sig : signature) entrypoints
  (EP: In (v1, v2, sig) entrypoints)
  (entry_points_ok :
    forall v1 v2 sig,
      In (v1, v2, sig) entrypoints ->
      exists b f1 f2,
        v1 = Vptr b Int.zero
        /\ v2 = Vptr b Int.zero
        /\ Genv.find_funct_ptr ge b = Some f1
        /\ Genv.find_funct_ptr tge b = Some f2)
  (vals1 : list val) (c1 : core_data) (m1 : mem) (j : meminj)
  (vals2 : list val) (m2 : mem)
  (CSM_Ini : initial_core CSharpMin_core_sem ge v1 vals1 = Some c1)
  (Inj : Mem.inject j m1 m2)
  (VI: Forall2 (val_inject j) vals1 vals2)
  (PG: meminj_preserves_globals ge j)
  (R: list_norepet (map fst (prog_defs prog)))
  (INIT_MEM: exists m0, Genv.init_mem prog = Some m0
    /\ Ple (Mem.nextblock m0) (Mem.nextblock m1)
    /\ Ple (Mem.nextblock m0) (Mem.nextblock m2)),
exists c2 : CMin_core,
  initial_core CMin_core_sem tge v2 vals2 = Some c2 /\
  match_cores c1 j c1 m1 c2 m2.
Proof. intros.
  inversion CSM_Ini. unfold  CSharpMin_initial_core in H0. unfold ge in *. unfold tge in *.
  destruct v1; inv H0.
  remember (Int.eq_dec i Int.zero) as z; destruct z; inv H1. clear Heqz.
  remember (Genv.find_funct_ptr (Genv.globalenv prog) b) as zz; destruct zz; inv H0.
    apply eq_sym in Heqzz.
  exploit function_ptr_translated; eauto. intros [tf [FIND TR]].
  exists (CMin_Callstate tf vals2 Cminor.Kstop).
  split.
  simpl.
  destruct (entry_points_ok _ _ _ EP) as [b0 [f1 [f2 [A [B [C D]]]]]].
  subst. inv A. rewrite C in Heqzz. inv Heqzz. rewrite D in FIND. inv FIND.
  unfold CMin_initial_core.
  case_eq (Int.eq_dec Int.zero Int.zero). intros ? e.
  solve[rewrite D; auto].
  intros CONTRA.
  solve[elimtype False; auto].
  eapply MC_callstate with (cenv:=PTree.empty _)(cs := @nil frame); try eassumption.
  destruct INIT_MEM as [m0 [INIT_MEM [A B]]].
  assert (Genv.init_mem tprog = Some m0).
    unfold transl_program in TRANSL.
    solve[eapply Genv.init_mem_transf_partial in TRANSL; eauto].
  apply mcs_nil with (Mem.nextblock m0).
  apply match_globalenvs_init'; auto.
  apply A. apply B.
  econstructor. simpl. trivial.
  simpl. apply forall_inject_val_list_inject; auto.
Qed.

Lemma MC_safely_halted: forall (cd : core_data) (j : meminj) (c1 : CSharpMin_core) (m1 : mem)
  (c2 : CMin_core) (m2 : mem) (v1 : val),
match_cores cd j c1 m1 c2 m2 ->
halted CSharpMin_core_sem  c1 = Some v1 ->
exists v2,
halted CMin_core_sem c2 = Some v2 /\ Mem.inject j m1 m2 /\
val_inject j v1 v2.
Proof.
  intros.
  inv H; simpl in *; inv H0.
  destruct k; inv H1. exists tv.
  split.
         inv MK. trivial.
  split; trivial.
Qed.

Lemma MC_at_external: forall (cd : core_data) (j : meminj) (st1 : CSharpMin_core) (m1 : mem)
  (st2 : CMin_core) (m2 : mem) (e : external_function) (vals1 : list val) sig,
(cd = st1 /\ match_cores cd j st1 m1 st2 m2) ->
at_external CSharpMin_core_sem st1 = Some (e, sig, vals1) ->
Mem.inject j m1 m2 /\
Events.meminj_preserves_globals ge j /\
(exists vals2 : list val,
   Forall2 (val_inject j) vals1 vals2 /\
   at_external CMin_core_sem st2 = Some (e, sig, vals2)).
Proof.
  intros. destruct H; subst.
  inv H1; simpl in *; inv H0.
  split; trivial.
  split. destruct (match_callstack_match_globalenvs _ _ _ _ _ _ _ MCS) as [hi Hhi].
              eapply inj_preserves_globals; eassumption.
  destruct fd; inv H1.
  exists targs.
  split. eapply val_list_inject_forall_inject; eassumption.
  inv TR.
  split; trivial.
Qed.

Lemma MC_after_external:forall (d : core_data) (j j' : meminj) (st1 : core_data) (st2 : CMin_core)
  (m1 : mem) (e : external_function) (vals1 : list val) (ret1 : val)
  (m1' m2 m2' : mem) (ret2 : val) (sig : signature),
d = st1 /\ match_cores d j st1 m1 st2 m2 ->
at_external CSharpMin_core_sem st1 = Some (e, sig, vals1) ->
Events.meminj_preserves_globals ge j ->
inject_incr j j' ->
Events.inject_separated j j' m1 m2 ->
Mem.inject j' m1' m2' ->
val_inject j' ret1 ret2 ->
mem_forward m1 m1' ->
Mem.unchanged_on (Events.loc_unmapped j) m1 m1' ->
mem_forward m2 m2' ->
Mem.unchanged_on (Events.loc_out_of_reach j m1) m2 m2' ->
exists st1' : core_data,
  exists st2' : CMin_core,
    exists d' : core_data,
      after_external CSharpMin_core_sem (Some ret1) st1 = Some st1' /\
      after_external CMin_core_sem (Some ret2) st2 = Some st2' /\
      d' = st1' /\ match_cores d' j' st1' m1' st2' m2'.
Proof. intros.
  destruct (MC_at_external _ _ _ _ _ _ _ _ _ H H0)
    as [_ [_ [vals2 [ValsInj AtExt2]]]].
  destruct H as [X MC]; subst.
  inv MC; simpl in *; inv H0.
  destruct fd; inv H10.
  destruct tfd; inv AtExt2.
  exists (CSharpMin_Returnstate ret1 k). eexists. eexists.
    split. reflexivity.
    split. reflexivity.
    split. reflexivity.
  simpl in *.
  econstructor; try eassumption.
  clear TR H10.
  destruct k; simpl in *; try contradiction. (*cases k = Kseq and k=Kblock eliminated*)
  (*k=Kstop*)
      inv MK; simpl in *.
      apply match_callstack_incr_bound with (Mem.nextblock m1) (Mem.nextblock m2).
      eapply match_callstack_external_call; eauto.
          intros. eapply H6; eauto.
          xomega.
          xomega.
         eapply forward_nextblock; assumption.
         eapply forward_nextblock; assumption.
  (*k=Kcall*)
      inv MK; simpl in *.
      apply match_callstack_incr_bound with (Mem.nextblock m1) (Mem.nextblock m2).
      eapply match_callstack_external_call; eauto.
          intros. eapply H6; eauto.
          xomega.
          xomega.
         eapply forward_nextblock; assumption.
         eapply forward_nextblock; assumption.
  solve [eapply meminj_preserves_incr_sep; eassumption].
Qed.

Lemma MC_MSI: forall d j
       q m q' m',
      match_cores d j q m q' m' ->
      match_statesInj prog j  (ToState q m) (Cminor_coop.ToState q' m').
  Proof. intros.
    inv H; simpl in *.
     eapply matchInj_state; try eassumption.
     eapply matchInj_state_seq; try eassumption.
     eapply matchInj_callstate; try eassumption.
     eapply matchInj_returnstate; try eassumption.
Qed.

Lemma MSI_MC: forall j q m q' m' d
      (*NEW:*) (PG: meminj_preserves_globals ge j),
      match_statesInj prog j (ToState q m) (Cminor_coop.ToState q' m') ->
      match_cores d j q m q' m'.
  Proof. intros.
    inv H; simpl in *.
     destruct q; simpl in *; inv H2.
        destruct q'; simpl in *; inv H3.
        eapply MC_states; try eassumption.
     destruct q; simpl in *; inv H2.
        destruct q'; simpl in *; inv H3.
        eapply MC_state_seq; try eassumption.
     destruct q; simpl in *; inv H2.
        destruct q'; simpl in *; inv H3.
        eapply MC_callstate; try eassumption.
     destruct q; simpl in *; inv H2.
        destruct q'; simpl in *; inv H3.
        eapply MC_returnstate; try eassumption.
Qed.

Lemma MSI_atExt: forall j c1 m1 c2 m2
(H: match_statesInj prog j (ToState c1 m1) (Cminor_coop.ToState c2 m2) ),
(CSharpMin_at_external c1 = None) = (CMin_at_external c2 = None).
Proof.
  intros.
  destruct c1; destruct c2; inv H; simpl in *; trivial.
  destruct f; destruct f0; simpl in *; trivial.
   apply bind_inversion in TR. destruct TR as [z [ZZ1 ZZ2]]; subst.
  inv ZZ2.
  inv TR.
  inv TR.
  apply prop_ext. split; intros; inv H.
Qed.

Parameter MC_order :  core_data -> core_data -> Prop.
Parameter MC_wellfounded: well_founded MC_order.
Definition MC_measure (q:CSharpMin_core): nat :=
  match q with
  | CSharpMin_State fn s k e lenv => seq_left_depth s
  | _ => O
  end.
(*Parameter MC_measure: CSharpMin_core-> nat.*)

Lemma MS_step_case_SkipSeq:
forall cenv sz f tfn j m tm  e lenv te sp lo hi cs s k tk xenv
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MK : match_cont (Csharpminor.Kseq s k) tk cenv xenv cs)
(MCS : match_callstack prog j m tm (Frame cenv tfn e lenv te sp lo hi :: cs)
        (Mem.nextblock m) (Mem.nextblock tm))
(*NEW:*) (PG: meminj_preserves_globals ge j),
exists c2' : CMin_core,
  exists m2' : mem,
        corestep_plus CMin_core_sem tge (CMin_State tfn Sskip tk (Vptr sp Int.zero) te) tm c2' m2' /\
        match_cores (CSharpMin_State f s k e lenv) j (CSharpMin_State f s k e lenv) m c2' m2'.
(*   exists c' : CSharpMin_core,
        inj_match_states_star unit match_cores MC_measure (tt,c') j (CSharpMin_State f s k e lenv) m c2' m2'.*)
Proof. intros.
  dependent induction MK.

  eexists. eexists.
  split.
    apply corestep_plus_one.
        eapply CompCertStep_CMin_corestep'.  simpl.  econstructor. reflexivity.
  simpl. (* exists (CSharpMin_State f s k e le).
     left. *) eapply MC_states; eauto.

  eexists. eexists.
  split.
    apply corestep_plus_one.
        eapply CompCertStep_CMin_corestep'.  simpl.  econstructor. reflexivity.
   simpl. (*exists (CSharpMin_State f (Csharpminor.Sseq s1 s2) k e le).
      left.  *) eapply MC_state_seq; eauto.

  exploit IHMK; eauto. clear IHMK.  intros [T2 [m2 [A C]]].
  exists T2; exists m2.
  split.
     eapply corestep_star_plus_trans.
        apply corestep_star_one.  eapply CompCertStep_CMin_corestep'.  simpl.  constructor. reflexivity.
        simpl. apply A.
  apply C.
Qed.

Lemma MS_step_case_SkipBlock:
forall cenv sz f tfn j m tm e lenv te sp lo hi cs k tk xenv
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MK : match_cont (Csharpminor.Kblock k) tk cenv xenv cs)
(MCS : match_callstack prog j m tm (Frame cenv tfn e lenv te sp lo hi :: cs)
        (Mem.nextblock m) (Mem.nextblock tm))
(*NEW:*) (PG: meminj_preserves_globals ge j),
exists c2' : CMin_core,
  exists m2' : mem,
        corestep_plus CMin_core_sem tge (CMin_State tfn Sskip tk (Vptr sp Int.zero) te) tm c2' m2' /\
         match_cores  (CSharpMin_State f Csharpminor.Sskip k e lenv)   j (CSharpMin_State f Csharpminor.Sskip k e lenv) m c2' m2'
(*exists c' : CSharpMin_core,
        inj_match_states_star unit match_cores MC_measure (tt,c') j (CSharpMin_State f Csharpminor.Sskip k e le) m c2' m2'*).
Proof. intros.
  dependent induction MK.

  eexists. eexists.
  split.
    apply corestep_plus_one.
        eapply CompCertStep_CMin_corestep'.  simpl. constructor. reflexivity.
   simpl. (*exists (CSharpMin_State f Csharpminor.Sskip k e le).
      left.  *) eapply MC_states; eauto.

  exploit IHMK; eauto. clear IHMK.  intros [T2 [m2 [A C]]].
  exists T2; exists m2.
  split.
     eapply corestep_star_plus_trans.
        apply corestep_star_one.  eapply CompCertStep_CMin_corestep'.  simpl.  constructor. reflexivity.
        simpl. apply A.
  (* simpl in *. exists c'.*) apply C.
Qed.

Lemma MS_match_is_call_cont:
  forall tfn te sp tm k tk cenv xenv cs,
  match_cont k tk cenv xenv cs ->
  Csharpminor.is_call_cont k ->
  exists tk',
    corestep_star CMin_core_sem tge (CMin_State tfn Sskip tk sp te) tm
                (CMin_State tfn Sskip tk' sp te) tm
    /\ is_call_cont tk'
    /\ match_cont k tk' cenv nil cs.
Proof.
  induction 1; simpl; intros; try contradiction.
  econstructor; split.
     apply corestep_star_zero. split. exact I. econstructor; eauto.
  exploit IHmatch_cont; eauto.
  intros [tk' [A B]]. exists tk'; split.
  eapply corestep_star_trans; eauto. apply corestep_star_one. simpl. eexists. constructor. auto.

  econstructor; split. apply corestep_star_zero. split. exact I. econstructor; eauto.
Qed.

Lemma MS_step_case_SkipCall:
 forall cenv sz f tfn j m tm e lenv te sp lo hi cs k tk xenv m'
(CC: Csharpminor.is_call_cont k)
(FL: Mem.free_list m (blocks_of_env e) = Some m')
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MK : match_cont k tk cenv xenv cs)
(MCS : match_callstack prog j m tm (Frame cenv tfn e lenv te sp lo hi :: cs)
        (Mem.nextblock m) (Mem.nextblock tm))
(*NEW:*) (PG: meminj_preserves_globals ge j),
exists c2' : CMin_core,
  exists m2' : mem,
        corestep_plus CMin_core_sem tge (CMin_State  tfn Sskip tk (Vptr sp Int.zero) te) tm c2' m2' /\
         match_cores  (CSharpMin_Returnstate Vundef k)  j (CSharpMin_Returnstate Vundef k) m' c2' m2'.
(*exists c' : CSharpMin_core,
       inj_match_states_star unit match_cores MC_measure (tt,c') j
       (CSharpMin_Returnstate Vundef k) m' c2' m2'.*)
Proof. intros.
  exploit MS_match_is_call_cont; eauto. intros [tk' [A [B C]]].
  exploit match_callstack_freelist; eauto. intros [tm' [P [Q R]]].

  eexists. eexists.
  split.
    eapply corestep_star_plus_trans. eexact A. apply corestep_plus_one.
      eapply CompCertStep_CMin_corestep'. apply step_skip_call. assumption.
      eauto.
    eauto.
    econstructor; eauto.
Qed.

Lemma MS_step_case_Assign:
forall cenv sz f tfn j m tm e lenv te sp lo hi cs k tk xenv  x a x0 v id
(EE:Csharpminor.eval_expr ge e lenv m a v)
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MK : match_cont k tk cenv xenv cs)
(MCS : match_callstack prog j m tm (Frame cenv tfn e lenv te sp lo hi :: cs)
        (Mem.nextblock m) (Mem.nextblock tm))
(EQ : transl_expr cenv a = OK (x, x0))
(*NEW:*) (PG: meminj_preserves_globals ge j),
exists c2' : CMin_core,
  exists m2' : mem,
    corestep_plus CMin_core_sem tge
     (CMin_State tfn (Sassign id x) tk (Vptr sp Int.zero) te) tm c2' m2' /\
   match_cores
     (CSharpMin_State f Csharpminor.Sskip k e (PTree.set id v lenv)) j
     (CSharpMin_State f Csharpminor.Sskip k e (PTree.set id v lenv)) m c2'
     m2'.
(*  exists c' : CSharpMin_core,
       inj_match_states_star unit match_cores MC_measure (tt,c') j
       (CSharpMin_State f Csharpminor.Sskip k e lenv) m' c2' m2'.*)
Proof. intros.
 intros.
  exploit transl_expr_correct; eauto. intros [tv [EVAL [VINJ APP]]].
(*
  exploit var_set_correct; eauto.
  intros [te' [tm' [EXEC [MINJ' [MCS' OTHER]]]]].
*)
  eexists; eexists; split.
     apply corestep_plus_one. eapply CompCertStep_CMin_corestep'.
         econstructor. eassumption. reflexivity.
inv MCS.
  econstructor; eauto.
econstructor; eauto.
eapply match_temps_assign; assumption.
Qed.

(*no case Set in CompCert 2.0
Lemma MS_step_case_Set:
forall cenv sz f tfn j m tm e lenv te sp lo hi cs k tk xenv x x0 v a id
(H: Csharpminor.eval_expr ge e lenv m a v)
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MCS : match_callstack prog j m tm (Frame cenv tfn e lenv te sp lo hi :: cs)
        (Mem.nextblock m) (Mem.nextblock tm))
(MK : match_cont k tk (fn_return f) cenv xenv cs)
(EQ : transl_expr cenv a = OK (x, x0)),
exists c2' : CMin_core,
  exists m2' : mem,
        corestep_plus CMin_core_sem tge (CMin_State  tfn (Sassign (for_temp id) x) tk (Vptr sp Int.zero) te) tm c2' m2' /\
       match_cores (CSharpMin_State f Csharpminor.Sskip k e (PTree.set id v lenv)) j
          (CSharpMin_State f Csharpminor.Sskip k e (PTree.set id v lenv)) m c2' m2' .
(*  exists c' : CSharpMin_core,
        inj_match_states_star unit match_cores MC_measure (tt,c') j
          (CSharpMin_State f Csharpminor.Sskip k e (PTree.set id v lenv)) m c2' m2' .*)
Proof. intros.
  exploit transl_expr_correct; eauto. intros [tv [EVAL [VINJ APP]]].
  eexists; eexists; split.
     apply corestep_plus_one. eapply CompCertStep_CMin_corestep'. econstructor; eauto.  reflexivity.
  simpl in *.
  econstructor; eauto.
  apply (match_callstack_set_temp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ id _ _ VINJ MCS).
(*  exists (CSharpMin_State f Csharpminor.Sskip k e (PTree.set id v lenv)).
    left. econstructor; eauto.*)
Qed.
*)

Lemma MS_step_case_Store:
forall cenv sz f tfn j m tm e lenv te sp lo hi cs k tk xenv x x0 x1 x2
      chunk m' a addr vaddr v
(CH: Mem.storev chunk m vaddr v = Some m')
(EvAddr : Csharpminor.eval_expr ge e lenv m addr vaddr)
(EvA : Csharpminor.eval_expr ge e lenv m a v)
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MCS : match_callstack prog j m tm (Frame cenv tfn e lenv te sp lo hi :: cs)
                (Mem.nextblock m) (Mem.nextblock tm))
(MK : match_cont k tk cenv xenv cs)
(EQ : transl_expr cenv addr = OK (x, x0))
(EQ1 : transl_expr cenv a = OK (x1, x2))
(*NEW:*) (PG: meminj_preserves_globals ge j),
exists c2' : CMin_core,
  exists m2' : mem,
        corestep_plus CMin_core_sem tge (CMin_State  tfn (make_store chunk x x1) tk (Vptr sp Int.zero) te) tm c2' m2' /\
        match_cores (CSharpMin_State f Csharpminor.Sskip k e lenv) j
                      (CSharpMin_State f Csharpminor.Sskip k e lenv) m' c2' m2' .
(* exists c' : CSharpMin_core,
        inj_match_states_star unit match_cores MC_measure (tt,c') j
                      (CSharpMin_State f Csharpminor.Sskip k e lenv) m' c2' m2' .*)
Proof. intros.
  exploit transl_expr_correct. eauto. eauto. eauto. eexact EvAddr. eauto.
  intros [tv1 [EVAL1 [VINJ1 APP1]]].
  exploit transl_expr_correct. eauto. eauto. eauto. eexact EvA. eauto.
  intros [tv2 [EVAL2 [VINJ2 APP2]]].
  exploit make_store_correct. eexact EVAL1. eexact EVAL2. eauto. eauto. auto. auto.
  intros [tm' [tv' [EXEC [STORE' MINJ']]]].
  eexists; eexists; split.
      apply corestep_plus_one. eapply CompCertStep_CMin_corestep'. eexact EXEC. reflexivity.
  simpl in *.
  inv VINJ1; simpl in CH; try discriminate.
  econstructor; eauto.
  rewrite (Mem.nextblock_store _ _ _ _ _ _ CH).
  rewrite (Mem.nextblock_store _ _ _ _ _ _ STORE').
  eapply match_callstack_invariant (*with f0 m tm*); eauto.
  intros. eapply Mem.perm_store_2; eauto.
  intros. eapply Mem.perm_store_1; eauto.
Qed.

Lemma MS_step_case_Call:
forall cenv sz f tfn j m tm e lenv te sp lo hi cs k tk xenv  x x0 x1 a vf fd optid vargs bl
(EvalA: Csharpminor.eval_expr ge e lenv m a vf)
(EvalBL: Csharpminor.eval_exprlist ge e lenv m bl vargs)
(FF: Genv.find_funct ge vf = Some fd)
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MCS : match_callstack prog j m tm (Frame cenv tfn e lenv te sp lo hi :: cs)
        (Mem.nextblock m) (Mem.nextblock tm))
(MK : match_cont tk k cenv xenv cs)
(EQ : transl_expr cenv a = OK (x, x0))
(EQ1 : transl_exprlist cenv bl = OK x1)
(*NEW:*) (PG: meminj_preserves_globals ge j),
exists c2' : CMin_core,
  exists m2' : mem,
        corestep_plus CMin_core_sem tge
             (CMin_State  tfn (Scall optid (Csharpminor.funsig fd) x x1)  k (Vptr sp Int.zero) te) tm c2' m2' /\
       match_cores (CSharpMin_Callstate fd vargs (Csharpminor.Kcall optid f e lenv tk))  j
              (CSharpMin_Callstate fd vargs (Csharpminor.Kcall optid f e lenv tk)) m c2' m2'.
(* exists c' : CSharpMin_core,
        inj_match_states_star unit match_cores MC_measure (tt,c') j
              (CSharpMin_Callstate fd vargs (Csharpminor.Kcall optid f e lenv tk)) m c2' m2'.*)
Proof. intros.
  simpl in FF. exploit functions_translated; eauto. intros [tfd [FIND TRANS]].
  exploit transl_expr_correct; eauto. intros [tvf [EVAL1 [VINJ1 APP1]]].
  assert (tvf = vf).
    exploit match_callstack_match_globalenvs; eauto. intros [bnd MG].
    eapply val_inject_function_pointer; eauto.
  subst tvf.
  exploit transl_exprlist_correct; eauto.
  intros [tvargs [EVAL2 VINJ2]].
  eexists; eexists; split.
      apply corestep_plus_one. eapply CompCertStep_CMin_corestep'.
          eapply step_call. eassumption. eassumption. apply FIND.
                      eapply sig_preserved; eauto.
          econstructor; eauto.
  simpl in *.
     (*exists  (CSharpMin_Callstate fd vargs (Csharpminor.Kcall optid f e lenv tk)).
     left.*) econstructor; eauto. eapply match_Kcall with (cenv' := cenv); eauto.
            simpl; trivial.
Qed.

Lemma MS_step_case_Builtin:
forall cenv sz f tfn j m tm e lenv te sp lo hi cs k tk xenv x t ef optid vres m' bl vargs
(EvalArgs: Csharpminor.eval_exprlist ge e lenv m bl vargs)
(ExtCall: Events.external_call ef ge vargs m t vres m')
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MCS : match_callstack prog j m tm (Frame cenv tfn e lenv te sp lo hi :: cs)
        (Mem.nextblock m) (Mem.nextblock tm))
(MK : match_cont k tk cenv xenv cs)
(EQ : transl_exprlist cenv bl = OK x)
(*NEW:*) (PG: meminj_preserves_globals ge j),
exists c2' : CMin_core,
  exists m2' : mem,
      corestep_plus CMin_core_sem tge
           (CMin_State tfn (Sbuiltin optid ef x) tk (Vptr sp Int.zero) te) tm c2' m2' /\
  exists j' : meminj,
        inject_incr j j' /\
        Events.inject_separated j j' m tm /\
       match_cores (CSharpMin_State f Csharpminor.Sskip k e (set_optvar optid vres lenv))  j'
              (CSharpMin_State f Csharpminor.Sskip k e (set_optvar optid vres lenv)) m' c2' m2'.
(*  exists c',
        inj_match_states_star unit match_cores MC_measure (tt,c') j'
          (CSharpMin_State f Csharpminor.Sskip k e (set_optvar optid vres lenv)) m' c2' m2'.*)
Proof. intros.
  exploit transl_exprlist_correct; eauto.
  intros [tvargs [EVAL2 VINJ2]].
  exploit match_callstack_match_globalenvs; eauto. intros [hi' MG].
  exploit Events.external_call_mem_inject; eauto.
  intros [j' [vres' [tm' [EC [VINJ [MINJ' [UNMAPPED [OUTOFREACH [INCR SEPARATED]]]]]]]]].
  eexists; eexists; split.
      apply corestep_plus_one. eapply CompCertStep_CMin_corestep'.
           econstructor; try eassumption.
             eapply Events.external_call_symbols_preserved; eauto.
                 eapply symbols_preserved; assumption.
                 eapply varinfo_preserved; assumption.
           reflexivity.
  assert (MCS': match_callstack prog j' m' tm'
                 (Frame cenv tfn e lenv te sp lo hi :: cs)
                 (Mem.nextblock m') (Mem.nextblock tm')).
    apply match_callstack_incr_bound with (Mem.nextblock m) (Mem.nextblock tm).
    eapply match_callstack_external_call; eauto.
    intros. eapply Events.external_call_max_perm; eauto.
    xomega. xomega.
    eapply external_call_nextblock; eauto.
    eapply external_call_nextblock; eauto.
exists j'. split. assumption.  split. assumption.
  simpl in *. (* exists  (CSharpMin_State f Csharpminor.Sskip k e (set_optvar optid vres lenv)).
  left. *) econstructor; eauto.
Opaque PTree.set.
  unfold set_optvar. destruct optid; simpl.
  eapply match_callstack_set_temp; eauto.
  auto.
solve [eapply meminj_preserves_incr_sep; eassumption].
Qed.

Lemma MS_step_case_Ite:
forall cenv sz f tfn j m tm e lenv te sp lo hi cs k tk xenv x x0 x1 x2 b v a s1 s2
(H : Csharpminor.eval_expr ge e lenv m a v)
(BoolOfVal : Val.bool_of_val v b)
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MCS : match_callstack prog j m tm (Frame cenv tfn e lenv te sp lo hi :: cs)
        (Mem.nextblock m) (Mem.nextblock tm))
(MK : match_cont k tk cenv xenv cs)
(EQ : transl_expr cenv a = OK (x, x0))
(EQ1 : transl_stmt cenv xenv s1 = OK x1)
(EQ0 : transl_stmt cenv xenv s2 = OK x2)
(*NEW:*) (PG: meminj_preserves_globals ge j),
exists c2' : CMin_core,
  exists m2' : mem,
        corestep_plus CMin_core_sem tge
             (CMin_State tfn (Sifthenelse x x1 x2) tk (Vptr sp Int.zero) te) tm c2' m2' /\
        match_cores  (CSharpMin_State f (if b then s1 else s2) k e lenv)  j
             (CSharpMin_State f (if b then s1 else s2) k e lenv) m c2' m2'.
(*  exists c',
        inj_match_states_star unit match_cores MC_measure (tt,c') j
             (CSharpMin_State f (if b then s1 else s2) k e lenv) m c2' m2'.*)
Proof. intros.
  exploit transl_expr_correct; eauto. intros [tv [EVAL [VINJ APP]]].
  exists (CMin_State tfn (if b then x1 else x2) tk (Vptr sp Int.zero) te). exists tm.
  split.
     apply corestep_plus_one. eapply CompCertStep_CMin_corestep.
              eapply step_ifthenelse; eauto. eapply bool_of_val_inject; eauto.
        econstructor; eauto.
  simpl in *.
 (*   exists (CSharpMin_State f (if b then s1 else s2) k e lenv).
    left. *) econstructor; eauto.
       destruct b; auto.
Qed.

Lemma MS_step_case_Loop:
forall cenv sz f tfn j m tm e lenv te sp lo hi cs k tk xenv x s
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MCS : match_callstack prog j m tm (Frame cenv tfn e lenv te sp lo hi :: cs)
        (Mem.nextblock m) (Mem.nextblock tm))
(MK : match_cont tk k cenv xenv cs)
(EQ : transl_stmt cenv xenv s = OK x)
(*NEW:*) (PG: meminj_preserves_globals ge j),
exists c2' : CMin_core,
  exists m2' : mem,
      corestep_plus CMin_core_sem tge (CMin_State tfn (Sloop x) k (Vptr sp Int.zero) te) tm c2' m2' /\
      match_cores  (CSharpMin_State f s (Csharpminor.Kseq (Csharpminor.Sloop s) tk) e lenv)  j
          (CSharpMin_State f s (Csharpminor.Kseq (Csharpminor.Sloop s) tk) e lenv) m c2' m2'.
(*    exists c',   inj_match_states_star unit match_cores MC_measure (tt,c') j
          (CSharpMin_State f s (Csharpminor.Kseq (Csharpminor.Sloop s) tk) e lenv) m c2' m2'. *)
Proof. intros.
  eexists; eexists.
  split.
     apply corestep_plus_one. eapply CompCertStep_CMin_corestep'.
        econstructor; eauto.
        reflexivity.
  simpl in *.
(*      exists  (CSharpMin_State f s (Csharpminor.Kseq (Csharpminor.Sloop s) tk) e lenv).
      left.*)
      econstructor; eauto. econstructor; eauto. simpl. rewrite EQ; auto.
Qed.

Lemma MS_step_case_Block:
forall cenv sz f tfn j m tm e lenv te sp lo hi cs k tk xenv x s
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MCS : match_callstack prog j m tm (Frame cenv tfn e lenv te sp lo hi :: cs)
        (Mem.nextblock m) (Mem.nextblock tm))
(MK : match_cont tk k cenv xenv cs)
(EQ : transl_stmt cenv (true :: xenv) s = OK x)
(*NEW:*) (PG: meminj_preserves_globals ge j),
exists c2' : CMin_core,
  exists m2' : mem,
        corestep_plus CMin_core_sem tge (CMin_State tfn (Sblock x) k (Vptr sp Int.zero) te) tm c2' m2' /\
        match_cores (CSharpMin_State f s (Csharpminor.Kblock tk) e lenv) j
                    (CSharpMin_State f s (Csharpminor.Kblock tk) e lenv) m c2' m2'.
(*    exists c' ,
       inj_match_states_star unit match_cores MC_measure (tt,c') j
         (CSharpMin_State f s (Csharpminor.Kblock tk) e lenv) m c2' m2'.*)
Proof. intros.
  eexists; eexists; split.
     apply corestep_plus_one. eapply CompCertStep_CMin_corestep'.
        econstructor; eauto.
        reflexivity.
  simpl in *.
(*      exists  (CSharpMin_State f s (Csharpminor.Kblock tk) e lenv).
      left.*)
      econstructor; eauto. econstructor; eauto.
Qed.

Lemma MS_step_case_ExitSeq:
forall  cenv sz f tfn j m tm e lenv te sp lo hi cs k tk xenv n s
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MCS : match_callstack prog j m tm (Frame cenv tfn e lenv te sp lo hi :: cs)
        (Mem.nextblock m) (Mem.nextblock tm))
(MK : match_cont (Csharpminor.Kseq s tk) k cenv xenv cs)
(*NEW:*) (PG: meminj_preserves_globals ge j),
exists c2' : CMin_core,
  exists m2' : mem,
        corestep_plus CMin_core_sem tge
               (CMin_State tfn (Sexit (shift_exit xenv n)) k (Vptr sp Int.zero) te) tm c2' m2'  /\
        match_cores (CSharpMin_State f (Csharpminor.Sexit n) tk e lenv) j
                               (CSharpMin_State f (Csharpminor.Sexit n) tk e lenv) m c2' m2'.
(*    exists c',  inj_match_states_star unit match_cores MC_measure (tt,c') j
                                   (CSharpMin_State f (Csharpminor.Sexit n) tk e lenv) m c2' m2'.*)
Proof. intros.
  dependent induction MK.

  eexists; eexists; split.
     apply corestep_plus_one. eapply CompCertStep_CMin_corestep'.
        econstructor; eauto.
        reflexivity.
  simpl in *.
      (*exists   (CSharpMin_State f (Csharpminor.Sexit n) tk e lenv).
      left.*) econstructor; eauto. reflexivity.

  exploit IHMK; eauto. intros [c2' [m2' [A B]]].
  exists c2'. exists m2'.
  split; auto.
     eapply corestep_plus_trans.
         apply corestep_plus_one. eapply CompCertStep_CMin_corestep'. constructor. reflexivity.
         simpl. apply A.

  exploit IHMK; eauto.  intros [c2' [m2' [A B]]].
  exists c2'. exists m2'.
  split; auto.
     eapply corestep_plus_trans.
         apply corestep_plus_one. eapply CompCertStep_CMin_corestep'. constructor. reflexivity.
         simpl. apply A.
Qed.

Lemma MS_step_case_ExitBlockZero:
forall  cenv sz f tfn j m tm e lenv te sp lo hi cs k tk xenv
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MCS : match_callstack prog j m tm (Frame cenv tfn e lenv te sp lo hi :: cs)
        (Mem.nextblock m) (Mem.nextblock tm))
(MK : match_cont (Csharpminor.Kblock tk) k cenv xenv cs)
(*NEW:*) (PG: meminj_preserves_globals ge j),
exists c2' : CMin_core,
  exists m2' : mem,
   corestep_plus CMin_core_sem tge
     (CMin_State tfn (Sexit (shift_exit xenv 0)) k (Vptr sp Int.zero) te) tm c2' m2' /\
   match_cores  (CSharpMin_State f Csharpminor.Sskip tk e lenv) j
                              (CSharpMin_State f Csharpminor.Sskip tk e lenv) m c2' m2'.
(*    exists c', inj_match_states_star unit match_cores MC_measure (tt,c') j
                                    (CSharpMin_State f Csharpminor.Sskip tk e lenv) m c2' m2'.*)
Proof. intros.
  dependent induction MK.

  eexists; eexists; split.
     apply corestep_plus_one. eapply CompCertStep_CMin_corestep'. constructor. reflexivity.
  simpl in *.
    (*exists  (CSharpMin_State f Csharpminor.Sskip tk e lenv).
    left.*) econstructor; eauto.

  exploit IHMK; eauto. intros [c2' [m2' [A B]]].
  exists c2'. exists m2'.
  split; auto.
     eapply corestep_plus_trans.
         apply corestep_plus_one. eapply CompCertStep_CMin_corestep'. constructor. reflexivity.
         simpl. apply A.
Qed.

Lemma MS_step_case_ExitBlockNonzero:
forall  cenv sz f tfn j m tm e lenv te sp lo hi cs k tk xenv n
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MCS : match_callstack prog j m tm (Frame cenv tfn e lenv te sp lo hi :: cs)
                     (Mem.nextblock m) (Mem.nextblock tm))
(MK : match_cont (Csharpminor.Kblock tk) k cenv xenv cs)
(*NEW:*) (PG: meminj_preserves_globals ge j),
exists c2' : CMin_core,
  exists m2' : mem,
        corestep_plus CMin_core_sem tge
          (CMin_State tfn (Sexit (shift_exit xenv (S n))) k (Vptr sp Int.zero) te) tm c2' m2' /\
       match_cores (CSharpMin_State f (Csharpminor.Sexit n) tk e lenv)  j
          (CSharpMin_State f (Csharpminor.Sexit n) tk e lenv) m c2' m2'.
Proof. intros.
  dependent induction MK.

  eexists; eexists; split.
     apply corestep_plus_one. eapply CompCertStep_CMin_corestep'. constructor. reflexivity.
  simpl in *.
    econstructor; eauto. auto.

  exploit IHMK; eauto. intros [c2' [m2' [A B]]].
  exists c2'. exists m2'.
  split; auto.
     eapply corestep_plus_trans.
         apply corestep_plus_one. eapply CompCertStep_CMin_corestep'. constructor. reflexivity.
         simpl. apply A.
Qed.

Lemma MS_switch_descent:
  forall cenv xenv k ls body s,
  transl_lblstmt cenv (switch_env ls xenv) ls body = OK s ->
  exists k',
  transl_lblstmt_cont cenv xenv ls k k'
  /\ (forall f sp e m,
      corestep_plus CMin_core_sem tge (CMin_State f s k sp e) m (CMin_State f body k' sp e) m).
Proof.
  induction ls; intros.
(*1*)
  monadInv H.
  eexists; split.
      econstructor; eauto.
  intros. eapply corestep_plus_trans.
                   apply corestep_plus_one. eapply CompCertStep_CMin_corestep'. constructor. reflexivity.
                   simpl.  apply corestep_plus_one. eapply CompCertStep_CMin_corestep.  constructor. reflexivity.
(*2*)
  monadInv H. exploit IHls; eauto. intros [k' [A B]].
  eexists; split.
      econstructor; eauto.
  intros. eapply corestep_plus_star_trans. eauto.
  eapply corestep_star_trans.
      apply corestep_star_one. eapply CompCertStep_CMin_corestep'. constructor. reflexivity.
      simpl. apply corestep_star_one. eapply CompCertStep_CMin_corestep.  constructor. reflexivity.
Qed.

Lemma MS_switch_ascent:
  forall f n sp e m cenv xenv k ls k1,
  let tbl := switch_table ls O in
  let ls' := select_switch n ls in
  transl_lblstmt_cont cenv xenv ls k k1 ->
  exists k2,
  corestep_star CMin_core_sem tge
    (CMin_State f (Sexit (Switch.switch_target n (length tbl) tbl)) k1 sp e) m
    (CMin_State f (Sexit O) k2 sp e) m
  /\ transl_lblstmt_cont cenv xenv ls' k k2.
Proof.
  induction ls; intros; unfold tbl, ls'; simpl.
(*1*)
  inv H.
  eexists; split.
     apply corestep_star_zero.
     econstructor; eauto.
(*2*)
  simpl in H. inv H.
  rewrite Int.eq_sym. destruct (Int.eq i n).
  econstructor; split.  apply corestep_star_zero. econstructor; eauto.
  exploit IHls; eauto. intros [k2 [A B]].
  rewrite (length_switch_table ls 1%nat 0%nat).
  rewrite switch_table_shift.
  exists k2; split; try exact B.
  eapply corestep_star_trans.
        eapply corestep_star_one.  eapply CompCertStep_CMin_corestep'. constructor. reflexivity.
        simpl. eapply corestep_star_trans.
          eapply corestep_star_one.  eapply CompCertStep_CMin_corestep'. econstructor. reflexivity.
          apply A.
Qed.

Lemma MS_switch_MSI:
  forall fn k e lenv m tfn ts tk sp te tm cenv xenv j lo hi cs sz ls body tk'
    (TRF: transl_funbody cenv sz fn = OK tfn)
    (TR: transl_lblstmt cenv (switch_env ls xenv) ls body = OK ts)
    (MINJ: Mem.inject j m tm)
    (MCS: match_callstack prog j m tm
               (Frame cenv tfn e lenv te sp lo hi :: cs)
               (Mem.nextblock m) (Mem.nextblock tm))
    (MK: match_cont k tk cenv xenv cs)
    (TK: transl_lblstmt_cont cenv xenv ls tk tk'),
  exists S, exists mm,
  corestep_plus CMin_core_sem tge (CMin_State tfn (Sexit O) tk' (Vptr sp Int.zero) te) tm S mm
  /\ match_statesInj prog j (Csharpminor.State fn (seq_of_lbl_stmt ls) k e lenv m) (Cminor_coop.ToState S mm).
Proof.
  intros. destruct ls; simpl.
(*1*)
  inv TK. econstructor; eexists; split.
     eapply corestep_plus_trans.
         eapply corestep_plus_one. eapply CompCertStep_CMin_corestep'. constructor. reflexivity.
         simpl. eapply corestep_plus_one. eapply CompCertStep_CMin_corestep'. constructor. reflexivity.
    simpl. eapply matchInj_state; eauto.
(*2*)
  inv TK. econstructor; eexists; split.
     eapply corestep_plus_trans.
         eapply corestep_plus_one. eapply CompCertStep_CMin_corestep'. constructor. reflexivity.
         simpl. eapply corestep_plus_one. eapply CompCertStep_CMin_corestep'. constructor. reflexivity.
    simpl.
       eapply matchInj_state_seq; eauto.
        simpl. eapply  switch_match_cont; eauto.
Qed.

Lemma MS_step_case_Switch:
forall cenv sz f tfn j m tm e lenv te sp lo hi cs k tk xenv a x x0 ts cases n
(EvalA: Csharpminor.eval_expr ge e lenv m a (Vint n))
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MCS : match_callstack prog j m tm (Frame cenv tfn e lenv te sp lo hi :: cs)
        (Mem.nextblock m) (Mem.nextblock tm))
(MK : match_cont k tk cenv xenv cs)
(EQ : transl_expr cenv a = OK (x, x0))
(EQ0 : transl_lblstmt cenv (switch_env cases xenv) cases
        (Sswitch x (switch_table cases 0) (length (switch_table cases 0))) =
      OK ts)
(*NEW:*) (PG: meminj_preserves_globals ge j),
exists c2' : CMin_core,
  exists m2' : mem,
          corestep_plus CMin_core_sem tge (CMin_State tfn ts tk (Vptr sp Int.zero) te) tm c2' m2' /\
         match_cores (CSharpMin_State f (seq_of_lbl_stmt (select_switch n cases)) k e lenv)  j
                               (CSharpMin_State f (seq_of_lbl_stmt (select_switch n cases)) k e lenv) m c2' m2'.
Proof. intros.
  exploit transl_expr_correct; eauto. intros [tv [EVAL [VINJ APP]]].
  inv VINJ.
  exploit MS_switch_descent; eauto. intros [k1 [A B]].
  exploit MS_switch_ascent; eauto. intros [k2 [C D]].
  exploit transl_lblstmt_suffix; eauto. simpl. intros [body' [ts' E]].
  exploit MS_switch_MSI; eauto. intros [T2 [m2' [F G]]].
  exists T2; exists m2'; split.
      eapply corestep_plus_star_trans.
          eapply B.
      eapply corestep_star_trans.
         eapply corestep_star_one. eapply CompCertStep_CMin_corestep'. constructor. eassumption. reflexivity.
      simpl.
        eapply corestep_star_trans.
         apply C.
         eapply corestep_plus_star. eapply F.
  simpl. eapply MSI_MC. apply PG. apply G.
Qed.

Lemma MS_step_case_ReturnNone:
forall cenv sz f tfn j m tm e lenv te sp lo hi cs k tk xenv m'
(Freelist: Mem.free_list m (blocks_of_env e) = Some m')
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MCS : match_callstack prog j m tm (Frame cenv tfn e lenv te sp lo hi :: cs)
                 (Mem.nextblock m) (Mem.nextblock tm))
(MK : match_cont tk k cenv xenv cs)
(*NEW:*) (PG: meminj_preserves_globals ge j),
exists c2' : CMin_core,
  exists m2' : mem,
        corestep_plus CMin_core_sem tge (CMin_State tfn (Sreturn None) k (Vptr sp Int.zero) te) tm c2' m2'  /\
       match_cores (CSharpMin_Returnstate Vundef (Csharpminor.call_cont tk))  j
                             (CSharpMin_Returnstate Vundef (Csharpminor.call_cont tk)) m' c2' m2'.
Proof. intros.
  exploit match_callstack_freelist; eauto. intros [tm' [A [B C]]].
  eexists; eexists; split.
     apply corestep_plus_one. eapply CompCertStep_CMin_corestep'. eapply step_return_0. eauto. reflexivity.
  simpl in *.
    econstructor; eauto. eapply match_call_cont; eauto.
Qed.

Lemma MS_step_case_ReturnSome:
forall cenv sz f tfn j m tm e lenv te sp lo hi cs k tk xenv a x x0 m' v
(EvalA: Csharpminor.eval_expr ge e lenv m a v)
(Freelist: Mem.free_list m (blocks_of_env e) = Some m')
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MCS : match_callstack prog j m tm (Frame cenv tfn e lenv te sp lo hi :: cs)
        (Mem.nextblock m) (Mem.nextblock tm))
(MK : match_cont tk k cenv xenv cs)
(EQ : transl_expr cenv a = OK (x, x0))
(*NEW:*) (PG: meminj_preserves_globals ge j),
exists c2' : CMin_core,
  exists m2' : mem,
        corestep_plus CMin_core_sem tge (CMin_State tfn (Sreturn (Some x)) k (Vptr sp Int.zero) te) tm c2' m2' /\
        match_cores  (CSharpMin_Returnstate v (Csharpminor.call_cont tk)) j
                 (CSharpMin_Returnstate v (Csharpminor.call_cont tk)) m' c2' m2'.
Proof. intros.
  exploit transl_expr_correct; eauto. intros [tv [EVAL [VINJ APP]]].
  exploit match_callstack_freelist; eauto. intros [tm' [A [B C]]].
  eexists; eexists; split.
     apply corestep_plus_one. eapply CompCertStep_CMin_corestep'. eapply step_return_1. eauto. eauto. reflexivity.
  simpl in *.
    econstructor; eauto. eapply match_call_cont; eauto.
Qed.

Lemma MS_step_case_Label:
forall cenv sz f tfn j m tm e lenv te sp lo hi cs k tk xenv lbl x s
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MCS : match_callstack prog j m tm (Frame cenv tfn e lenv te sp lo hi :: cs)
        (Mem.nextblock m) (Mem.nextblock tm))
(MK : match_cont k tk cenv xenv cs)
(EQ : transl_stmt cenv xenv s = OK x)
(*NEW:*) (PG: meminj_preserves_globals ge j),
exists c2' : CMin_core,
  exists m2' : mem,
       corestep_plus CMin_core_sem tge (CMin_State tfn (Slabel lbl x) tk (Vptr sp Int.zero) te) tm c2' m2' /\
      match_cores (CSharpMin_State f s k e lenv)  j (CSharpMin_State f s k e lenv) m c2' m2'.
Proof. intros.
  eexists; eexists; split.
    eapply corestep_plus_one. eapply CompCertStep_CMin_corestep'. constructor. reflexivity.
  simpl.
  econstructor; eauto.
Qed.

Lemma MS_step_case_Goto:
forall cenv sz f tfn j m tm e lenv te sp lo hi cs k tk xenv lbl s' k'
(FindLab: Csharpminor.find_label lbl (Csharpminor.fn_body f)
       (Csharpminor.call_cont k) = Some (s', k'))
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MCS : match_callstack prog j m tm (Frame cenv tfn e lenv te sp lo hi :: cs)
        (Mem.nextblock m) (Mem.nextblock tm))
(MK : match_cont k tk cenv xenv cs)
(*NEW:*) (PG: meminj_preserves_globals ge j),
exists c2' : CMin_core,
  exists m2' : mem,
       corestep_plus CMin_core_sem tge (CMin_State tfn (Sgoto lbl) tk (Vptr sp Int.zero) te) tm c2' m2' /\
       match_cores  (CSharpMin_State f s' k' e lenv) j (CSharpMin_State f s' k' e lenv) m c2' m2'.
Proof. intros.
  exploit transl_find_label_body; eauto.
  intros [ts' [tk' [xenv' [A [B C]]]]].
  eexists; eexists; split.
    eapply corestep_plus_one. eapply CompCertStep_CMin_corestep'. apply step_goto. eexact A. reflexivity.
  simpl.
  econstructor; eauto.
Qed.

(******************************Functions required for internal call rule*****************************)
(****These extend the original lemmas by additional guarantees of the (now exposed) memory injections, in order
    for the overall lemma for internal calls to establish the inject_separated fact******************************)

Lemma MS_match_callstack_alloc_variables_rec:
  forall tm sp tf cenv le te lo cs,
  Mem.valid_block tm sp ->
  fn_stackspace tf <= Int.max_unsigned ->
  (forall ofs k p, Mem.perm tm sp ofs k p -> 0 <= ofs < fn_stackspace tf) ->
  (forall ofs k p, 0 <= ofs < fn_stackspace tf -> Mem.perm tm sp ofs k p) ->
  forall e1 m1 vars e2 m2,
  alloc_variables e1 m1 vars e2 m2 ->
  forall f1,
  list_norepet (map fst vars) ->
  cenv_compat cenv vars (fn_stackspace tf) ->
  cenv_separated cenv vars ->
  cenv_mem_separated cenv vars f1 sp m1 ->
  (forall id sz, In (id, sz) vars -> e1!id = None) ->
  match_callstack prog f1 m1 tm
    (Frame (cenv_remove cenv vars) tf e1 le te sp lo (Mem.nextblock m1) :: cs)
    (Mem.nextblock m1) (Mem.nextblock tm) ->
  Mem.inject f1 m1 tm ->
  exists f2,
    match_callstack prog f2 m2 tm
      (Frame cenv tf e2 le te sp lo (Mem.nextblock m2) :: cs)
      (Mem.nextblock m2) (Mem.nextblock tm)
  /\ Mem.inject f2 m2 tm
  /\ (*LENB: THIS IS NEW*) inject_incr f1 f2
(****************The following three conditions are new******************)
  /\ (forall b, Mem.valid_block m1 b -> f2 b = f1 b)
  /\ (forall b b' d', f1 b = None -> f2 b = Some (b',d') -> b' = sp)
  /\ forall j',  inject_incr f2 j' -> inject_separated f2 j' m2 tm ->
                 inject_separated f2 j' m1 tm.
Proof.
Proof.
  intros until cs; intros VALID REPRES STKSIZE STKPERMS.
  induction 1; intros f1 NOREPET COMPAT SEP1 SEP2 UNBOUND MCS MINJ.
  (* base case *)
  simpl in MCS. exists f1.
   split. assumption.
   split. assumption.
   split. apply inject_incr_refl.
   split. auto.
   split. intros. rewrite H in H0; inv H0.
   intros. assumption.
  (* inductive case *)
  simpl in NOREPET. inv NOREPET.
(* exploit Mem.alloc_result; eauto. intros RES.
  exploit Mem.nextblock_alloc; eauto. intros NB.*)
  exploit (COMPAT id sz). auto with coqlib. intros [ofs [CENV [ALIGNED [LOB HIB]]]].
  exploit Mem.alloc_left_mapped_inject.
    eexact MINJ.
    eexact H.
    eexact VALID.
    instantiate (1 := ofs). zify. omega.
    intros. exploit STKSIZE; eauto. omega.
    intros. apply STKPERMS. zify. omega.
    replace (sz - 0) with sz by omega. auto.
    intros. eapply SEP2. eauto with coqlib. eexact CENV. eauto. eauto. omega.
  intros [f2 [A [B [C D]]]].
  exploit (IHalloc_variables f2); eauto.
    red; intros. eapply COMPAT. auto with coqlib.
    red; intros. eapply SEP1; eauto with coqlib.
    red; intros. exploit Mem.perm_alloc_inv; eauto. destruct (eq_block b b1); intros P.
    subst b. rewrite C in H5; inv H5.
    exploit SEP1. eapply in_eq. eapply in_cons; eauto. eauto. eauto.
    red; intros; subst id0. elim H3. change id with (fst (id, sz0)). apply in_map; auto.
    omega.
    eapply SEP2. apply in_cons; eauto. eauto.
    rewrite D in H5; eauto. eauto. auto.
    intros. rewrite PTree.gso. eapply UNBOUND; eauto with coqlib.
    red; intros; subst id0. elim H3. change id with (fst (id, sz0)). apply in_map; auto.
    eapply match_callstack_alloc_left; eauto.
    rewrite cenv_remove_gso; auto.
    apply UNBOUND with sz; auto with coqlib.
  intros. destruct H1 as [f3 [HF1 [HF2 [Hf3 [HF4 [HF5 HF6]]]]]].
    exists f3. split; trivial.
    split; trivial.
    split. eapply inject_incr_trans; eassumption.
    split. intros.
        rewrite HF4.
         apply D.
           intros N; subst.
               eapply (Mem.fresh_block_alloc _ _ _ _ _ H H1).
           apply (Mem.valid_block_alloc _ _ _ _ _ H _ H1).
    split; intros.
       destruct (eq_block b b1); subst.
       rewrite (Hf3 _ _ _ C) in H2. inv H2. trivial.
       specialize (D _ n).
         rewrite <- D in H1. apply (HF5 _ _ _ H1 H2).
    intros b; intros.
      destruct (H2 _ _ _ H5 H6).
      split; trivial.
      intros N. apply H7; clear H7.
      apply (Mem.valid_block_alloc _ _ _ _ _ H) in N.
      eapply alloc_variables_forward. eassumption. apply N.
Qed.

Lemma MS_match_callstack_alloc_variables_aux:
  forall tm1 sp tm2 m1 vars e m2 cenv f1 cs fn le te,
  Mem.alloc tm1 0 (fn_stackspace fn) = (tm2, sp) ->
  fn_stackspace fn <= Int.max_unsigned ->
  alloc_variables empty_env m1 vars e m2 ->
  list_norepet (map fst vars) ->
  cenv_compat cenv vars (fn_stackspace fn) ->
  cenv_separated cenv vars ->
  (forall id ofs, cenv!id = Some ofs -> In id (map fst vars)) ->
  Mem.inject f1 m1 tm1 ->
  match_callstack prog f1 m1 tm1 cs (Mem.nextblock m1) (Mem.nextblock tm1) ->
  match_temps f1 le te ->
  exists f2,
    match_callstack prog f2 m2 tm2 (Frame cenv fn e le te sp (Mem.nextblock m1) (Mem.nextblock m2) :: cs)
                    (Mem.nextblock m2) (Mem.nextblock tm2)
  /\ Mem.inject f2 m2 tm2
  /\ (*LENB: THIS IS NEW*) inject_incr f1 f2
(****************The following three conditions are new******************)
(* In the third clause, we now stepfrom  m' to m, and also from f' to f and from tm' to tm******************)
  /\ (forall b, Mem.valid_block m1 b -> f2 b = f1 b)
  /\ (forall b b' d', f1 b = None -> f2 b = Some (b',d') -> b' = sp)
  /\ forall j',  inject_incr f2 j' -> Events.inject_separated f2 j' m2 tm2 ->
          Events.inject_separated f2 j' m1 tm1.
Proof. clear core_data.
  intros.
  unfold build_compilenv in H.
assert (AR: exists f',
   match_callstack prog f' m2 tm2
                     (Frame cenv fn e le te sp (Mem.nextblock m1) (Mem.nextblock m2) :: cs)
                     (Mem.nextblock m2) (Mem.nextblock tm2)

  /\ Mem.inject f' m2 tm2
  /\ inject_incr f1 f'
  /\ (forall b, Mem.valid_block m1 b -> f' b = f1 b)
  /\ (forall b b' d', f1 b = None -> f' b = Some (b',d') -> b' = sp)
  /\ forall j',  inject_incr f' j' -> Events.inject_separated f' j' m2 tm2 ->
                  Events.inject_separated f' j' m1 tm2).

  eapply MS_match_callstack_alloc_variables_rec; eauto with mem.
  (*instantiate (1 := f1).*) red; intros. eelim Mem.fresh_block_alloc; eauto.
  eapply Mem.valid_block_inject_2; eauto.
  intros. apply PTree.gempty.
  eapply match_callstack_alloc_right; eauto.
  intros. destruct (In_dec peq id (map fst vars)).
  apply cenv_remove_gss; auto.
  rewrite cenv_remove_gso; auto.
  destruct (cenv!id) as [ofs|] eqn:?; auto. elim n; eauto.
  eapply Mem.alloc_right_inject; eauto.

destruct AR as  [f' [INC [INJ [MC [VB1 [SP SEP]]]]]].
exists f' ; intuition.
  intros b; intros.
  remember (f' b) as z; destruct z; apply eq_sym in Heqz.
  (*Some p*) destruct p.
            assert (j' b = Some (b0,z)). apply (H9 _ _ _ Heqz). inv H11.
   (*None*) assert (HH:= SEP _ H9 H10).
                     destruct (HH _ _ _ Heqz H12).
                     split; trivial.
                     intros N. apply H14. eapply Mem.valid_block_alloc; eauto.
Qed.

Lemma MS_match_callstack_alloc_variables:
  forall tm1 sp tm2 m1 vars e m2 cenv f1 cs fn le te,
  Mem.alloc tm1 0 (fn_stackspace fn) = (tm2, sp) ->
  fn_stackspace fn <= Int.max_unsigned ->
  alloc_variables empty_env m1 vars e m2 ->
  list_norepet (map fst vars) ->
  cenv_compat cenv vars (fn_stackspace fn) ->
  cenv_separated cenv vars ->
  (forall id ofs, cenv!id = Some ofs -> In id (map fst vars)) ->
  Mem.inject f1 m1 tm1 ->
  match_callstack prog f1 m1 tm1 cs (Mem.nextblock m1) (Mem.nextblock tm1) ->
  match_temps f1 le te ->
  exists f2,
    match_callstack prog f2 m2 tm2 (Frame cenv fn e le te sp (Mem.nextblock m1) (Mem.nextblock m2) :: cs)
                    (Mem.nextblock m2) (Mem.nextblock tm2)
  /\ Mem.inject f2 m2 tm2
  /\ (*LENB: THIS IS NEW*) inject_incr f1 f2
  /\ (*LENB this clause in new in coop-sim proof*) inject_separated f1 f2 m1 tm1.
Proof.
  intros.
  destruct (MS_match_callstack_alloc_variables_aux
     _ _ _ _ _ _ _ _ _ _ _ _ _ H H0 H1 H2 H3 H4 H5 H6 H7 H8)
     as [f2 [MCS2 [INJ2 [INC [HH1 [HH2 HH3]]]]]].
  exists f2.
  split; trivial.
  split; trivial.
  split; trivial.
  intros b; intros.
  specialize (HH2 _ _ _ H9 H10); subst.
  split. intros N. rewrite (HH1 _ N) in H10.
         rewrite H10 in H9; discriminate.
  eapply (Mem.fresh_block_alloc _ _ _ _ _ H).
Qed.

(***** All the additional conditions in the above auxiliary lemmas were needed for proving
 the condition Events.inject_separated j j' m tm in his lemma; otherwise, the claim is as before,
  just updated by replacing star step by corestep_star, as ususal*)

Theorem MS_match_callstack_function_entry:
  forall fn cenv tf m e m' tm tm' sp f cs args targs le,
  build_compilenv fn = (cenv, tf.(fn_stackspace)) ->
  tf.(fn_stackspace) <= Int.max_unsigned ->
  list_norepet (map fst (Csharpminor.fn_vars fn)) ->
  list_norepet (Csharpminor.fn_params fn) ->
  list_disjoint (Csharpminor.fn_params fn) (Csharpminor.fn_temps fn) ->
  alloc_variables Csharpminor.empty_env m (Csharpminor.fn_vars fn) e m' ->
  bind_parameters (Csharpminor.fn_params fn) args (create_undef_temps fn.(fn_temps)) = Some le ->
  val_list_inject f args targs ->
  Mem.alloc tm 0 tf.(fn_stackspace) = (tm', sp) ->
  match_callstack prog f m tm cs (Mem.nextblock m) (Mem.nextblock tm) ->
  Mem.inject f m tm ->
  let te := set_locals (Csharpminor.fn_temps fn) (set_params targs (Csharpminor.fn_params fn)) in
  exists f',
     match_callstack prog f' m' tm'
                     (Frame cenv tf e le te sp (Mem.nextblock m) (Mem.nextblock m') :: cs)
                     (Mem.nextblock m') (Mem.nextblock tm')
  /\ Mem.inject f' m' tm'
  /\ (*LENB: this clause is new in Restructured Proof*) inject_incr f f'
  /\ (*LENB this clause in new in coop-sim proof*) inject_separated f f' m tm.
Proof.
  intros.
  exploit build_compilenv_sound; eauto. intros [C1 C2].
  eapply MS_match_callstack_alloc_variables; eauto.
  intros. eapply build_compilenv_domain; eauto.
  eapply bind_parameters_agree; eauto.
Qed.

Lemma MS_step_case_InternalCall:
forall cenv  f j m tm e cs k tk vargs targs x m1 lenv
(Param1: list_norepet (map fst (Csharpminor.fn_vars f)))
(Param2 : list_norepet (Csharpminor.fn_params f))
(Param3 : list_disjoint (Csharpminor.fn_params f) (fn_temps f))
(AlocVars : alloc_variables empty_env m (Csharpminor.fn_vars f) e m1)
(BindParams: bind_parameters (Csharpminor.fn_params f) vargs
       (create_undef_temps (fn_temps f)) = Some lenv)
(MINJ : Mem.inject j m tm)
(MCS : match_callstack prog j m tm cs (Mem.nextblock m) (Mem.nextblock tm))
(MK : match_cont k tk cenv nil cs)
(ISCC : Csharpminor.is_call_cont k)
(ARGSINJ : val_list_inject j vargs targs)
(EQ : transl_function f = OK x)
(*NEW:*) (PG: meminj_preserves_globals ge j),
exists (c2' : CMin_core) (m2' : mem),
  corestep_plus CMin_core_sem tge (CMin_Callstate (AST.Internal x) targs tk) tm c2' m2'
 /\ exists (j' : meminj),
  inject_incr j j' /\
  inject_separated j j' m tm /\
  match_cores (CSharpMin_State f (Csharpminor.fn_body f) k e lenv) j'
    (CSharpMin_State f (Csharpminor.fn_body f) k e lenv) m1 c2' m2'.
Proof. intros.
  generalize EQ; clear EQ; unfold transl_function.
  caseEq (build_compilenv f). intros ce sz BC.
  destruct (zle sz Int.max_unsigned).
  Focus 2. intros. exfalso. clear core_data.  congruence. (*core data versus congruence bug; Xavier's proof has
             destruct (zle sz Int.max_unsigned); try congruence here....*)
  intro TRBODY.
  generalize TRBODY; intro TMP. monadInv TMP.
  set (tf := mkfunction (Csharpminor.fn_sig f)
                        (Csharpminor.fn_params f)
                        (Csharpminor.fn_temps f)
                        sz
                        x0) in *.
  caseEq (Mem.alloc tm 0 (fn_stackspace tf)). intros tm' sp ALLOC'.
  exploit MS_match_callstack_function_entry; eauto. simpl; eauto. simpl; auto.
  intros [j' [MCS2 [MINJ2 [IINCR SEP]]]].
  exists (CMin_State tf x0 tk (Vptr sp Int.zero)
     (set_locals (fn_temps f) (set_params targs (Csharpminor.fn_params f)))).
  exists tm'.
  split.
    eapply corestep_plus_one. simpl.
    econstructor.
    constructor. assumption. reflexivity.
  exists j'. split. assumption.
  split. assumption.
  econstructor. eexact TRBODY. eauto. eexact MINJ2.
  eexact MCS2.
  inv MK; simpl in ISCC; contradiction || econstructor; eauto.
solve [eapply meminj_preserves_incr_sep; eassumption].
Qed.

(******************End of updated section for internal call rule*****************************)
(************************************************************************************)

Lemma MS_step_case_Return:
forall j m tm cs f e lenv k tk cenv v tv optid
(MINJ : Mem.inject j m tm)
(MCS : match_callstack prog j m tm cs (Mem.nextblock m) (Mem.nextblock tm))
(MK : match_cont (Csharpminor.Kcall optid f e lenv k) tk cenv nil cs)
(RESINJ : val_inject j v tv)
(*NEW:*) (PG: meminj_preserves_globals ge j),
exists c2' : CMin_core,
  exists m2' : mem,
       corestep_plus CMin_core_sem tge (CMin_Returnstate tv tk) tm c2' m2'  /\
       match_cores  (CSharpMin_State f Csharpminor.Sskip k e (set_optvar optid v lenv)) j
             (CSharpMin_State f Csharpminor.Sskip k e (set_optvar optid v lenv)) m c2' m2' .
Proof. intros.
  inv MK. simpl.
  eexists; eexists; split.
       eapply corestep_plus_one. eapply CompCertStep_CMin_corestep'. econstructor; eauto. reflexivity.
  simpl.
  unfold set_optvar. destruct optid; simpl option_map; econstructor; eauto.
         eapply match_callstack_set_temp; eauto.
Qed.

Lemma MS_step: forall (c1 : core_data) (m1 : mem) (c1' : core_data) (m1' : mem),
corestep CSharpMin_core_sem ge c1 m1 c1' m1' ->
forall (c2 : CMin_core) (m2 : mem) (j : meminj),
match_cores c1 j c1 m1 c2 m2 ->
(exists c2' : CMin_core,
   exists m2' : mem,
     exists j' : meminj,
       inject_incr j j' /\
       Events.inject_separated j j' m1 m2 /\
       corestep_plus CMin_core_sem tge c2 m2 c2' m2' /\
       match_cores c1' j' c1' m1' c2' m2') \/
(MC_measure c1' < MC_measure c1)%nat /\ match_cores c1' j c1' m1' c2 m2.
Proof.
  intros. unfold core_data in *.
   destruct (CSharpMin_corestep_2_CompCertStep _ _ _ _ _ H) as [t Ht]. simpl in *.
  apply CSharpMin_corestep_not_at_external in H.
   assert (PG:= match_cores_genvs _ _ _ _ _ _ H0).
   apply MC_MSI in H0. rename H0 into MSTATE.
   inv Ht; simpl in *.
  (*skip seq*)
      destruct c1; simpl in *; try inv H1.
      destruct c1'; simpl in *; try inv H3.
      inv MSTATE; simpl in *.
      monadInv TR.
      destruct c2; simpl in *; try inv H8.
      destruct (MS_step_case_SkipSeq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        TRF MINJ MK MCS PG) as [c2' [m2' [cstepPlus MS]]].
      left. exists c2'. exists m2'. exists j.
      split. apply inject_incr_refl.
      split. apply inject_separated_same_meminj.
      auto.
  (*skip Block*)
      destruct c1; simpl in *; try inv H1.
      destruct c1'; simpl in *; try inv H3.
      inv MSTATE; simpl in *.
      monadInv TR.
      destruct c2; simpl in *; try inv H8.
      destruct (MS_step_case_SkipBlock _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        TRF MINJ MK MCS PG) as [c2' [m2' [cstepPlus MS]]].
      left. exists c2'. exists m2'. exists j.
      split. apply inject_incr_refl.
      split. apply inject_separated_same_meminj.
      auto.
  (*skip Call*)
      destruct c1; simpl in *; try inv H0.
      destruct c1'; simpl in *; try inv H1.
      inv MSTATE; simpl in *.
      monadInv TR.
      destruct c2; simpl in *; try inv H10.
      destruct (MS_step_case_SkipCall  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        H2 H4 TRF MINJ MK MCS PG) as [c2' [m2' [cstepPlus MS]]].
      left. exists c2'. exists m2'. exists j.
      split. apply inject_incr_refl.
      split. apply inject_separated_same_meminj.
      auto.
   (*assign*)
      destruct c1; simpl in *; try inv H0.
      destruct c1'; simpl in *; try inv H1.
      inv MSTATE; simpl in *.
      monadInv TR.
      destruct c2; simpl in *; try inv H9.
      rename  m1' into m'. rename m' into m.
      rename m2 into tm. rename k0 into tk.
      rename f0 into tfn. rename e0 into te.
      rename le0 into lenv.
      destruct (MS_step_case_Assign  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        id H3 TRF MINJ MK MCS EQ PG) as [c2' [m2' [cstepPlus MS]]].
      left. exists c2'. exists m2'. exists j.
      split. apply inject_incr_refl.
      split. apply inject_separated_same_meminj.
      auto.
   (*set case has disappeared*)
   (*store*)
      destruct c1; simpl in *; try inv H0.
      destruct c1'; simpl in *; try inv H1.
      inv MSTATE; simpl in *.
      monadInv TR.
      destruct c2; simpl in *; try inv H11.
      rename f0 into tfn. rename m1 into m. rename m2  into tm.
      rename e0 into te. rename k0 into tk. rename  m1' into m'.
      destruct (MS_step_case_Store _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        H5 H2 H3 TRF MINJ MCS MK EQ EQ1 PG) as [c2' [m2' [cstepPlus MS]]].
      left. exists c2'. exists m2'. exists j.
      split. apply inject_incr_refl.
      split. apply inject_separated_same_meminj.
      auto.
   (*call*)
      destruct c1; simpl in *; try inv H0.
      destruct c1'; simpl in *; try inv H1.
      inv MSTATE; simpl in *.
      monadInv TR.
      destruct c2; simpl in *; try inv H11.
      rename f into fd. rename f0 into f. rename f1 into tfn.
      rename m1' into m. rename m2  into tm. rename e into te.
      rename e0 into e.  rename k0 into tk. rename  le0 into le.
      destruct (MS_step_case_Call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        optid _ _ H2 H3 H4 TRF MINJ MCS MK EQ EQ1 PG) as [c2' [m2' [cstepPlusMS]]].
      left. exists c2'. exists m2'. exists j.
      split. apply inject_incr_refl.
      split. apply inject_separated_same_meminj.
      auto.
  (*builtin*)
      destruct c1; simpl in *; try inv H0.
      destruct c1'; simpl in *; try inv H1.
      inv MSTATE; simpl in *.
      monadInv TR.
      destruct c2; simpl in *; try inv H10.
      rename f0 into tfn.
      rename m1 into m. rename m2  into tm. rename e into te.
      rename e0 into e.  rename k0 into tk. rename  le0 into le.  rename m1' into m'.
      destruct (MS_step_case_Builtin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ optid
        _ _ _ _ H2 H4 TRF MINJ MCS MK EQ PG)
        as [c2' [m2' [cstepPlus [j' [InjIncr [InjSep MS]]]]]].
      left. exists c2'. exists m2'.  exists j'. auto.
  (* seq *)
      destruct c1; simpl in *; try inv H1.
      destruct c1'; simpl in *; try inv H3.
     rename k0 into k.
      inv MSTATE.
      (*Case 1*)
         monadInv TR. left.
         destruct c2; simpl in *; try inv H8.
         rename f0 into tfn. rename e0 into te. rename k0 into tk.
         exists  (CMin_State tfn x (Kseq x0 tk) (Vptr sp Int.zero) te). exists m2.
         exists j.
                split. apply inject_incr_refl.
                split. apply inject_separated_same_meminj.
                split; simpl.
                    eapply corestep_plus_one.
                    eapply CompCertStep_CMin_corestep.
                    econstructor; eauto. reflexivity.
                econstructor; eauto.
                          econstructor; eauto.
      (* seq 2 *)
         destruct c2; simpl in *; try inv H9.
         right. split. omega.
                   econstructor; eauto.
(* ifthenelse *)
      destruct c1; simpl in *; try inv H0.
      destruct c1'; simpl in *; try inv H1.
      inv MSTATE.
      monadInv TR.
      destruct c2; simpl in *; try inv H10.
         rename f0 into tfn. rename e0 into te. rename k0 into tk.
      rename m1' into m. rename m2  into tm.
      destruct (MS_step_case_Ite _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        H2 H4 TRF MINJ MCS MK EQ EQ1 EQ0 PG) as [c2' [m2' [cstepPlus MS]]].
      left. exists c2'. exists m2'. exists j.
      split. apply inject_incr_refl.
      split. apply inject_separated_same_meminj.
      auto.
  (*loop*)
      destruct c1; simpl in *; try inv H1.
      destruct c1'; simpl in *; try inv H3.
      inv MSTATE.
      monadInv TR.
      destruct c2; simpl in *; try inv H8.
         rename f0 into tfn. rename e0 into te. rename k0 into tk.
      rename m1' into m. rename m2  into tm.
      destruct (MS_step_case_Loop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        TRF MINJ MCS MK EQ PG) as [c2' [m2' [cstepPlus MS]]].
      left. exists c2'. exists m2'. exists j.
      split. apply inject_incr_refl.
      split. apply inject_separated_same_meminj.
      auto.
  (*block*)
      destruct c1; simpl in *; try inv H1.
      destruct c1'; simpl in *; try inv H3.
      inv MSTATE.
      monadInv TR.
      destruct c2; simpl in *; try inv H8.
         rename f0 into tfn. rename e0 into te. rename k0 into tk.
      rename m1' into m. rename m2  into tm.  rename s0 into s.
      destruct (MS_step_case_Block _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        TRF MINJ MCS MK EQ PG) as [c2' [m2' [cstepPlus MS]]].
      left. exists c2'. exists m2'. exists j.
      split. apply inject_incr_refl.
      split. apply inject_separated_same_meminj.
      auto.
  (*exit seq*)
      destruct c1; simpl in *; try inv H1.
      destruct c1'; simpl in *; try inv H3.
      inv MSTATE.
      monadInv TR.
      destruct c2; simpl in *; try inv H8.
         rename f0 into tfn. rename e0 into te. rename k0 into tk.
      rename m1' into m. rename m2  into tm.
      destruct (MS_step_case_ExitSeq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n _
        TRF MINJ MCS MK PG) as [c2' [m2' [cstepPlus MS]]].
      left. exists c2'. exists m2'. exists j.
      split. apply inject_incr_refl.
      split. apply inject_separated_same_meminj.
      auto.
  (*exit block 0*)
      destruct c1; simpl in *; try inv H1.
      destruct c1'; simpl in *; try inv H3.
      inv MSTATE.
      monadInv TR.
      destruct c2; simpl in *; try inv H8.
         rename f0 into tfn. rename e0 into te. rename k0 into tk.
      rename m1' into m. rename m2  into tm.
      destruct (MS_step_case_ExitBlockZero _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        TRF MINJ MCS MK PG) as [c2' [m2' [cstepPlus MS]]].
      left. exists c2'. exists m2'. exists j.
      split. apply inject_incr_refl.
      split. apply inject_separated_same_meminj.
      auto.
  (*exit block n+1*)
      destruct c1; simpl in *; try inv H1.
      destruct c1'; simpl in *; try inv H3.
      inv MSTATE.
      monadInv TR.
      destruct c2; simpl in *; try inv H8.
         rename f0 into tfn. rename e0 into te. rename k0 into tk.
      rename m1' into m. rename m2  into tm.
      destruct (MS_step_case_ExitBlockNonzero _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        n TRF MINJ MCS MK PG) as [c2' [m2' [cstepPlus MS]]].
      left. exists c2'. exists m2'. exists j.
      split. apply inject_incr_refl.
      split. apply inject_separated_same_meminj.
      auto.
  (*switch*)
      destruct c1; simpl in *; try inv H0.
      destruct c1'; simpl in *; try inv H1.
      inv MSTATE.
      monadInv TR.
      destruct c2; simpl in *; try inv H9.
         rename f0 into tfn.  rename e0 into te.
         rename k0 into tk. rename m1' into m. rename m2  into tm.  rename s into ts.
      destruct (MS_step_case_Switch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        H3 TRF MINJ MCS MK EQ EQ0 PG) as [c2' [m2' [cstepPlus MS]]].
      left. exists c2'. exists m2'. exists j.
      split. apply inject_incr_refl.
      split. apply inject_separated_same_meminj.
      auto.
  (*return none*)
      destruct c1; simpl in *; try inv H0.
      destruct c1'; simpl in *; try inv H1.
      inv MSTATE.
      monadInv TR.
      destruct c2; simpl in *; try inv H9.
       rename f into tfn.  rename f0 into f. rename e into te. rename e0 into e.
         rename k0 into tk. rename m1 into m. rename m2  into tm.
         rename m1'  into m'.  rename le0 into le.
      destruct (MS_step_case_ReturnNone _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        H3 TRF MINJ MCS MK PG) as [c2' [m2' [cstepPlus MS]]].
      left. exists c2'. exists m2'. exists j.
      split. apply inject_incr_refl.
      split. apply inject_separated_same_meminj.
      auto.
  (*return some*)
      destruct c1; simpl in *; try inv H0.
      destruct c1'; simpl in *; try inv H1.
      inv MSTATE.
      monadInv TR.
      destruct c2; simpl in *; try inv H10.
       rename f into tfn.  rename f0 into f. rename e into te.
         rename e0 into e. rename k into tk.
         rename k0 into k. rename m1 into m. rename m2  into tm.
         rename m1'  into m'.  rename le0 into le. rename v0 into v.
      destruct (MS_step_case_ReturnSome _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        H2 H4 TRF MINJ MCS MK EQ PG) as [c2' [m2' [cstepPlus MS]]].
      left. exists c2'. exists m2'. exists j.
      split. apply inject_incr_refl.
      split. apply inject_separated_same_meminj.
      auto.
  (*label*)
      destruct c1; simpl in *; try inv H1.
      destruct c1'; simpl in *; try inv H3.
      inv MSTATE.
      monadInv TR.
      destruct c2; simpl in *; try inv H8.
       rename f0 into tfn. rename e0 into te.
         rename k0 into tk. rename m1' into m. rename m2  into tm. rename s0 into s.
      destruct (MS_step_case_Label _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        lbl _ _ TRF MINJ MCS MK EQ PG) as [c2' [m2' [cstepPlus MS]]].
      left. exists c2'. exists m2'. exists j.
      split. apply inject_incr_refl.
      split. apply inject_separated_same_meminj.
      auto.
  (*goto*)
      destruct c1; simpl in *; try inv H0.
      destruct c1'; simpl in *; try inv H1.
      inv MSTATE.
      monadInv TR.
      destruct c2; simpl in *; try inv H9.
       rename f0 into tfn. rename e0 into te.
         rename k1 into tk. rename s into s'.  rename k into k'.
         rename k0 into k. rename m1' into m. rename m2  into tm.
      destruct (MS_step_case_Goto _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        H3 TRF MINJ MCS MK PG) as [c2' [m2' [cstepPlus MS]]].
      left. exists c2'. exists m2'. exists j.
      split. apply inject_incr_refl.
      split. apply inject_separated_same_meminj.
      auto.
(* internal call *)
      destruct c1; simpl in *; try inv H0.
      destruct c1'; simpl in *; try inv H1.
      inv MSTATE.
      monadInv TR.
      destruct c2; simpl in *; try inv H11.
      rename m1 into m. rename m2 into tm.
      rename f0 into f. rename e0 into e.
      rename m1' into m1. rename args into vargs.
      rename k0 into tk. rename le0 into lenv.
      rename args0 into targs.
      destruct (MS_step_case_InternalCall _ _ _ _ _ _ _ _ _ _ _ _ _ _
        H2 H3 H4 H5 H7 MINJ MCS MK ISCC ARGSINJ EQ PG)
        as [c2' [m2' [cstepPlus [j' [InjIncr [InjSep MS]]]]]].
      left. exists c2'. exists m2'. exists j'. auto.
(* external call *)
      destruct c1; simpl in *; try inv H0. inv H.
   (*nothing to show here - cf corestep not at external *)

(* return *)
      destruct c1; simpl in *; try inv H1.
      destruct c1'; simpl in *; try inv H3.
      inv MSTATE.
      destruct c2; simpl in *; try inv H5.
      rename m1' into m. rename m2 into tm. rename f0 into f.
      rename e0 into e. rename k into tk. rename k0 into k.
      rename v into tv. rename v0 into v.
      destruct (MS_step_case_Return _ _ _ _ _ _ _ _ _ _ _
        tv optid MINJ MCS MK RESINJ PG) as [c2' [m2' [cstepPlus MS]]].
      left. exists c2'. exists m2'. exists j.
      split. apply inject_incr_refl.
      split. apply inject_separated_same_meminj.
      auto.
Qed.

Require Import sepcomp.forward_simulations.

Require Import sepcomp.forward_simulations_lemmas.

(*program structure not yet updated to module*)
Theorem transl_program_correct:
  forall (R: list_norepet (map fst (prog_defs prog)))
         entrypoints
         (entry_points_ok :
            forall v1 v2 sig,
              In (v1, v2, sig) entrypoints ->
              exists b f1 f2,
                v1 = Vptr b Int.zero
                /\ v2 = Vptr b Int.zero
                /\ Genv.find_funct_ptr ge b = Some f1
                /\ Genv.find_funct_ptr tge b = Some f2)
         (init_mem: exists m0, Genv.init_mem prog = Some m0),
  Forward_simulation_inj.Forward_simulation_inject
       CSharpMin_core_sem
       CMin_core_sem ge tge entrypoints.
Proof.
intros.
 eapply inj_simulation_star with
  (match_states:=match_cores)(measure:=MC_measure).
 (*genvs_dom_eq*)
    unfold genvs_domain_eq, genv2blocks.
    simpl; split; intros.
     split; intros; destruct H as [id Hid].
      rewrite <- (symbols_preserved _ _ TRANSL) in Hid.
      exists id; assumption.
     rewrite (symbols_preserved _ _ TRANSL) in Hid.
      exists id; assumption.
     split; intros; destruct H as [id Hid].
      rewrite <- (varinfo_preserved _ _ TRANSL) in Hid.
      exists id; assumption.
     rewrite (varinfo_preserved _ _ TRANSL) in Hid.
      exists id; assumption.
  apply match_cores_valid.
 (*preserves_globals*) apply match_cores_genvs.
 (*init_cores*)
    intros.
    eapply (init_cores _ _ _ entrypoints); eauto.
    destruct init_mem as [m0 INIT].
    exists m0; split; auto.
    unfold meminj_preserves_globals in H3.
    destruct H3 as [A [B C]].

    assert (P: forall p q, {Ple p q} + {Plt q p}).
      intros p q.
      case_eq (Pos.leb p q).
      intros TRUE.
      apply Pos.leb_le in TRUE.
      left; auto.
      intros FALSE.
      apply Pos.leb_gt in FALSE.
      right; auto.

    cut (forall b, Plt b (Mem.nextblock m0) ->
           exists id, Genv.find_symbol ge id = Some b). intro D.

    split.
    destruct (P (Mem.nextblock m0) (Mem.nextblock m1)); auto.
    exfalso.
    destruct (D _ p).
    apply A in H3.
    assert (Mem.valid_block m1 (Mem.nextblock m1)).
      eapply Mem.valid_block_inject_1; eauto.
    clear - H4; unfold Mem.valid_block in H4.
    xomega.

    destruct (P (Mem.nextblock m0) (Mem.nextblock m2)); auto.
    exfalso.
    destruct (D _ p).
    apply A in H3.
    assert (Mem.valid_block m2 (Mem.nextblock m2)).
      eapply Mem.valid_block_inject_2; eauto.
    clear - H4; unfold Mem.valid_block in H4.
    xomega.

    intros b LT.
    unfold ge.
    apply valid_init_is_global with (b := b) in INIT.
    eapply INIT; auto.
    apply R.
    apply LT.

  (*halted*)
  { intros.
    eapply MC_safely_halted in H; eauto.
    destruct H as [v2 [A [B C]]].
    solve[exists v2; split; auto]. }
  (*at_external*)
  { intros.
    destruct (MC_at_external _ _ _ _ _ _ _ _ _ H H0)
           as [Inc [Presv [vals2 [ValsInj AtExt2]]]].
    split; trivial.
    exists vals2.
    split; trivial. }
 (*after_external*)
 {  intros.
    assert (PG: meminj_preserves_globals ge j).
      destruct H; subst.
      apply (match_cores_genvs _ _ _ _ _ _ H9).
    destruct (MC_after_external _ _ _ _ _ _ _ _ _ _ _ _ _ _ H H0
             PG H1 H2 H3 H4 H5 H6 H7 H8)
           as [dd [core [dd' [afterExtA [afterExtB [ MC X]]]]]].
     subst. eexists; eexists. eexists.
        split. eassumption.
        split. eassumption.
        split. reflexivity. eassumption. }
  (*core_diagram*)
  { intros. destruct (MS_step _ _ _ _ H _ _ _ H0).
    destruct H1 as [c2' [m2' [j' [INC [Sep [CSP MC]]]]]].
      exists c2', m2', j'.
       split; trivial.
       split; trivial.
       split; trivial.
       left; trivial.
    destruct H1.
      exists c2, m2, j.
      split. apply inject_incr_refl.
      split. apply inject_separated_same_meminj.
      split; trivial.
      right. split; trivial.
      apply corestep_star_zero. }
Qed.

Lemma MS_step_coopsem: forall (c1 : core_data) (m1 : mem) (c1' : core_data) (m1' : mem),
corestep csharpmin_coop_sem ge c1 m1 c1' m1' ->
forall (c2 : CMin_core) (m2 : mem) (j : meminj),
match_cores c1 j c1 m1 c2 m2 ->
(exists c2' : CMin_core,
   exists m2' : mem,
     exists j' : meminj,
       inject_incr j j' /\
       Events.inject_separated j j' m1 m2 /\
       corestep_plus cmin_coop_sem tge c2 m2 c2' m2' /\
       match_cores c1' j' c1' m1' c2' m2') \/
(MC_measure c1' < MC_measure c1)%nat /\ match_cores c1' j c1' m1' c2 m2.
Proof. intros.
  eapply MS_step; eauto.
Qed.

Theorem transl_program_correct_coopsem:
  forall (R: list_norepet (map fst (prog_defs prog)))
         entrypoints
         (entry_points_ok :
            forall v1 v2 sig,
              In (v1, v2, sig) entrypoints ->
              exists b f1 f2,
                v1 = Vptr b Int.zero
                /\ v2 = Vptr b Int.zero
                /\ Genv.find_funct_ptr ge b = Some f1
                /\ Genv.find_funct_ptr tge b = Some f2)
         (init_mem: exists m0, Genv.init_mem prog = Some m0),
  Forward_simulation_inj.Forward_simulation_inject csharpmin_coop_sem
   cmin_coop_sem ge tge entrypoints.
Proof.
intros.
 eapply inj_simulation_star with
  (match_states:=match_cores)(measure:=MC_measure).
 (*genvs_dom_eq*)
    unfold genvs_domain_eq, genv2blocks.
    simpl; split; intros.
     split; intros; destruct H as [id Hid].
      rewrite <- (symbols_preserved _ _ TRANSL) in Hid.
      exists id; assumption.
     rewrite (symbols_preserved _ _ TRANSL) in Hid.
      exists id; assumption.
     split; intros; destruct H as [id Hid].
      rewrite <- (varinfo_preserved _ _ TRANSL) in Hid.
      exists id; assumption.
     rewrite (varinfo_preserved _ _ TRANSL) in Hid.
      exists id; assumption.
  apply match_cores_valid.
 (*preserves_globals*) apply match_cores_genvs.
 (*init_cores*)
    intros.
    eapply (init_cores _ _ _ entrypoints); eauto.
    destruct init_mem as [m0 INIT].
    exists m0; split; auto.
    unfold meminj_preserves_globals in H3.
    destruct H3 as [A [B C]].

    assert (P: forall p q, {Ple p q} + {Plt q p}).
      intros p q.
      case_eq (Pos.leb p q).
      intros TRUE.
      apply Pos.leb_le in TRUE.
      left; auto.
      intros FALSE.
      apply Pos.leb_gt in FALSE.
      right; auto.

    cut (forall b, Plt b (Mem.nextblock m0) ->
           exists id, Genv.find_symbol ge id = Some b). intro D.

    split.
    destruct (P (Mem.nextblock m0) (Mem.nextblock m1)); auto.
    exfalso.
    destruct (D _ p).
    apply A in H3.
    assert (Mem.valid_block m1 (Mem.nextblock m1)).
      eapply Mem.valid_block_inject_1; eauto.
    clear - H4; unfold Mem.valid_block in H4.
    xomega.

    destruct (P (Mem.nextblock m0) (Mem.nextblock m2)); auto.
    exfalso.
    destruct (D _ p).
    apply A in H3.
    assert (Mem.valid_block m2 (Mem.nextblock m2)).
      eapply Mem.valid_block_inject_2; eauto.
    clear - H4; unfold Mem.valid_block in H4.
    xomega.

    intros b LT.
    unfold ge.
    apply valid_init_is_global with (b := b) in INIT.
    eapply INIT; auto.
    apply R.
    apply LT.
  (*halted*)
  { intros.
    eapply MC_safely_halted in H; eauto.
    destruct H as [v2 [A [B C]]].
    solve[exists v2; split; auto]. }
  (*at_external*)
  { intros.
    destruct (MC_at_external _ _ _ _ _ _ _ _ _ H H0)
           as [Inc [Presv [vals2 [ValsInj AtExt2]]]].
    split; trivial.
    exists vals2.
    split; trivial. }
 (*after_external*)
 {  intros.
    assert (PG: meminj_preserves_globals ge j).
      destruct H; subst.
      apply (match_cores_genvs _ _ _ _ _ _ H9).
    destruct (MC_after_external _ _ _ _ _ _ _ _ _ _ _ _ _ _ H H0
             PG H1 H2 H3 H4 H5 H6 H7 H8)
           as [dd [core [dd' [afterExtA [afterExtB [ MC X]]]]]].
     subst. eexists; eexists. eexists.
        split. eassumption.
        split. eassumption.
        split. reflexivity. eassumption. }
  (*core_diagram*)
  { intros. destruct (MS_step_coopsem _ _ _ _ H _ _ _ H0).
    destruct H1 as [c2' [m2' [j' [INC [Sep [CSP MC]]]]]].
      exists c2', m2', j'.
       split; trivial.
       split; trivial.
       split; trivial.
       left; trivial.
    destruct H1.
      exists c2, m2, j.
      split. apply inject_incr_refl.
      split. apply inject_separated_same_meminj.
      split; trivial.
      right. split; trivial.
      apply corestep_star_zero. }
Qed.

End TRANSLATION.