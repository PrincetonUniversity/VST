Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import compcert.common.Values.
Require Import Memory.
Require Export Maps.
Require Import Events.
Require Import Globalenvs.

Require Import sepcomp.mem_lemmas. (*for mem_forward*)
Require Import sepcomp.core_semantics.
Require Import sepcomp.effect_semantics.

Require Import sepcomp.Csharpminor.
Require Import sepcomp.Csharpminor_coop.

Lemma EmptyEffect_allocvariables: forall L e m e' m'
      (ALLOC: alloc_variables e m L e' m'),
  Mem.unchanged_on (fun b ofs => EmptyEffect b ofs = false) m m'.
Proof. intros L.
  induction L; simpl; intros; inv ALLOC.
    apply Mem.unchanged_on_refl.
  specialize (IHL _ _ _ _ H6). clear H6.
  eapply (unchanged_on_trans _ m1).
    eapply EmptyEffect_alloc; eassumption.
    eassumption.
  eapply alloc_forward; eassumption.
Qed.

Inductive csharpmin_effstep (g: Csharpminor.genv):  (block -> Z -> bool) ->
            CSharpMin_core -> mem -> CSharpMin_core -> mem -> Prop :=

  | csharpmin_effstep_skip_seq: forall f s k e le m,
      csharpmin_effstep g EmptyEffect (CSharpMin_State f Sskip (Kseq s k) e le) m
        (CSharpMin_State f s k e le) m
  | csharpmin_effstep_skip_block: forall f k e le m,
      csharpmin_effstep g EmptyEffect (CSharpMin_State f Sskip (Kblock k) e le) m
        (CSharpMin_State f Sskip k e le) m
  | csharpmin_effstep_skip_call: forall f k e le m m',
      is_call_cont k ->
      Mem.free_list m (blocks_of_env e) = Some m' ->
      csharpmin_effstep g (FreelistEffect m (blocks_of_env e)) (CSharpMin_State f Sskip k e le) m
        (CSharpMin_Returnstate Vundef k) m'

  | csharpmin_effstep_set: forall f id a k e le m v,
      eval_expr g e le m a v ->
      csharpmin_effstep g EmptyEffect (CSharpMin_State f (Sset id a) k e le) m
        (CSharpMin_State f Sskip k e (PTree.set id v le)) m

  | csharpmin_effstep_store: forall f chunk addr a k e le m vaddr v m',
      eval_expr g e le m addr vaddr ->
      eval_expr g e le m a v ->
      Mem.storev chunk m vaddr v = Some m' ->
      csharpmin_effstep g (StoreEffect vaddr (encode_val chunk v))
        (CSharpMin_State f (Sstore chunk addr a) k e le) m
        (CSharpMin_State f Sskip k e le) m'

  | csharpmin_effstep_call: forall f optid sig a bl k e le m vf vargs fd,
      eval_expr g e le m a vf ->
      eval_exprlist g e le m bl vargs ->
      Genv.find_funct g vf = Some fd ->
      funsig fd = sig ->
      csharpmin_effstep g EmptyEffect (CSharpMin_State f (Scall optid sig a bl) k e le) m
        (CSharpMin_Callstate fd vargs (Kcall optid f e le k)) m

(* WE DO NOT TREAT BUILTINS *)
(*  | csharpmin_effstep_builtin: forall f optid ef bl k e le m vargs t vres m',
      eval_exprlist g e le m bl vargs ->
      external_call ef g vargs m t vres m' ->
      csharpmin_effstep g (BuiltinEffect g (ef_sig ef) vargs m)
         (CSharpMin_State f (Sbuiltin optid ef bl) k e le) m
         (CSharpMin_State f Sskip k e (Cminor.set_optvar optid vres le)) m'*)

  | csharpmin_effstep_seq: forall f s1 s2 k e le m,
      csharpmin_effstep g EmptyEffect (CSharpMin_State f (Sseq s1 s2) k e le) m
        (CSharpMin_State f s1 (Kseq s2 k) e le) m

  | csharpmin_effstep_ifthenelse: forall f a s1 s2 k e le m v b,
      eval_expr g e le m a v ->
      Val.bool_of_val v b ->
      csharpmin_effstep g EmptyEffect (CSharpMin_State f (Sifthenelse a s1 s2) k e le) m
        (CSharpMin_State f (if b then s1 else s2) k e le) m

  | csharpmin_effstep_loop: forall f s k e le m,
      csharpmin_effstep g EmptyEffect (CSharpMin_State f (Sloop s) k e le) m
        (CSharpMin_State f s (Kseq (Sloop s) k) e le) m

  | csharpmin_effstep_block: forall f s k e le m,
      csharpmin_effstep g EmptyEffect (CSharpMin_State f (Sblock s) k e le) m
        (CSharpMin_State f s (Kblock k) e le) m

  | csharpmin_effstep_exit_seq: forall f n s k e le m,
      csharpmin_effstep g EmptyEffect (CSharpMin_State f (Sexit n) (Kseq s k) e le) m
        (CSharpMin_State f (Sexit n) k e le) m
  | csharpmin_effstep_exit_block_0: forall f k e le m,
      csharpmin_effstep g EmptyEffect (CSharpMin_State f (Sexit O) (Kblock k) e le) m
        (CSharpMin_State f Sskip k e le) m
  | csharpmin_effstep_exit_block_S: forall f n k e le m,
      csharpmin_effstep g EmptyEffect
        (CSharpMin_State f (Sexit (S n)) (Kblock k) e le) m
        (CSharpMin_State f (Sexit n) k e le) m

  | csharpmin_effstep_switch: forall f a cases k e le m n,
      eval_expr g e le m a (Vint n) ->
      csharpmin_effstep g EmptyEffect (CSharpMin_State f (Sswitch a cases) k e le) m
        (CSharpMin_State f (seq_of_lbl_stmt (select_switch n cases)) k e le) m

  | csharpmin_effstep_return_0: forall f k e le m m',
      Mem.free_list m (blocks_of_env e) = Some m' ->
      csharpmin_effstep g (FreelistEffect m (blocks_of_env e)) (CSharpMin_State f (Sreturn None) k e le) m
        (CSharpMin_Returnstate Vundef (call_cont k)) m'
  | csharpmin_effstep_return_1: forall f a k e le m v m',
      eval_expr g e le m a v ->
      Mem.free_list m (blocks_of_env e) = Some m' ->
      csharpmin_effstep g (FreelistEffect m (blocks_of_env e)) (CSharpMin_State f (Sreturn (Some a)) k e le) m
        (CSharpMin_Returnstate v (call_cont k)) m'
  | csharpmin_effstep_label: forall f lbl s k e le m,
      csharpmin_effstep g EmptyEffect (CSharpMin_State f (Slabel lbl s) k e le) m
        (CSharpMin_State f s k e le) m

  | csharpmin_effstep_goto: forall f lbl k e le m s' k',
      find_label lbl f.(fn_body) (call_cont k) = Some(s', k') ->
      csharpmin_effstep g EmptyEffect (CSharpMin_State f (Sgoto lbl) k e le) m
        (CSharpMin_State f s' k' e le) m

  | csharpmin_effstep_internal_function: forall f vargs k m m1 e le,
      list_norepet (map fst f.(fn_vars)) ->
      list_norepet f.(fn_params) ->
      list_disjoint f.(fn_params) f.(fn_temps) ->
      alloc_variables empty_env m (fn_vars f) e m1 ->
      bind_parameters f.(fn_params) vargs (create_undef_temps f.(fn_temps)) = Some le ->
      csharpmin_effstep g EmptyEffect
        (CSharpMin_Callstate (Internal f) vargs k) m
        (CSharpMin_State f f.(fn_body) k e le) m1
(* no external call
  | csharpmin_effstep_external_function: forall ef vargs k m t vres m',
      external_call ef g vargs m t vres m' ->
      csharpmin_effstep g EmptyEffect (CSharpMin_Callstate (External ef) vargs k) m
         (CSharpMin_Returnstate vres k) m' *)

  | csharpmin_effstep_return: forall v optid f e le k m,
      csharpmin_effstep g EmptyEffect (CSharpMin_Returnstate v (Kcall optid f e le k)) m
        (CSharpMin_State f Sskip k e (Cminor.set_optvar optid v le)) m


  | csharpmin_effstep_sub_val: forall E EE c m c' m',
      (forall b ofs, Mem.valid_block m b ->
                     E b ofs = true -> EE b ofs = true) ->
      csharpmin_effstep g E c m c' m' ->
      csharpmin_effstep g EE c m c' m'.

Lemma csharpminstep_effax1: forall (M : block -> Z -> bool) g c m c' m'
      (H: csharpmin_effstep g M c m c' m'),
       corestep csharpmin_coop_sem g c m c' m' /\
       Mem.unchanged_on (fun (b : block) (ofs : Z) => M b ofs = false) m m'.
Proof.
intros.
  induction H.
  split. unfold corestep, coopsem; simpl. econstructor.
         apply Mem.unchanged_on_refl.
  split. unfold corestep, coopsem; simpl. econstructor.
         apply Mem.unchanged_on_refl.
  split. unfold corestep, coopsem; simpl. econstructor; eassumption.
         eapply FreelistEffect_freelist; eassumption.
  split. unfold corestep, coopsem; simpl. econstructor; eassumption.
         apply Mem.unchanged_on_refl.
  split. unfold corestep, coopsem; simpl. econstructor; eassumption.
         eapply StoreEffect_Storev; eassumption.
  split. unfold corestep, coopsem; simpl. econstructor; try eassumption.
         apply Mem.unchanged_on_refl.
(*  split. unfold corestep, coopsem; simpl. econstructor; eassumption.
         eapply ec_builtinEffectPolymorphic; eassumption.*)
  split. unfold corestep, coopsem; simpl. econstructor; eassumption.
         apply Mem.unchanged_on_refl.
  split. unfold corestep, coopsem; simpl. econstructor; eassumption.
         apply Mem.unchanged_on_refl.
  split. unfold corestep, coopsem; simpl. econstructor; eassumption.
         apply Mem.unchanged_on_refl.
  split. unfold corestep, coopsem; simpl. econstructor; eassumption.
         apply Mem.unchanged_on_refl.
  split. unfold corestep, coopsem; simpl. econstructor; eassumption.
         apply Mem.unchanged_on_refl.
  split. unfold corestep, coopsem; simpl. econstructor; eassumption.
         apply Mem.unchanged_on_refl.
  split. unfold corestep, coopsem; simpl. econstructor; eassumption.
         apply Mem.unchanged_on_refl.
  split. unfold corestep, coopsem; simpl. econstructor; eassumption.
         apply Mem.unchanged_on_refl.
  split. unfold corestep, coopsem; simpl. econstructor; eassumption.
         eapply FreelistEffect_freelist; eassumption.
  split. unfold corestep, coopsem; simpl. econstructor; eassumption.
         eapply FreelistEffect_freelist; eassumption.
  split. unfold corestep, coopsem; simpl. econstructor; eassumption.
         apply Mem.unchanged_on_refl.
  split. unfold corestep, coopsem; simpl. econstructor; eassumption.
         apply Mem.unchanged_on_refl.
  split. unfold corestep, coopsem; simpl. econstructor; try eassumption.
         eapply EmptyEffect_allocvariables; eassumption.
  (*no external call*)
  split. unfold corestep, coopsem; simpl. econstructor; eassumption.
         apply Mem.unchanged_on_refl.
  (*effstep_sub_val*)
    destruct IHcsharpmin_effstep.
    split; trivial.
    eapply unchanged_on_validblock; try eassumption.
    intros; simpl. remember (E b ofs) as d.
    destruct d; trivial. apply eq_sym in Heqd.
    rewrite (H _ _ H3 Heqd) in H4. discriminate.
Qed.

Lemma csharpminstep_effax2: forall  g c m c' m',
      corestep csharpmin_coop_sem g c m c' m' ->
      exists M, csharpmin_effstep g M c m c' m'.
Proof.
intros. inv H.
    eexists. eapply csharpmin_effstep_skip_seq.
    eexists. eapply csharpmin_effstep_skip_block.
    eexists. eapply csharpmin_effstep_skip_call; try eassumption.
    eexists. eapply csharpmin_effstep_set; eassumption.
    eexists. eapply csharpmin_effstep_store; eassumption.
    eexists. eapply csharpmin_effstep_call; try eassumption. reflexivity.
(*    eexists. eapply csharpmin_effstep_builtin; eassumption.*)
    eexists. eapply csharpmin_effstep_seq.
    eexists. eapply csharpmin_effstep_ifthenelse; eassumption.
    eexists. eapply csharpmin_effstep_loop.
    eexists. eapply csharpmin_effstep_block.
    eexists. eapply csharpmin_effstep_exit_seq.
    eexists. eapply csharpmin_effstep_exit_block_0.
    eexists. eapply csharpmin_effstep_exit_block_S.
    eexists. eapply csharpmin_effstep_switch; eassumption.
    eexists. eapply csharpmin_effstep_return_0; try eassumption.
    eexists. eapply csharpmin_effstep_return_1; try eassumption.
    eexists. eapply csharpmin_effstep_label.
    eexists. eapply csharpmin_effstep_goto; eassumption.
    eexists. eapply csharpmin_effstep_internal_function; try eassumption.
    eexists. eapply csharpmin_effstep_return.
Qed.

Program Definition csharpmin_eff_sem :
  @EffectSem Csharpminor.genv CSharpMin_core.
eapply Build_EffectSem with (sem := csharpmin_coop_sem)(effstep:=csharpmin_effstep).
apply csharpminstep_effax1.
apply csharpminstep_effax2.
apply csharpmin_effstep_sub_val.
Defined.