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

Require Import sepcomp.Cminor.
Require Import sepcomp.Cminor_coop.

Inductive cmin_effstep (g: Cminor.genv):  (block -> Z -> bool) ->
            CMin_core -> mem -> CMin_core -> mem -> Prop :=

  | cmin_effstep_skip_seq: forall f s k sp e m,
      cmin_effstep g EmptyEffect (CMin_State f Sskip (Kseq s k) sp e) m
         (CMin_State f s k sp e) m

  | cmin_effstep_skip_block: forall f k sp e m,
      cmin_effstep g EmptyEffect (CMin_State f Sskip (Kblock k) sp e) m
         (CMin_State f Sskip k sp e) m

  | cmin_effstep_skip_call: forall f k sp e m m',
      is_call_cont k ->
      Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
      cmin_effstep g (FreeEffect m 0 (f.(fn_stackspace)) sp) (CMin_State f Sskip k (Vptr sp Int.zero) e) m
         (CMin_Returnstate Vundef k) m'

  | cmin_effstep_assign: forall f id a k sp e m v,
      eval_expr g sp e m a v ->
      cmin_effstep g EmptyEffect (CMin_State f (Sassign id a) k sp e) m
         (CMin_State f Sskip k sp (PTree.set id v e)) m

  | cmin_effstep_store: forall f chunk addr a k sp e m vaddr v m',
      eval_expr g sp e m addr vaddr ->
      eval_expr g sp e m a v ->
      Mem.storev chunk m vaddr v = Some m' ->
      cmin_effstep g (StoreEffect vaddr (encode_val chunk v)) (CMin_State f (Sstore chunk addr a) k sp e) m
         (CMin_State f Sskip k sp e) m'

  | cmin_effstep_call: forall f optid sig a bl k sp e m vf vargs fd,
      eval_expr g sp e m a vf ->
      eval_exprlist g sp e m bl vargs ->
      Genv.find_funct g vf = Some fd ->
      funsig fd = sig ->
      cmin_effstep g EmptyEffect (CMin_State f (Scall optid sig a bl) k sp e) m
         (CMin_Callstate fd vargs (Kcall optid f sp e k)) m

  | cmin_effstep_tailcall: forall f sig a bl k sp e m vf vargs fd m',
      eval_expr g (Vptr sp Int.zero) e m a vf ->
      eval_exprlist g (Vptr sp Int.zero) e m bl vargs ->
      Genv.find_funct g vf = Some fd ->
      funsig fd = sig ->
      Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
      cmin_effstep g (FreeEffect m 0 (f.(fn_stackspace)) sp) (CMin_State f (Stailcall sig a bl) k (Vptr sp Int.zero) e) m
         (CMin_Callstate fd vargs (call_cont k)) m'

(* WE DO NOT TREAT BUILTINS *)
(*| cmin_effstep_builtin: forall f optid ef bl k sp e m vargs t vres m',
      eval_exprlist g sp e m bl vargs ->
      external_call ef g vargs m t vres m' ->
      cmin_effstep g (BuiltinEffect g (ef_sig ef) vargs m) (CMin_State f (Sbuiltin optid ef bl) k sp e) m
          (CMin_State f Sskip k sp (set_optvar optid vres e)) m'*)

  | cmin_effstep_seq: forall f s1 s2 k sp e m,
      cmin_effstep g EmptyEffect (CMin_State f (Sseq s1 s2) k sp e) m
         (CMin_State f s1 (Kseq s2 k) sp e) m

  | cmin_effstep_ifthenelse: forall f a s1 s2 k sp e m v b,
      eval_expr g sp e m a v ->
      Val.bool_of_val v b ->
      cmin_effstep g EmptyEffect (CMin_State f (Sifthenelse a s1 s2) k sp e) m
         (CMin_State f (if b then s1 else s2) k sp e) m

  | cmin_effstep_loop: forall f s k sp e m,
      cmin_effstep g EmptyEffect (CMin_State f (Sloop s) k sp e) m
         (CMin_State f s (Kseq (Sloop s) k) sp e) m

  | cmin_effstep_block: forall f s k sp e m,
      cmin_effstep g EmptyEffect (CMin_State f (Sblock s) k sp e) m
         (CMin_State f s (Kblock k) sp e) m

  | cmin_effstep_exit_seq: forall f n s k sp e m,
      cmin_effstep g EmptyEffect (CMin_State f (Sexit n) (Kseq s k) sp e) m
         (CMin_State f (Sexit n) k sp e) m

  | cmin_effstep_exit_block_0: forall f k sp e m,
      cmin_effstep g EmptyEffect (CMin_State f (Sexit O) (Kblock k) sp e) m
         (CMin_State f Sskip k sp e) m
  | cmin_effstep_exit_block_S: forall f n k sp e m,
      cmin_effstep g EmptyEffect (CMin_State f (Sexit (S n)) (Kblock k) sp e) m
         (CMin_State f (Sexit n) k sp e) m

  | cmin_effstep_switch: forall f a cases default k sp e m n,
      eval_expr g sp e m a (Vint n) ->
      cmin_effstep g EmptyEffect (CMin_State f (Sswitch a cases default) k sp e) m
         (CMin_State f (Sexit (Switch.switch_target n default cases)) k sp e) m

  | cmin_effstep_return_0: forall f k sp e m m',
      Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
      cmin_effstep g (FreeEffect m 0 (f.(fn_stackspace)) sp) (CMin_State f (Sreturn None) k (Vptr sp Int.zero) e) m
         (CMin_Returnstate Vundef (call_cont k)) m'
  | cmin_effstep_return_1: forall f a k sp e m v m',
      eval_expr g (Vptr sp Int.zero) e m a v ->
      Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
      cmin_effstep g (FreeEffect m 0 (f.(fn_stackspace)) sp) (CMin_State f (Sreturn (Some a)) k (Vptr sp Int.zero) e) m
         (CMin_Returnstate v (call_cont k)) m'

  | cmin_effstep_label: forall f lbl s k sp e m,
      cmin_effstep g EmptyEffect (CMin_State f (Slabel lbl s) k sp e) m
         (CMin_State f s k sp e) m

  | cmin_effstep_goto: forall f lbl k sp e m s' k',
      find_label lbl f.(fn_body) (call_cont k) = Some(s', k') ->
      cmin_effstep g EmptyEffect (CMin_State f (Sgoto lbl) k sp e) m
         (CMin_State f s' k' sp e) m

  | cmin_effstep_internal_function: forall f vargs k m m' sp e,
      Mem.alloc m 0 f.(fn_stackspace) = (m', sp) ->
      set_locals f.(fn_vars) (set_params vargs f.(fn_params)) = e ->
      cmin_effstep g EmptyEffect (CMin_Callstate (Internal f) vargs k) m
         (CMin_State f f.(fn_body) k (Vptr sp Int.zero) e) m'

(*no external functions in coresteps!
  | cmin_effstep_external_function: forall ef vargs k m t vres m',
      external_call ef g vargs m t vres m' ->
      cmin_effstep g EmptyEffect (CMin_Callstate (External ef) vargs k) m
         (CMin_Returnstate vres k) m'*)

  | cmin_effstep_return: forall v optid f sp e k m,
      cmin_effstep g EmptyEffect (CMin_Returnstate v (Kcall optid f sp e k)) m
        (CMin_State f Sskip k sp (set_optvar optid v e)) m

  | cmin_effstep_sub_val: forall E EE c m c' m',
      (forall b ofs, Mem.valid_block m b ->
                     E b ofs = true -> EE b ofs = true) ->
      cmin_effstep g E c m c' m' ->
      cmin_effstep g EE c m c' m'.

Lemma cminstep_effax1: forall (M : block -> Z -> bool) g c m c' m',
      cmin_effstep g M c m c' m' ->
      (corestep cmin_coop_sem g c m c' m' /\
       Mem.unchanged_on (fun (b : block) (ofs : Z) => M b ofs = false) m m').
Proof.
intros.
  induction H.
  split. unfold corestep, coopsem; simpl. econstructor.
         apply Mem.unchanged_on_refl.
  split. unfold corestep, coopsem; simpl. econstructor.
         apply Mem.unchanged_on_refl.
  split. unfold corestep, coopsem; simpl. econstructor; eassumption.
         eapply FreeEffect_free; eassumption.
  split. unfold corestep, coopsem; simpl. econstructor; eassumption.
         apply Mem.unchanged_on_refl.
  split. unfold corestep, coopsem; simpl. econstructor; eassumption.
         eapply StoreEffect_Storev; eassumption.
  split. unfold corestep, coopsem; simpl. econstructor; try eassumption. trivial.
         apply Mem.unchanged_on_refl.
  split. unfold corestep, coopsem; simpl. econstructor; try eassumption. trivial.
         eapply FreeEffect_free; eassumption.
(*  split. unfold corestep, coopsem; simpl. econstructor; try eassumption.
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
         eapply FreeEffect_free; eassumption.
  split. unfold corestep, coopsem; simpl. econstructor; eassumption.
         eapply FreeEffect_free; eassumption.
  split. unfold corestep, coopsem; simpl. econstructor; eassumption.
         apply Mem.unchanged_on_refl.
  split. unfold corestep, coopsem; simpl. econstructor; eassumption.
         apply Mem.unchanged_on_refl.
  split. unfold corestep, coopsem; simpl. econstructor; try eassumption. trivial.
         eapply Mem.alloc_unchanged_on; eassumption.
  (*no external call*)
  split. unfold corestep, coopsem; simpl. econstructor; eassumption.
         apply Mem.unchanged_on_refl.
  (*effstep_sub_val*)
    destruct IHcmin_effstep.
    split; trivial.
    eapply unchanged_on_validblock; try eassumption.
    intros; simpl. remember (E b ofs) as d.
    destruct d; trivial. apply eq_sym in Heqd.
    rewrite (H _ _ H3 Heqd) in H4. discriminate.
Qed.

Lemma cminstep_effax2: forall  g c m c' m',
      corestep cmin_coop_sem g c m c' m' ->
      exists M, cmin_effstep g M c m c' m'.
Proof.
intros. inv H.
    eexists. eapply cmin_effstep_skip_seq.
    eexists. eapply cmin_effstep_skip_block.
    eexists. eapply cmin_effstep_skip_call; try eassumption.
    eexists. eapply cmin_effstep_assign; eassumption.
    eexists. eapply cmin_effstep_store; eassumption.
    eexists. eapply cmin_effstep_call; try eassumption. reflexivity.
    eexists. eapply cmin_effstep_tailcall; try eassumption. reflexivity.
(*    eexists. eapply cmin_effstep_builtin; eassumption.*)
    eexists. eapply cmin_effstep_seq.
    eexists. eapply cmin_effstep_ifthenelse; eassumption.
    eexists. eapply cmin_effstep_loop.
    eexists. eapply cmin_effstep_block.
    eexists. eapply cmin_effstep_exit_seq.
    eexists. eapply cmin_effstep_exit_block_0.
    eexists. eapply cmin_effstep_exit_block_S.
    eexists. eapply cmin_effstep_switch; eassumption.
    eexists. eapply cmin_effstep_return_0; try eassumption.
    eexists. eapply cmin_effstep_return_1; try eassumption.
    eexists. eapply cmin_effstep_label.
    eexists. eapply cmin_effstep_goto; eassumption.
    eexists. eapply cmin_effstep_internal_function; try eassumption. reflexivity.
    eexists. eapply cmin_effstep_return; try eassumption.
Qed.

Program Definition cmin_eff_sem :
  @EffectSem Cminor.genv CMin_core.
eapply Build_EffectSem with (sem := cmin_coop_sem)(effstep:=cmin_effstep).
apply cminstep_effax1.
apply cminstep_effax2.
intros.
eapply cmin_effstep_sub_val; eassumption.
Defined.
