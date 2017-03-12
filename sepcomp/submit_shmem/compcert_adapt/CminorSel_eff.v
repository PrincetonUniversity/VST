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

Require Import sepcomp.CminorSel.
Require Import sepcomp.CminorSel_coop.

Inductive cminsel_effstep (g:genv):  (block -> Z -> bool) ->
            CMinSel_core -> mem -> CMinSel_core -> mem -> Prop :=

  | cminsel_effstep_skip_seq: forall f s k sp e m,
      cminsel_effstep g EmptyEffect (CMinSel_State f Sskip (Kseq s k) sp e) m
         (CMinSel_State f s k sp e) m

  | cminsel_effstep_skip_block: forall f k sp e m,
      cminsel_effstep g EmptyEffect (CMinSel_State f Sskip (Kblock k) sp e) m
         (CMinSel_State f Sskip k sp e) m

  | cminsel_effstep_skip_call: forall f k sp e m m',
      is_call_cont k ->
      Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
      cminsel_effstep g (FreeEffect m 0 (f.(fn_stackspace)) sp)
         (CMinSel_State f Sskip k (Vptr sp Int.zero) e) m
         (CMinSel_Returnstate Vundef k) m'

  | cminsel_effstep_assign: forall f id a k sp e m v,
      CminorSel.eval_expr g sp e m nil a v ->
      cminsel_effstep g EmptyEffect (CMinSel_State f (Sassign id a) k sp e) m
         (CMinSel_State f Sskip k sp (PTree.set id v e)) m


  | cminsel_effstep_store: forall f chunk addr al b k sp e m vl v vaddr m',
      CminorSel.eval_exprlist g sp e m nil al vl ->
      CminorSel.eval_expr g sp e m nil b v ->
      Op.eval_addressing g sp addr vl = Some vaddr ->
      Mem.storev chunk m vaddr v = Some m' ->
      cminsel_effstep g (StoreEffect vaddr (encode_val chunk v))
        (CMinSel_State f (Sstore chunk addr al b) k sp e) m
        (CMinSel_State f Sskip k sp e) m'

  | cminsel_effstep_call:forall f optid sig a bl k sp e m vf vargs fd,
      CminorSel.eval_expr_or_symbol g sp e m nil a vf ->
      CminorSel.eval_exprlist g sp e m nil bl vargs ->
      Genv.find_funct g vf = Some fd ->
      funsig fd = sig ->
      cminsel_effstep g EmptyEffect
         (CMinSel_State f (Scall optid sig a bl) k sp e) m
         (CMinSel_Callstate fd vargs (Kcall optid f sp e k)) m

  | cminsel_effstep_tailcall: forall f sig a bl k sp e m vf vargs fd m',
      CminorSel.eval_expr_or_symbol g (Vptr sp Int.zero) e m nil a vf ->
      CminorSel.eval_exprlist g (Vptr sp Int.zero) e m nil bl vargs ->
      Genv.find_funct g vf = Some fd ->
      funsig fd = sig ->
      Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
      cminsel_effstep g (FreeEffect m 0 (f.(fn_stackspace)) sp)
        (CMinSel_State f (Stailcall sig a bl) k (Vptr sp Int.zero) e) m
        (CMinSel_Callstate fd vargs (call_cont k)) m'

(* WE DO NOT TREAT BUILTINS
  | cminsel_effstep_builtin: forall f optid ef al k sp e m vl t v m',
      CminorSel.eval_exprlist g sp e m nil al vl ->
      external_call ef g vl m t v m' ->
      cminsel_effstep g (BuiltinEffect g (ef_sig ef) vl m)
          (CMinSel_State f (Sbuiltin optid ef al) k sp e) m
          (CMinSel_State f Sskip k sp (Cminor.set_optvar optid v e)) m'
*)
  | cminsel_effstep_seq: forall f s1 s2 k sp e m,
      cminsel_effstep g EmptyEffect (CMinSel_State f (Sseq s1 s2) k sp e) m
         (CMinSel_State f s1 (Kseq s2 k) sp e) m

  | cminsel_effstep_ifthenelse:  forall f c s1 s2 k sp e m b,
      CminorSel.eval_condexpr g sp e m nil c b ->
      cminsel_effstep g EmptyEffect
         (CMinSel_State f (Sifthenelse c s1 s2) k sp e) m
         (CMinSel_State f (if b then s1 else s2) k sp e) m

  | cminsel_effstep_loop: forall f s k sp e m,
      cminsel_effstep g EmptyEffect
         (CMinSel_State f (Sloop s) k sp e) m
         (CMinSel_State f s (Kseq (Sloop s) k) sp e) m

  | cminsel_effstep_block: forall f s k sp e m,
      cminsel_effstep g EmptyEffect (CMinSel_State f (Sblock s) k sp e) m
         (CMinSel_State f s (Kblock k) sp e) m

  | cminsel_effstep_exit_seq: forall f n s k sp e m,
      cminsel_effstep g EmptyEffect (CMinSel_State f (Sexit n) (Kseq s k) sp e) m
         (CMinSel_State f (Sexit n) k sp e) m

  | cminsel_effstep_exit_block_0: forall f k sp e m,
      cminsel_effstep g EmptyEffect (CMinSel_State f (Sexit O) (Kblock k) sp e) m
         (CMinSel_State f Sskip k sp e) m
  | cminsel_effstep_exit_block_S: forall f n k sp e m,
      cminsel_effstep g EmptyEffect (CMinSel_State f (Sexit (S n)) (Kblock k) sp e) m
         (CMinSel_State f (Sexit n) k sp e) m

  | cminsel_effstep_switch: forall f a cases default k sp e m n,
      CminorSel.eval_expr g sp e m nil a (Vint n) ->
      cminsel_effstep g EmptyEffect
         (CMinSel_State f (Sswitch a cases default) k sp e) m
         (CMinSel_State f (Sexit (Switch.switch_target n default cases)) k sp e) m

  | cminsel_effstep_return_0: forall f k sp e m m',
      Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
      cminsel_effstep g (FreeEffect m 0 (f.(fn_stackspace)) sp) (CMinSel_State f (Sreturn None) k (Vptr sp Int.zero) e) m
         (CMinSel_Returnstate Vundef (call_cont k)) m'
  | cminsel_effstep_return_1: forall f a k sp e m v m',
      CminorSel.eval_expr g (Vptr sp Int.zero) e m nil a v ->
      Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
      cminsel_effstep g (FreeEffect m 0 (f.(fn_stackspace)) sp)
         (CMinSel_State f (Sreturn (Some a)) k (Vptr sp Int.zero) e) m
         (CMinSel_Returnstate v (call_cont k)) m'

  | cminsel_effstep_label: forall f lbl s k sp e m,
      cminsel_effstep g EmptyEffect
         (CMinSel_State f (Slabel lbl s) k sp e) m
         (CMinSel_State f s k sp e) m

  | cminsel_effstep_goto: forall f lbl k sp e m s' k',
      find_label lbl f.(fn_body) (call_cont k) = Some(s', k') ->
      cminsel_effstep g EmptyEffect
         (CMinSel_State f (Sgoto lbl) k sp e) m
         (CMinSel_State f s' k' sp e) m

  | cminsel_effstep_internal_function: forall f vargs k m m' sp e,
      Mem.alloc m 0 f.(fn_stackspace) = (m', sp) ->
      Cminor.set_locals f.(fn_vars) (Cminor.set_params vargs f.(fn_params)) = e ->
      cminsel_effstep g EmptyEffect
         (CMinSel_Callstate (Internal f) vargs k) m
         (CMinSel_State f f.(fn_body) k (Vptr sp Int.zero) e) m'

(*no external functions in coresteps!
  | cminsel_effstep_external_function: forall ef vargs k m t vres m',
      external_call ef g vargs m t vres m' ->
      cminsel_effstep g EmptyEffect
         (CMinSel_Callstate (External ef) vargs k) m
         (CMinSel_Returnstate vres k) m'*)

  | cminsel_effstep_return: forall v optid f sp e k m,
      cminsel_effstep g EmptyEffect
        (CMinSel_Returnstate v (Kcall optid f sp e k)) m
        (CMinSel_State f Sskip k sp (Cminor.set_optvar optid v e)) m

  | cminsel_effstep_sub_val: forall E EE c m c' m',
      (forall b ofs, Mem.valid_block m b ->
                     E b ofs = true -> EE b ofs = true) ->
      cminsel_effstep g E c m c' m' ->
      cminsel_effstep g EE c m c' m'.

Lemma cminselstep_effax1: forall (M : block -> Z -> bool) g c m c' m',
      cminsel_effstep g M c m c' m' ->
      (corestep cminsel_coop_sem g c m c' m' /\
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
    destruct IHcminsel_effstep.
    split; trivial.
    eapply unchanged_on_validblock; try eassumption.
    intros; simpl. remember (E b ofs) as d.
    destruct d; trivial. apply eq_sym in Heqd.
    rewrite (H _ _ H3 Heqd) in H4. discriminate.
Qed.

Lemma cminselstep_effax2: forall  g c m c' m',
      corestep cminsel_coop_sem g c m c' m' ->
      exists M, cminsel_effstep g M c m c' m'.
Proof.
intros. inv H.
    eexists. eapply cminsel_effstep_skip_seq.
    eexists. eapply cminsel_effstep_skip_block.
    eexists. eapply cminsel_effstep_skip_call; try eassumption.
    eexists. eapply cminsel_effstep_assign; eassumption.
    eexists. eapply cminsel_effstep_store; eassumption.
    eexists. eapply cminsel_effstep_call; try eassumption. reflexivity.
    eexists. eapply cminsel_effstep_tailcall; try eassumption. reflexivity.
(*    eexists. eapply cminsel_effstep_builtin; eassumption.*)
    eexists. eapply cminsel_effstep_seq.
    eexists. eapply cminsel_effstep_ifthenelse; eassumption.
    eexists. eapply cminsel_effstep_loop.
    eexists. eapply cminsel_effstep_block.
    eexists. eapply cminsel_effstep_exit_seq.
    eexists. eapply cminsel_effstep_exit_block_0.
    eexists. eapply cminsel_effstep_exit_block_S.
    eexists. eapply cminsel_effstep_switch; eassumption.
    eexists. eapply cminsel_effstep_return_0; try eassumption.
    eexists. eapply cminsel_effstep_return_1; try eassumption.
    eexists. eapply cminsel_effstep_label.
    eexists. eapply cminsel_effstep_goto; eassumption.
    eexists. eapply cminsel_effstep_internal_function; try eassumption. reflexivity.
    eexists. eapply cminsel_effstep_return; try eassumption.
Qed.

Program Definition cminsel_eff_sem :
  @EffectSem genv CMinSel_core.
eapply Build_EffectSem with (sem := cminsel_coop_sem)(effstep:=cminsel_effstep).
apply cminselstep_effax1.
apply cminselstep_effax2.
intros.
eapply cminsel_effstep_sub_val; eassumption.
Defined.
