Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Ctypes.
Require Import Cop.

Require Import compcert.cfrontend.Clight.
Require Import sepcomp.mem_lemmas.

Require Import sepcomp.semantics.
Require Import sepcomp.semantics_lemmas.

Require Import ccc26x86.BuiltinEffects.
Require Import sepcomp.val_casted.

Section CLIGHT_MEM.

Variable hf : I64Helpers.helper_functions.

Inductive CL_core: Type :=
  | CL_State
      (f: function)
      (s: statement)
      (k: cont)
      (e: env)
      (le: temp_env): CL_core
  | CL_Callstate
      (fd: fundef)
      (args: list val)
      (k: cont): CL_core
  | CL_Returnstate
      (res: val)
      (k: cont): CL_core.

Definition CL_at_external (c: CL_core) : option (external_function * signature * list val) :=
  match c with
  | CL_State _ _ _ _ _ => None
  | CL_Callstate fd args k =>
      match fd with
        Internal f => None
      | External ef targs tres cc =>
          if observableEF_dec (*hf *)ef && vals_def args
          then Some (ef, ef_sig ef, args)
          else None
      end
  | CL_Returnstate v k => None
 end.

Definition CL_after_external (rv: option val) (c: CL_core) : option CL_core :=
  match c with
     CL_Callstate fd vargs k =>
        match fd with
          Internal _ => None
        | External ef tps tp cc =>
            match rv with
              Some v => Some(CL_Returnstate v k)
            | None  => Some(CL_Returnstate Vundef k)
            end
        end
   | _ => None
  end.

Definition CL_halted (q : CL_core): option val :=
    match q with
       CL_Returnstate v Kstop =>
         if vals_def (v::nil) then Some v
         else None
     | _ => None
    end.

(** Transition relation *)

Section SEMANTICS.

Variable function_entry: function -> list val -> mem -> env -> temp_env -> mem -> Prop.

Variable ge: genv.
Inductive clight_corestep: CL_core -> mem-> CL_core -> mem -> Prop :=

  | clight_corestep_assign:   forall f a1 a2 k e le m loc ofs v2 v m',
      eval_lvalue ge e le m a1 loc ofs ->
      eval_expr ge e le m a2 v2 ->
      sem_cast v2 (typeof a2) (typeof a1) m = Some v ->
      assign_loc ge (typeof a1) m loc ofs v m' ->
      assign_loc ge (typeof a1) m loc ofs v m' ->
      clight_corestep (CL_State f (Sassign a1 a2) k e le) m
        (CL_State f Sskip k e le) m'

  | clight_corestep_set:   forall f id a k e le m v,
      eval_expr ge e le m a v ->
      clight_corestep (CL_State f (Sset id a) k e le) m
        (CL_State f Sskip k e (PTree.set id v le)) m

  | clight_corestep_call:   forall f optid a al k e le m tyargs tyres cconv vf vargs fd,
      classify_fun (typeof a) = fun_case_f tyargs tyres cconv ->
      eval_expr ge e le m a vf ->
      eval_exprlist ge e le m al tyargs vargs ->
      Genv.find_funct ge vf = Some fd ->
      type_of_fundef fd = Tfunction tyargs tyres cconv ->
      clight_corestep (CL_State f (Scall optid a al) k e le) m
        (CL_Callstate fd vargs (Kcall optid f e le k)) m
(*We don't currently support builtins
  | clight_corestep_builtin:   forall f optid ef tyargs al k e le m vargs t vres m',
      eval_exprlist ge e le m al tyargs vargs ->
      external_call ef ge vargs m t vres m' ->
      ~ observableEF (*hf*) ef ->
      clight_corestep (CL_State f (Sbuiltin optid ef tyargs al) k e le) m
         (CL_State f Sskip k e (set_opttemp optid vres le)) m'
*)
  | clight_corestep_seq:  forall f s1 s2 k e le m,
      clight_corestep (CL_State f (Ssequence s1 s2) k e le) m
        (CL_State f s1 (Kseq s2 k) e le) m
  | clight_corestep_skip_seq: forall f s k e le m,
      clight_corestep (CL_State f Sskip (Kseq s k) e le) m
        (CL_State f s k e le) m
  | clight_corestep_continue_seq: forall f s k e le m,
      clight_corestep (CL_State f Scontinue (Kseq s k) e le) m
        (CL_State f Scontinue k e le) m
  | clight_corestep_break_seq: forall f s k e le m,
      clight_corestep (CL_State f Sbreak (Kseq s k) e le) m
        (CL_State f Sbreak k e le) m

  | clight_corestep_ifthenelse:  forall f a s1 s2 k e le m v1 b,
      eval_expr ge e le m a v1 ->
      bool_val v1 (typeof a) m = Some b ->
      clight_corestep (CL_State f (Sifthenelse a s1 s2) k e le) m
        (CL_State f (if b then s1 else s2) k e le) m

  | clight_corestep_loop: forall f s1 s2 k e le m,
      clight_corestep (CL_State f (Sloop s1 s2) k e le) m
        (CL_State f s1 (Kloop1 s1 s2 k) e le) m
  | clight_corestep_skip_or_continue_loop1:  forall f s1 s2 k e le m x,
      x = Sskip \/ x = Scontinue ->
      clight_corestep (CL_State f x (Kloop1 s1 s2 k) e le) m
        (CL_State f s2 (Kloop2 s1 s2 k) e le) m
  | clight_corestep_break_loop1:  forall f s1 s2 k e le m,
      clight_corestep (CL_State f Sbreak (Kloop1 s1 s2 k) e le) m
        (CL_State f Sskip k e le) m
  | clight_corestep_skip_loop2: forall f s1 s2 k e le m,
      clight_corestep (CL_State f Sskip (Kloop2 s1 s2 k) e le) m
        (CL_State f (Sloop s1 s2) k e le) m
  | clight_corestep_break_loop2: forall f s1 s2 k e le m,
      clight_corestep (CL_State f Sbreak (Kloop2 s1 s2 k) e le) m
        (CL_State f Sskip k e le) m

  | clight_corestep_return_0: forall f k e le m m',
      Mem.free_list m (blocks_of_env ge e) = Some m' ->
      clight_corestep (CL_State f (Sreturn None) k e le) m
        (CL_Returnstate Vundef (call_cont k)) m'

  | clight_corestep_return_1: forall f a k e le m v v' m',
      eval_expr ge e le m a v ->
      sem_cast v (typeof a) f.(fn_return) m = Some v' ->
      Mem.free_list m (blocks_of_env ge e) = Some m' ->
      clight_corestep (CL_State f (Sreturn (Some a)) k e le) m
        (CL_Returnstate v' (call_cont k)) m'

  | clight_corestep_skip_call: forall f k e le m m',
      is_call_cont k ->
      Mem.free_list m (blocks_of_env ge e) = Some m' ->
      clight_corestep (CL_State f Sskip k e le) m
        (CL_Returnstate Vundef k) m'

  | clight_corestep_switch: forall f a sl k e le m v n,
      eval_expr ge e le m a v ->
      sem_switch_arg v (typeof a) = Some n ->
      clight_corestep (CL_State f (Sswitch a sl) k e le) m
        (CL_State f (seq_of_labeled_statement (select_switch n sl)) (Kswitch k) e le) m

  | clight_corestep_skip_break_switch: forall f x k e le m,
      x = Sskip \/ x = Sbreak ->
      clight_corestep (CL_State f x (Kswitch k) e le) m
        (CL_State f Sskip k e le) m
  | clight_corestep_continue_switch: forall f k e le m,
      clight_corestep (CL_State f Scontinue (Kswitch k) e le) m
        (CL_State f Scontinue k e le) m

  | clight_corestep_label: forall f lbl s k e le m,
      clight_corestep (CL_State f (Slabel lbl s) k e le) m
        (CL_State f s k e le) m

  | clight_corestep_goto: forall f lbl k e le m s' k',
      find_label lbl f.(fn_body) (call_cont k) = Some (s', k') ->
      clight_corestep (CL_State f (Sgoto lbl) k e le) m
        (CL_State f s' k' e le) m

  | clight_corestep_internal_function: forall f vargs k m e le m',
      function_entry f vargs m e le m' ->
      clight_corestep (CL_Callstate (Internal f) vargs k) m
        (CL_State f f.(fn_body) k e le) m'

  | clight_corestep_returnstate: forall v optid f e le k m,
      clight_corestep (CL_Returnstate v (Kcall optid f e le k)) m
        (CL_State f Sskip k e (set_opttemp optid v le)) m.

Lemma CL_corestep_not_at_external:
       forall m q m' q', clight_corestep q m q' m' -> CL_at_external q = None.
  Proof. intros. inv H; reflexivity. Qed.

Lemma CL_corestep_not_halted : forall m q m' q',
       clight_corestep q m q' m' -> CL_halted q = None.
  Proof. intros. inv H; reflexivity. Qed.

Lemma CL_at_external_halted_excl :
       forall q, CL_at_external q = None \/ CL_halted q = None.
   Proof. intros. destruct q; auto. Qed.

Definition CL_initial_core (v: val) (args:list val): option CL_core :=
   match v with
     | Vptr b i =>
          if Int.eq_dec i Int.zero
          then match Genv.find_funct_ptr ge b with
                 | None => None
                 | Some f =>
                    match f with Internal fi =>
                      match type_of_fundef f with
                        | Tfunction targs tres cconv =>
                            if val_casted_list_func args targs
                               && tys_nonvoid targs
                               && vals_defined args
                               && zlt (4*(2*(Zlength args))) Int.max_unsigned
                            then Some (CL_Callstate f args Kstop)
                            else None
                        | _ => None
                      end
                    | External _ _ _ _ => None
                    end
               end
          else None
     | _ => None
    end.

End SEMANTICS.

Definition CL_core_sem (FE:function -> list val -> mem -> env -> temp_env -> mem -> Prop)
         : CoreSemantics genv CL_core mem.
Proof.
  eapply (@Build_CoreSemantics _ _ _
      CL_initial_core CL_at_external CL_after_external
       CL_halted (clight_corestep FE)).
    apply CL_corestep_not_at_external.
    apply CL_corestep_not_halted.
    apply CL_at_external_halted_excl.
Defined.

Lemma ple_valid_pointer m b z (VP:Mem.valid_pointer m b z = true) m1
      (PLE : perm_lesseq m m1): Mem.valid_pointer m1 b z = true.
Proof.
  apply Mem.valid_pointer_nonempty_perm. apply Mem.valid_pointer_nonempty_perm in VP.
    unfold Mem.perm in *.
    destruct PLE. specialize (perm_le_Cur b z).
    destruct ((Mem.mem_access m) !! b z Cur); simpl in *; try contradiction.
    - destruct ((Mem.mem_access m1) !! b z Cur); simpl in *; try contradiction. eapply perm_order_trans; eassumption.
Qed.

Lemma ple_weak_valid_pointer m b i (VP:Mem.weak_valid_pointer m b (Int.unsigned i) = true) m1
      (PLE : perm_lesseq m m1): Mem.weak_valid_pointer m1 b (Int.unsigned i) = true.
Proof. apply Mem.weak_valid_pointer_spec in VP.
  apply Mem.weak_valid_pointer_spec.
  destruct VP.
  + left. eapply ple_valid_pointer; eassumption.
  + right. eapply ple_valid_pointer; eassumption.
Qed.

Lemma ple_unop op v1 t m v (SUO: sem_unary_operation op v1 t m = Some v) m1
      (PLE : perm_lesseq m m1): sem_unary_operation op v1 t m1 = Some v.
Proof.
destruct op; simpl in *.
+ unfold sem_notbool in *. destruct (classify_bool t); try discriminate.
  - destruct v1; inv SUO; trivial.
  - destruct v1; inv SUO; trivial.
  - destruct v1; inv SUO; trivial.
  - destruct v1; inv SUO; trivial.
    remember (Mem.weak_valid_pointer m b (Int.unsigned i)) as d.
    destruct d; inv H0. symmetry in Heqd.
    rewrite (ple_weak_valid_pointer _ _ _ Heqd _ PLE). trivial.
  - destruct v1; inv SUO; trivial.
+ unfold sem_notint in *. destruct (classify_notint t); try discriminate.
  - destruct v1; inv SUO; trivial.
  - destruct v1; inv SUO; trivial.
+ unfold sem_neg in *. destruct (classify_neg t); try discriminate.
  - destruct v1; inv SUO; trivial.
  - destruct v1; inv SUO; trivial.
  - destruct v1; inv SUO; trivial.
  - destruct v1; inv SUO; trivial.
+ unfold sem_absfloat in *. destruct (classify_neg t); try discriminate.
  - destruct v1; inv SUO; trivial.
  - destruct v1; inv SUO; trivial.
  - destruct v1; inv SUO; trivial.
  - destruct v1; inv SUO; trivial.
Qed.

Lemma ple_cast v0 v1 t1 t2 m:
      Some v0 = sem_cast v1 t1 t2 m -> forall mm, perm_lesseq m mm ->
      Some v0 = sem_cast v1 t1 t2 mm.
Proof. intros. unfold sem_cast in *.
destruct (classify_cast t1 t2); try solve [destruct v1; try discriminate; trivial].
destruct v1; try discriminate; trivial.
remember (Mem.weak_valid_pointer m b (Int.unsigned i)) as p.
destruct p; try discriminate. symmetry in Heqp.
erewrite ple_weak_valid_pointer; trivial; eassumption.
Qed.

Lemma ple_sem_binarith si sl sf ss v1 t1 v2 t2 m v
  (SB: sem_binarith si sl sf ss v1 t1 v2 t2 m = Some v)
  mm (PLE: perm_lesseq m mm):
  sem_binarith si sl sf ss v1 t1 v2 t2 mm = Some v.
Proof.
  unfold sem_binarith in *.
  remember (sem_cast v1 t1 (binarith_type (classify_binarith t1 t2)) m) as cast1.
  destruct cast1; try discriminate.
  remember (sem_cast v2 t2 (binarith_type (classify_binarith t1 t2)) m) as cast2.   destruct cast2; try discriminate.
  rewrite <- (ple_cast _ _ _ _ _ Heqcast1 _ PLE).
  rewrite <- (ple_cast _ _ _ _ _ Heqcast2 _ PLE); trivial.
Qed.

Lemma ple_sem_cmp op v1 t1 v2 t2 m v (CMP: sem_cmp op v1 t1 v2 t2 m = Some v) m1 (PLE : perm_lesseq m m1):
      sem_cmp op v1 t1 v2 t2 m1 = Some v.
Proof. unfold sem_cmp in *. destruct (classify_cmp t1 t2); try discriminate.
  - destruct v1; destruct v2; inv CMP; simpl; trivial.
    destruct (Int.eq i Int.zero); simpl in *; trivial.
    remember (Mem.valid_pointer m b (Int.unsigned i0)) as q; destruct q; simpl in *; trivial; inv H0.
    * symmetry in Heqq. rewrite (ple_valid_pointer _ _ _ Heqq _ PLE); simpl; trivial.
    * remember (Mem.valid_pointer m b (Int.unsigned i0 - 1)) as w. destruct w; simpl in *; trivial; inv H1.
      symmetry in Heqw. rewrite (ple_valid_pointer _ _ _ Heqw _ PLE); simpl; trivial.
         rewrite orb_true_r. reflexivity.
    * destruct (Int.eq i0 Int.zero); simpl in *; trivial.
      remember (Mem.valid_pointer m b (Int.unsigned i)) as q; destruct q; simpl in *; trivial; inv H0.
      ++ symmetry in Heqq. rewrite (ple_valid_pointer _ _ _ Heqq _ PLE); simpl; trivial.
      ++ remember (Mem.valid_pointer m b (Int.unsigned i - 1)) as w. destruct w; simpl in *; trivial; inv H1.
         symmetry in Heqw. rewrite (ple_valid_pointer _ _ _ Heqw _ PLE); simpl; trivial.
         rewrite orb_true_r. reflexivity.
    * destruct (eq_block b b0); subst; simpl in *; trivial.
      remember (Mem.valid_pointer m b0 (Int.unsigned i)) as q; destruct q; simpl in *.
      ++ symmetry in Heqq. rewrite (ple_valid_pointer _ _ _ Heqq _ PLE); simpl.
         remember (Mem.valid_pointer m b0 (Int.unsigned i0)) as w. destruct w; simpl in *.
         -- symmetry in Heqw. rewrite (ple_valid_pointer _ _ _ Heqw _ PLE); simpl. reflexivity.
         -- remember (Mem.valid_pointer m b0 (Int.unsigned i0 - 1)) as r. destruct r; simpl in *; inv H0.
            symmetry in Heqr. rewrite (ple_valid_pointer _ _ _ Heqr _ PLE); simpl. rewrite orb_true_r. reflexivity.
      ++ remember (Mem.valid_pointer m b0 (Int.unsigned i - 1)) as w. destruct w; simpl in *; trivial; inv H0.
         symmetry in Heqw. rewrite (ple_valid_pointer _ _ _ Heqw _ PLE); simpl; trivial.
         rewrite orb_true_r. simpl.
         remember (Mem.valid_pointer m b0 (Int.unsigned i0)) as p. destruct p; simpl in *.
         -- symmetry in Heqp. rewrite (ple_valid_pointer _ _ _ Heqp _ PLE); simpl. reflexivity.
         -- remember (Mem.valid_pointer m b0 (Int.unsigned i0 - 1)) as r. destruct r; simpl in *; inv H1.
            symmetry in Heqr. rewrite (ple_valid_pointer _ _ _ Heqr _ PLE); simpl. rewrite orb_true_r. reflexivity.
     ++ remember (Mem.valid_pointer m b (Int.unsigned i) ) as q. destruct q; inv H0; simpl in *.
        symmetry in Heqq. rewrite (ple_valid_pointer _ _ _ Heqq _ PLE); simpl.
        remember (Mem.valid_pointer m b0 (Int.unsigned i0)) as w. destruct w; inv H1.
        symmetry in Heqw. rewrite (ple_valid_pointer _ _ _ Heqw _ PLE); simpl; trivial.
  - destruct v2; inv CMP; trivial. destruct v1; simpl in *; inv H0; trivial.
    destruct (Int.eq (Int.repr (Int64.unsigned i)) Int.zero); simpl in *; inv H1.
    remember (Mem.valid_pointer m b (Int.unsigned i0)) as q. destruct q; simpl in *; inv H0.
    symmetry in Heqq. rewrite (ple_valid_pointer _ _ _ Heqq _ PLE); simpl; trivial.
    remember (Mem.valid_pointer m b (Int.unsigned i0 - 1)) as r. destruct r; inv H1.
    symmetry in Heqr. rewrite (ple_valid_pointer _ _ _ Heqr _ PLE), orb_true_r; simpl; trivial.
  - destruct v1; inv CMP. destruct v2; simpl in *; inv H0; trivial.
    destruct (Int.eq (Int.repr (Int64.unsigned i)) Int.zero); simpl in *; inv H1.
    remember (Mem.valid_pointer m b (Int.unsigned i0)) as q. destruct q; simpl in *; inv H0.
    symmetry in Heqq. rewrite (ple_valid_pointer _ _ _ Heqq _ PLE); simpl; trivial.
    remember (Mem.valid_pointer m b (Int.unsigned i0 - 1)) as r. destruct r; inv H1.
    symmetry in Heqr. rewrite (ple_valid_pointer _ _ _ Heqr _ PLE), orb_true_r; simpl; trivial.
  - eapply ple_sem_binarith; eassumption.
Qed.

Lemma ple_binop g op v1 t1 v2 t2 m v (SBO: sem_binary_operation g op v1 t1 v2 t2 m = Some v)
      m1 (PLE : perm_lesseq m m1): sem_binary_operation g op v1 t1 v2 t2 m1 = Some v.
Proof. destruct op; simpl in *; trivial.
+ unfold sem_add in *. destruct (classify_add t1 t2); trivial.
  eapply ple_sem_binarith; eassumption.
+ unfold sem_sub in *. destruct (classify_sub t1 t2); trivial.
  eapply ple_sem_binarith; eassumption.
+ unfold sem_mul in *.
  eapply ple_sem_binarith; eassumption.
+ unfold sem_div in *.
  eapply ple_sem_binarith; eassumption.
+ unfold sem_mod in *.
  eapply ple_sem_binarith; eassumption.
+ unfold sem_and in *.
  eapply ple_sem_binarith; eassumption.
+ unfold sem_or in *.
  eapply ple_sem_binarith; eassumption.
+ unfold sem_xor in *.
  eapply ple_sem_binarith; eassumption.
+ eapply ple_sem_cmp; eassumption.
+ eapply ple_sem_cmp; eassumption.
+ eapply ple_sem_cmp; eassumption.
+ eapply ple_sem_cmp; eassumption.
+ eapply ple_sem_cmp; eassumption.
+ eapply ple_sem_cmp; eassumption.
Qed.

Lemma ple_deref_loc t m loc ofs v (D:deref_loc t m loc ofs v) m1 (PLE : perm_lesseq m m1):
      deref_loc t m1 loc ofs v.
Proof.
inv D.
+ eapply deref_loc_value. eassumption. eapply ple_load; eassumption.
+ apply deref_loc_reference; trivial.
+ apply deref_loc_copy; trivial.
Qed.

Lemma ple_eval_evallvalue g e le m:
     (forall (a : expr) (v : val), eval_expr g e le m a v ->
         (forall m1 (PLE:perm_lesseq m m1), eval_expr g e le m1 a v)) /\
     (forall (a : expr) (b : block) (i : int), eval_lvalue g e le m a b i ->
         (forall m1 (PLE:perm_lesseq m m1), eval_lvalue g e le m1 a b i)).
Proof.
apply eval_expr_lvalue_ind; simpl; intros; try solve [econstructor; eauto].
+ econstructor; eauto. eapply ple_unop; eassumption.
+ econstructor; eauto. eapply ple_binop; eassumption.
+ econstructor; eauto. symmetry. symmetry in H1.  eapply ple_cast; eassumption.
+ econstructor. eauto. eapply ple_deref_loc; eassumption.
Qed.

Lemma ple_eval_expr g e le m:
      forall a v (EE:eval_expr g e le m a v) mm
      (PLE : perm_lesseq m mm), eval_expr g e le mm a v.
Proof.
induction a; simpl; intros; inv EE; simpl; try solve [constructor; trivial]; try solve [inv H].
+ econstructor.
   eapply ple_eval_evallvalue; eassumption.
   eapply ple_deref_loc; eassumption.
+ econstructor.
   eapply ple_eval_evallvalue; eassumption.
   eapply ple_deref_loc; eassumption.
+ econstructor.
   eapply ple_eval_evallvalue; eassumption.
+ econstructor; eauto.
   eapply ple_unop; eassumption.
+ econstructor; eauto.
   eapply ple_binop; eassumption.
+ econstructor; eauto.
    symmetry. symmetry in H3. eapply ple_cast; eassumption.
+ econstructor.
   eapply ple_eval_evallvalue; eassumption.
   eapply ple_deref_loc; eassumption.
Qed.

Lemma ple_eval_exprlist g e le: forall al tyargs vargs m (EE:eval_exprlist g e le m al tyargs vargs) m1
      (PLE : perm_lesseq m m1), eval_exprlist g e le m1 al tyargs vargs.
Proof.
induction al; simpl; intros; inv EE.
+ constructor.
+ econstructor.
  eapply ple_eval_expr; eassumption.
  symmetry. symmetry in H2. eapply ple_cast; eassumption.
  eauto.
Qed.

Lemma ple_assign_loc g t loc ofs v m m' (A:assign_loc g t m loc ofs v m')
      m1 (PLE:perm_lesseq m m1): exists m1',  assign_loc g t m1 loc ofs v m1' /\ perm_lesseq m' m1'.
Proof.
inv A.
+ destruct (ple_store _ _ _ _ _ _ PLE H0) as [mm [PP MM]].
  exists mm; split; trivial. eapply assign_loc_value; eassumption.
+ destruct (ple_storebytes _ _ _ _ _ _ PLE H4) as [mm [ST MM]].
  exists mm; split; trivial.
  eapply assign_loc_copy; try eassumption.
  eapply ple_loadbytes; try eassumption. specialize (sizeof_pos g t). omega.
Qed.

Lemma clight_inc_perm
           (FE:function -> list val -> mem -> env -> temp_env -> mem -> Prop)
           (HFE_ple: forall f vargs m e le m', FE f vargs m e le m'->
                forall m1 (PLE:perm_lesseq m m1), exists m1':mem,  FE f vargs m1 e le m1' /\ perm_lesseq m' m1'):
       forall (g : genv) c m c' m' (CS:corestep (CL_core_sem FE) g c m c' m')
       m1 (PLE:perm_lesseq m m1), exists m1', corestep (CL_core_sem FE) g c m1 c' m1' /\ perm_lesseq m' m1'.
Proof.
 intros; inv CS; try contradiction;
 try solve [exists m1; split; trivial; econstructor; try eassumption].
+ destruct (ple_assign_loc _ _ _ _ _ _ _ H2 _ PLE) as [mm [AA MM]].
  exists mm. split; trivial.
  econstructor; try eassumption.
   eapply ple_eval_evallvalue; eassumption.
   eapply ple_eval_evallvalue; eassumption.
   symmetry. symmetry in H1. eapply ple_cast; eassumption.
+ exists m1; split; trivial. econstructor. eapply ple_eval_evallvalue; eassumption.
+ exists m1; split; trivial. econstructor; try eassumption.  eapply ple_eval_evallvalue; eassumption. eapply ple_eval_exprlist; eassumption.
+ exists m1; split; trivial. econstructor; try eassumption. eapply ple_eval_evallvalue; eassumption.
   unfold bool_val in *. destruct (classify_bool (typeof a)); inv H0.
   destruct v1; simpl in *; inv H2; trivial.
   destruct v1; simpl in *; inv H2; trivial.
   destruct v1; simpl in *; inv H2; trivial.
   destruct v1; simpl in *; inv H2; trivial.
   remember (Mem.weak_valid_pointer m' b0 (Int.unsigned i) ) as q. destruct q; inv H1.
   symmetry in Heqq. rewrite (ple_weak_valid_pointer _ _ _ Heqq _ PLE); trivial.
   destruct v1; simpl in *; inv H2; trivial.
+ exploit ple_freelist; try eassumption.
  intros [mm [MMF MM]].
  eexists mm; split; trivial. econstructor; eassumption.
+ exploit ple_freelist; try eassumption.
  intros [mm [MMF MM]].
  eexists mm; split; trivial. econstructor; try eassumption. eapply ple_eval_evallvalue; eassumption.
  symmetry. symmetry in H0. eapply ple_cast; eassumption.
+ exploit ple_freelist; try eassumption.
  intros [mm [MMF MM]].
  eexists mm; split; trivial. econstructor; try eassumption.
+ exists m1; split; trivial. econstructor; try eassumption. eapply ple_eval_evallvalue; eassumption.
+ destruct (HFE_ple _ _ _ _ _ _ H _ PLE) as [mm [FEM MM]].
  exists mm; split; trivial. econstructor; trivial.
Qed.

Definition CL_memsem
           (FE:function -> list val -> mem -> env -> temp_env -> mem -> Prop)
           (HFE_mem: forall f vargs m e le m', FE f vargs m e le m'-> mem_step m m')
           (HFE_ple: forall f vargs m e le m', FE f vargs m e le m'->
                forall m1 (PLE:perm_lesseq m m1), exists m1',  FE f vargs m1 e le m1' /\ perm_lesseq m' m1')
           : @MemSem genv CL_core.
Proof.
eapply Build_MemSem with (csem := @CL_core_sem FE).
  intros.
  destruct CS; try apply mem_step_refl.
  + destruct H2.
    - simpl in H3.
      eapply mem_step_storebytes.
      apply Mem.store_storebytes; eassumption.
    - eapply mem_step_storebytes; eassumption.
(*  + eapply extcall_mem_step; eassumption.*)
  + eapply mem_step_freelist; eassumption.
  + eapply mem_step_freelist; eassumption.
  + eapply mem_step_freelist; eassumption.
  + eauto.
Defined.

Lemma alloc_variables_mem_step: forall ge vars m e e2 m'
      (M: alloc_variables ge e m vars e2 m'), mem_step m m'.
Proof. intros.
  induction M.
  apply mem_step_refl.
  eapply mem_step_trans.
    eapply mem_step_alloc; eassumption. eassumption.
Qed.

Lemma bind_parameters_mem_step: forall ge e m pars vargs m'
      (M: bind_parameters ge e m pars vargs m'), mem_step m m'.
Proof. intros.
  induction M.
  apply mem_step_refl.
  inv H0.
+ eapply mem_step_trans; try eassumption. simpl in H2.
  eapply mem_step_store; eassumption.
+ eapply mem_step_trans; try eassumption.
  eapply mem_step_storebytes; eassumption.
Qed.

Lemma function_entry1_mem_step: forall g f vargs m e le m',
      function_entry1 g f vargs m e le m'-> mem_step m m'.
Proof. intros. inv H.
  eapply mem_step_trans.
  eapply alloc_variables_mem_step; try eassumption.
  eapply bind_parameters_mem_step; eassumption.
Qed.

Lemma function_entry2_mem_step: forall g f vargs m e le m',
      function_entry2 g f vargs m e le m'-> mem_step m m'.
Proof. intros. inv H.
    eapply alloc_variables_mem_step; try eassumption.
Qed.

Lemma alloc_variables_inc_perm: forall ge vars m e e2 m'
      (M: alloc_variables ge e m vars e2 m') m1 (PLE: perm_lesseq m m1),
      exists m1' : mem, alloc_variables ge e m1 vars e2 m1' /\ perm_lesseq m' m1'.
Proof. intros until m'.
  induction 1; simpl; intros.
  exists m1; split; trivial. constructor.
  destruct (alloc_inc_perm _ _ _ _ _ H _ PLE) as [m1' [X2 M2]].
  destruct (IHM _ M2) as [mm [? ?]].
  exists mm; split; simpl; trivial. econstructor; eassumption.
Qed.

Lemma bind_parameters_inc_perm: forall ge e m pars vargs m'
      (M: bind_parameters ge e m pars vargs m') m1 (PLE: perm_lesseq m m1),
      exists m1' : mem, bind_parameters ge e m1 pars vargs m1' /\ perm_lesseq m' m1'.
Proof. intros until m'.
  induction 1; simpl; intros.
  + exists m1; split; trivial. constructor.
  + destruct (ple_assign_loc _ _ _ _ _ _ _ H0 _ PLE) as [m1' [ALL M1]].
    destruct (IHM _ M1) as [m2' [BP PLE2]].
    exists m2'; split; trivial. econstructor; eassumption.
Qed.

Lemma function_entry1_inc_perm: forall g f vargs m e le m',
      function_entry1 g f vargs m e le m' ->
        forall m1 : mem, perm_lesseq m m1 ->
      exists m1' : mem, function_entry1 g f vargs m1 e le m1' /\ perm_lesseq m' m1'.
Proof.
  intros. inv H.
  destruct (alloc_variables_inc_perm _ _ _ _ _ _ H2 _ H0) as [m1' [? ?]].
  destruct (bind_parameters_inc_perm _ _ _ _ _ _ H3 _ H4) as [m2' [? ?]].
  exists m2'; split; trivial. econstructor; try eassumption. trivial.
Qed.

Lemma function_entry2_inc_perm: forall g f vargs m e le m',
      function_entry2 g f vargs m e le m' ->
        forall m1 : mem, perm_lesseq m m1 ->
      exists m1' : mem, function_entry2 g f vargs m1 e le m1' /\ perm_lesseq m' m1'.
Proof.
  intros. inv H.
  destruct (alloc_variables_inc_perm _ _ _ _ _ _ H4 _ H0) as [m1' [? ?]].
  exists m1'; split; trivial. econstructor; try eassumption.
Qed.


Definition CL_memsem1 g := CL_memsem _ (function_entry1_mem_step g) (function_entry1_inc_perm g).
Definition CL_memsem2 g := CL_memsem _ (function_entry2_mem_step g) (function_entry2_inc_perm g).

Lemma alloc_variables_forward g vars m e e2 m'
      (M: alloc_variables g e m vars e2 m'): mem_forward m m'.
Proof.
  apply alloc_variables_mem_step in M.
  apply mem_forward_preserve in M. trivial.
Qed.

Lemma bind_parameter_forward g e m pars vargs m'
      (M: bind_parameters g e m pars vargs m'):
      mem_forward m m'.
Proof.
  apply bind_parameters_mem_step in M.
  apply mem_forward_preserve in M. trivial.
Qed.

(*
Lemma CL_forward :
  forall (FE: function -> list val -> mem -> env -> temp_env -> mem -> Prop)
         (HFE: forall f vargs m e le m', FE f vargs m e le m'-> mem_forward m m')
         g c m c' m' (CS: clight_corestep FE g c m c' m'),
                     mem_forward m m'.
  Proof. intros.
     inv CS; simpl in *; try apply mem_forward_refl.
         (*Storev*)
          inv H2.
          eapply store_forward. eassumption.
          eapply storebytes_forward. eassumption.
         (*builtin*)
          eapply external_call_mem_forward; eassumption.
         (*free*)
         eapply freelist_forward; eassumption.
         eapply freelist_forward; eassumption.
         eapply freelist_forward; eassumption.
       eapply HFE. apply H.
Qed.

Lemma alloc_variables_forward: forall vars m e e2 m'
      (M: alloc_variables e m vars e2 m'),
      mem_forward m m'.
Proof. intros.
  induction M.
  apply mem_forward_refl.
  apply alloc_forward in H.
  eapply mem_forward_trans; eassumption.
Qed.

Lemma bind_parameter_forward: forall e m pars vargs m'
      (M: bind_parameters e m pars vargs m'),
      mem_forward m m'.
Proof. intros.
  induction M.
  apply mem_forward_refl.
  eapply mem_forward_trans; try eassumption.
  inv H0.
  eapply store_forward. eassumption.
  eapply storebytes_forward. eassumption.
Qed.

Lemma CL_rdonly g
            (FE: function -> list val -> mem -> env -> temp_env -> mem -> Prop)
            (HFE: forall f vargs m e le m', FE f vargs m e le m' ->
                    forall b, Mem.valid_block m b -> readonly m b m')
             c m c' m'
            (CS: clight_corestep FE g c m c' m') b
            (VB: Mem.valid_block m b):
         readonly m b m'.
  Proof.
     inv CS; simpl in *; try apply readonly_refl.
          remember (typeof a1) as t; clear Heqt.
            inv H2. eapply store_readonly; eassumption.
                    eapply storebytes_readonly; eassumption.
          eapply ec_readonly_strong; eassumption.
          eapply freelist_readonly; eassumption.
          eapply freelist_readonly; eassumption.
          eapply freelist_readonly; eassumption.
          eapply HFE. eassumption. eassumption.
  Qed.


Definition CL_coop_sem
           (FE:function -> list val -> mem -> env -> temp_env -> mem -> Prop)
           (HFE: forall f vargs m e le m', FE f vargs m e le m'-> mem_forward m m')
           (HFE_rdo: forall f vargs m e le m', FE f vargs m e le m' ->
                     forall b, Mem.valid_block m b -> readonly m b m')
           : CoopCoreSem genv CL_core.
Proof.
apply Build_CoopCoreSem with (coopsem := CL_core_sem FE).
  apply CL_forward. apply HFE.
  intros. eapply CL_rdonly; eassumption.
Defined.

Lemma CL_decay g
            (FE: function -> list val -> mem -> env -> temp_env -> mem -> Prop)
            (HFE: forall f vargs m e le m', FE f vargs m e le m' -> decay m m')
             c m c' m'
            (CS: clight_corestep FE g c m c' m'):
         decay m m'.
  Proof.
     inv CS; simpl in *; try apply decay_refl.
          remember (typeof a1) as t; clear Heqt.
            inv H2. eapply store_decay; eassumption.
                    eapply storebytes_decay; eassumption.
          eapply ec_decay; eassumption.
          eapply freelist_decay; eassumption.
          eapply freelist_decay; eassumption.
          eapply freelist_decay; eassumption.
          eauto.
  Qed.

Definition CL_decay_sem
           (FE:function -> list val -> mem -> env -> temp_env -> mem -> Prop)
           (HFE_fwd: forall f vargs m e le m', FE f vargs m e le m'-> mem_forward m m')
           (HFE_rdo: forall f vargs m e le m', FE f vargs m e le m' ->
                     forall b, Mem.valid_block m b -> readonly m b m')
           (HFE_dec: forall f vargs m e le m', FE f vargs m e le m'-> decay m m')
           : @DecayCoreSem genv CL_core.
Proof.
eapply Build_DecayCoreSem with (decaysem := @CL_coop_sem FE HFE_fwd HFE_rdo).
  intros. eapply CL_decay; eassumption.
Defined.

(** The two semantics for function parameters.  First, parameters as local variables. *)

Inductive function_entry1 (f: function) (vargs: list val) (m: mem) (e: env) (le: temp_env) (m': mem) : Prop :=
  | function_entry1_intro: forall m1,
      list_norepet (var_names f.(fn_params) ++ var_names f.(fn_vars)) ->
      alloc_variables empty_env m (f.(fn_params) ++ f.(fn_vars)) e m1 ->
      bind_parameters e m1 f.(fn_params) vargs m' ->
      le = create_undef_temps f.(fn_temps) ->
      function_entry1 f vargs m e le m'.

Lemma function_entry1_forward: forall f vargs m e le m',
      function_entry1 f vargs m e le m'-> mem_forward m m'.
Proof. intros. inv H.
  eapply mem_forward_trans.
    eapply alloc_variables_forward; try eassumption.
    eapply bind_parameter_forward; eassumption.
Qed.

Lemma alloc_variables_readonly: forall vars m e e2 m'
      (M: alloc_variables e m vars e2 m') b (VB: Mem.valid_block m b),
      readonly m b m'.
Proof. intros.
  induction M.
  apply readonly_refl.
  eapply readonly_trans.
     eapply alloc_readonly; try eassumption.
     apply IHM. eapply alloc_forward; eassumption.
Qed.

Lemma bind_parameter_readonly: forall e m pars vargs m'
      (M: bind_parameters e m pars vargs m') b (VB: Mem.valid_block m b),
      readonly m b m'.
Proof. intros.
  induction M.
  apply readonly_refl.
  eapply readonly_trans; try eassumption.
  inv H0.
  eapply store_readonly; eassumption.
  eapply storebytes_readonly; eassumption.
     apply IHM. inv H0. eapply store_forward; eassumption.
                        eapply storebytes_forward; eassumption.
Qed.

Lemma function_entry1_readonly: forall f vargs m e le m',
      function_entry1 f vargs m e le m'-> forall b,
      Mem.valid_block m b -> readonly m b m'.
Proof. intros. inv H.
  eapply readonly_trans.
    eapply alloc_variables_readonly; try eassumption.
    eapply bind_parameter_readonly; try eassumption.
      eapply alloc_variables_forward; try eassumption.
Qed.


Lemma alloc_variables_decay: forall vars m e e2 m'
      (M: alloc_variables e m vars e2 m'), decay m m'.
Proof. intros.
  induction M.
  apply decay_refl.
  eapply decay_trans.
    eapply alloc_forward; eassumption.
    eapply alloc_decay; try eassumption.
    apply IHM.
Qed.

Lemma bind_parameter_decay: forall e m pars vargs m'
      (M: bind_parameters e m pars vargs m'), decay m m'.
Proof. intros.
  induction M.
  apply decay_refl.
  inv H0.
+ eapply decay_trans; try eassumption.
  eapply store_forward; eassumption.
  eapply store_decay; eassumption.
+ eapply decay_trans; try eassumption.
  eapply storebytes_forward; eassumption.
  eapply storebytes_decay; eassumption.
Qed.

Lemma function_entry1_decay: forall f vargs m e le m',
      function_entry1 f vargs m e le m'-> decay m m'.
Proof. intros. inv H.
  eapply decay_trans.
    eapply alloc_variables_forward; try eassumption.
    eapply alloc_variables_decay; try eassumption.
    eapply bind_parameter_decay; try eassumption.
Qed.

(*Definition clight_corestep1 (ge: genv) := clight_corestep function_entry1 ge.*)

Definition CL_core_sem1 := CL_core_sem function_entry1.
Definition CL_coop_sem1 : CoopCoreSem genv CL_core.
  eapply (CL_coop_sem function_entry1).
  apply function_entry1_forward.
  apply function_entry1_readonly.
Defined.
Definition CL_decay_sem1 : @DecayCoreSem genv CL_core.
  eapply (CL_decay_sem function_entry1).
  apply function_entry1_forward.
  apply function_entry1_readonly.
  apply function_entry1_decay.
Defined.

Inductive function_entry2 (f: function) (vargs: list val) (m: mem) (e: env) (le: temp_env) (m': mem) : Prop :=
  | function_entry2_intro:
      list_norepet (var_names f.(fn_vars)) ->
      list_norepet (var_names f.(fn_params)) ->
      list_disjoint (var_names f.(fn_params)) (var_names f.(fn_temps)) ->
      alloc_variables empty_env m f.(fn_vars) e m' ->
      bind_parameter_temps f.(fn_params) vargs (create_undef_temps f.(fn_temps)) = Some le ->
      function_entry2 f vargs m e le m'.

Lemma function_entry2_forward: forall f vargs m e le m',
      function_entry2 f vargs m e le m'-> mem_forward m m'.
Proof. intros. inv H.
    eapply alloc_variables_forward; try eassumption.
Qed.

Lemma function_entry2_readonly: forall f vargs m e le m',
      function_entry2 f vargs m e le m' -> forall b,
      Mem.valid_block m b -> readonly m b m'.
Proof. intros. inv H.
  eapply alloc_variables_readonly; try eassumption.
Qed.

Lemma function_entry2_decay: forall f vargs m e le m',
      function_entry2 f vargs m e le m'-> decay m m'.
Proof. intros. inv H.
    eapply alloc_variables_decay; try eassumption.
Qed.

(*Definition clight_corestep2 (ge: genv) := clight_corestep function_entry2 ge.*)

Definition CL_core_sem2 := CL_core_sem function_entry2.
Definition CL_coop_sem2 : CoopCoreSem genv CL_core.
  eapply (CL_coop_sem function_entry2).
  apply function_entry2_forward.
  apply function_entry2_readonly.
Defined.

Definition CL_decay_sem2 : @DecayCoreSem genv CL_core.
  eapply (CL_decay_sem function_entry2).
  apply function_entry2_forward.
  apply function_entry2_readonly.
  apply function_entry2_decay.
Defined.

End CLIGHT_COOP.*)
End CLIGHT_MEM.
