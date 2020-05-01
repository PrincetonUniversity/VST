Require Import VST.sepcomp.semantics.
Require Import VST.veric.Clight_base.
Require Import VST.veric.Clight_lemmas.
Require compcert.common.Globalenvs.
Require Import compcert.common.Events.
Require Import compcert.cfrontend.Clight.

(*To prove memsem*)
Require Import VST.sepcomp.semantics_lemmas.
Require Import VST.sepcomp.mem_lemmas.
Require Import VST.sepcomp.event_semantics.

Definition ef_deterministic (ef: external_function) : bool :=
  match ef with
  | EF_external name sg => false
  | EF_builtin name sg => true
  | EF_runtime name sg => false
  | EF_vload chunk => false
  | EF_vstore chunk => false
  | EF_malloc => true
  | EF_free => true
  | EF_memcpy sz al => true
  | EF_annot kind text targs => true
  | EF_annot_val kind Text rg => true
  | EF_inline_asm text sg clob => false
  | EF_debug kind text targs => true
  end.

Axiom ef_deterministic_fun:
 forall ef,
  ef_deterministic ef = true ->
 forall  ge args m t1 t2 vres1 vres2 m1 m2,
  Events.external_call ef ge args m t1 vres1 m1 ->
  Events.external_call ef ge args m t2 vres2 m2 ->
  (vres1,t1,m1) = (vres2,t2,m2).

Axiom inline_external_call_mem_events:
   forall ef ge vargs m t vres m',
   ef_inline ef = true ->
   external_call ef ge vargs m t vres m' ->
   {trace | ev_elim m trace m'}.

Inductive state : Type :=
    State : function ->
            statement -> cont -> env -> temp_env -> state
  | Callstate : fundef -> list val -> cont -> state
  | Returnstate : val -> cont -> state.

Definition CC_core := state.

Definition CC_core_to_CC_state (c:state) (m:mem) : Clight.state :=
  match c with
     State f st k e te => Clight.State f st k e te m
  |  Callstate fd args k => Clight.Callstate fd args k m
  | Returnstate v k => Clight.Returnstate v k m
 end.

Definition CC_state_to_CC_core (c:Clight.state): state * mem :=
  match c with
     Clight.State f st k e te m => (State f st k e te, m)
  |  Clight.Callstate fd args k m => (Callstate fd args k, m)
  | Clight.Returnstate v k m => (Returnstate v k, m)
 end.

Lemma  CC_core_CC_state_1: forall c m,
   CC_state_to_CC_core  (CC_core_to_CC_state c m) = (c,m).
  Proof. intros. destruct c; auto. Qed.

Lemma  CC_core_CC_state_2: forall s c m,
   CC_state_to_CC_core  s = (c,m) -> s= CC_core_to_CC_state c m.
  Proof. intros. destruct s; simpl in *.
      destruct c; simpl in *; inv H; trivial.
      destruct c; simpl in *; inv H; trivial.
      destruct c; simpl in *; inv H; trivial.
  Qed.

Lemma  CC_core_CC_state_3: forall s c m,
   s= CC_core_to_CC_state c m -> CC_state_to_CC_core  s = (c,m).
  Proof. intros. subst. apply CC_core_CC_state_1. Qed.

Lemma  CC_core_CC_state_4: forall s, exists c, exists m, s =  CC_core_to_CC_state c m.
  Proof. intros. destruct s.
             exists (State f s k e le). exists m; reflexivity.
             exists (Callstate fd args k). exists m; reflexivity.
             exists (Returnstate res k). exists m; reflexivity.
  Qed.

Lemma CC_core_to_CC_state_inj: forall c m c' m',
     CC_core_to_CC_state c m = CC_core_to_CC_state c' m' -> (c',m')=(c,m).
  Proof. intros.
       apply  CC_core_CC_state_3 in H. rewrite  CC_core_CC_state_1 in H.  inv H. trivial.
  Qed.

Definition cl_halted (c: CC_core) : option val := 
  match c with
  | Returnstate v Kstop => Some v
  | _ => None
  end.

Definition empty_function : function := mkfunction Tvoid cc_default nil nil nil Sskip.

Fixpoint temp_bindings (i: positive) (vl: list val) :=
 match vl with
 | nil => PTree.empty val
 | v::vl' => PTree.set i v (temp_bindings (i+1)%positive vl')
 end.

Fixpoint params_of_types (i: positive) (l : list type) : list (ident * type) :=
  match l with
  | nil => nil
  | t :: l => (i, t) :: params_of_types (i+1)%positive l
  end.

Fixpoint typelist2list (tl: typelist) : list type :=
  match tl with
  | Tcons t r => t::typelist2list r
  | Tnil => nil
  end.

Definition params_of_fundef (f: fundef) : list type :=
  match f with
  | Internal {| fn_params := fn_params |} => map snd fn_params
  | External _ t _ _ => typelist2list t
  end.

Definition cl_initial_core (ge: genv) (v: val) (args: list val) : option CC_core :=
  match v with
    Vptr b i =>
    if Ptrofs.eq_dec i Ptrofs.zero then
      match Genv.find_funct_ptr ge b with
        Some f =>
        Some (Callstate f args Kstop)
      | _ => None end
    else None
  | _ => None
  end.

Definition stuck_signature : signature := mksignature nil AST.Tvoid cc_default.

(*
Definition ef_no_event (ef: external_function) : bool :=
  match ef with
  | EF_external name sg => false
  | EF_builtin name sg => false
  | EF_runtime name sg => false
  | EF_vload chunk => false
  | EF_vstore chunk => false
  | EF_malloc => true
  | EF_free => true
  | EF_memcpy sz al => true
  | EF_annot kind text targs => true
  | EF_annot_val kind Text rg => true
  | EF_inline_asm text sg clob => true
  | EF_debug kind text targs => true
  end.

Axiom no_event_sound:
  forall ef, ef_no_event ef = true ->
  forall ge args m t v m',
   external_call ef ge args m t v m' -> t=E0.
*)
Definition cl_at_external (c: CC_core) : option (external_function * list val) :=
  match c with
  | Callstate (External ef _ _ _) args _ => 
     if ef_inline ef then None else Some (ef, args)
  | _ => None
end.

Definition cl_after_external (vret: option val) (c: CC_core) : option CC_core :=
   match c with
   | Callstate (External ef _ _ _) _ k => 
        Some (Returnstate (match vret with Some v => v | _ => Vundef end) k)
   | _ => None
   end.

Inductive step: genv -> state -> mem -> state -> mem -> Prop :=

  | step_assign:   forall ge f a1 a2 k e le m loc ofs v2 v m',
      eval_lvalue ge e le m a1 loc ofs ->
      eval_expr ge e le m a2 v2 ->
      sem_cast v2 (typeof a2) (typeof a1) m = Some v ->
      assign_loc ge (typeof a1) m loc ofs v m' ->
      step ge (State f (Sassign a1 a2) k e le) m
                  (State f Sskip k e le) m'

  | step_set:   forall ge f id a k e le m v,
      eval_expr ge e le m a v ->
      step ge (State f (Sset id a) k e le) m
              (State f Sskip k e (PTree.set id v le)) m

  | step_call:   forall ge f optid a al k e le m tyargs tyres cconv vf vargs fd,
      classify_fun (typeof a) = fun_case_f tyargs tyres cconv ->
      eval_expr ge e le m a vf ->
      eval_exprlist ge e le m al tyargs vargs ->
      Genv.find_funct ge vf = Some fd ->
      type_of_fundef fd = Tfunction tyargs tyres cconv ->
      step ge (State f (Scall optid a al) k e le) m
                  (Callstate fd vargs (Kcall optid f e le k)) m

  | step_builtin:   forall ge f optid ef tyargs al k e le m vargs t vres m',
      ef_inline ef && ef_deterministic ef = true ->
      eval_exprlist ge e le m al tyargs vargs ->
      external_call ef ge vargs m t vres m' ->
      step ge (State f (Sbuiltin optid ef tyargs al) k e le) m
           (State f Sskip k e (set_opttemp optid vres le)) m'

  | step_seq:  forall ge f s1 s2 k e le m,
      step ge (State f (Ssequence s1 s2) k e le) m
                 (State f s1 (Kseq s2 k) e le) m

  | step_skip_seq: forall ge f s k e le m,
      step ge (State f Sskip (Kseq s k) e le) m
              (State f s k e le) m
  | step_continue_seq: forall ge f s k e le m,
      step ge (State f Scontinue (Kseq s k) e le) m
             (State f Scontinue k e le) m
  | step_break_seq: forall ge f s k e le m,
      step ge (State f Sbreak (Kseq s k) e le) m
            (State f Sbreak k e le) m

  | step_ifthenelse:  forall ge f a s1 s2 k e le m v1 b,
      eval_expr ge e le m a v1 ->
      bool_val v1 (typeof a) m = Some b ->
      step ge (State f (Sifthenelse a s1 s2) k e le) m
            (State f (if b then s1 else s2) k e le) m

  | step_loop: forall ge f s1 s2 k e le m,
      step ge (State f (Sloop s1 s2) k e le) m
            (State f s1 (Kloop1 s1 s2 k) e le) m
  | step_skip_or_continue_loop1:  forall ge f s1 s2 k e le m x,
      x = Sskip \/ x = Scontinue ->
      step ge (State f x (Kloop1 s1 s2 k) e le) m
            (State f s2 (Kloop2 s1 s2 k) e le) m
  | step_break_loop1:  forall ge f s1 s2 k e le m,
      step ge (State f Sbreak (Kloop1 s1 s2 k) e le) m
             (State f Sskip k e le) m
  | step_skip_loop2: forall ge f s1 s2 k e le m,
      step ge (State f Sskip (Kloop2 s1 s2 k) e le) m
             (State f (Sloop s1 s2) k e le) m
  | step_break_loop2: forall ge f s1 s2 k e le m,
      step ge (State f Sbreak (Kloop2 s1 s2 k) e le) m
            (State f Sskip k e le) m

  | step_return_0: forall ge f k e le m m',
      Mem.free_list m (blocks_of_env ge e) = Some m' ->
      step ge (State f (Sreturn None) k e le) m
            (Returnstate Vundef (call_cont k)) m'
  | step_return_1: forall ge f a k e le m v v' m',
      eval_expr ge e le m a v ->
      sem_cast v (typeof a) f.(fn_return) m = Some v' ->
      Mem.free_list m (blocks_of_env ge e) = Some m' ->
      step ge (State f (Sreturn (Some a)) k e le) m
           (Returnstate v' (call_cont k)) m'
  | step_skip_call: forall ge f k e le m m',
      is_call_cont k ->
      Mem.free_list m (blocks_of_env ge e) = Some m' ->
      step ge (State f Sskip k e le) m
              (Returnstate Vundef k) m'

  | step_switch: forall ge f a sl k e le m v n,
      eval_expr ge e le m a v ->
      sem_switch_arg v (typeof a) = Some n ->
      step ge (State f (Sswitch a sl) k e le) m
            (State f (seq_of_labeled_statement (select_switch n sl)) (Kswitch k) e le) m
  | step_skip_break_switch: forall ge f x k e le m,
      x = Sskip \/ x = Sbreak ->
      step ge (State f x (Kswitch k) e le) m
             (State f Sskip k e le) m
  | step_continue_switch: forall ge f k e le m,
      step ge (State f Scontinue (Kswitch k) e le) m
             (State f Scontinue k e le) m

  | step_label: forall ge f lbl s k e le m,
      step ge (State f (Slabel lbl s) k e le) m
             (State f s k e le) m

  | step_goto: forall ge f lbl k e le m s' k',
      find_label lbl f.(fn_body) (call_cont k) = Some (s', k') ->
      step ge (State f (Sgoto lbl) k e le) m
             (State f s' k' e le) m

  | step_internal_function: forall ge f vargs k m e le m1,
      function_entry2 ge f vargs m e le m1 ->
      step ge (Callstate (Internal f) vargs k) m
            (State f f.(fn_body) k e le) m1

  | step_external_function: forall (ge: genv) ef targs tres cconv vargs k m t vres m',
      ef_inline ef  && ef_deterministic ef = true ->
      external_call ef ge vargs m t vres m' ->
      step ge (Callstate (External ef targs tres cconv) vargs k) m
          (Returnstate vres k) m'

  | step_returnstate: forall ge v optid f e le k m,
      step ge (Returnstate v (Kcall optid f e le k)) m
           (State f Sskip k e (set_opttemp optid v le)) m.

Definition cl_step: genv -> CC_core -> mem -> CC_core -> mem -> Prop := step.

Lemma cl_step_equiv: forall ge (q: CC_core) (m: mem) q' m',
  cl_at_external q = None ->
  step ge q m q' m' -> exists t, Clight.step ge (Clight.function_entry2 ge) 
      (CC_core_to_CC_state q m) t (CC_core_to_CC_state q' m').
Proof.
intros.
rename H into Hat.
(*split; intro. *)
-
inv H0; 
repeat match goal with H: _ = CC_core_to_CC_state ?q _ |- _ => destruct q; inv H end;
try solve [do 2 econstructor; eassumption].
Qed.

Lemma cl_corestep_not_at_external:
  forall ge m q m' q', 
          cl_step ge q m q' m' -> cl_at_external q = None.
Proof.
 simpl; intros.
 inv H; try reflexivity; simpl.
rewrite andb_true_iff in H0. destruct H0.
 rewrite H; auto.
Qed.

Lemma cl_corestep_not_halted :
  forall ge m q m' q' (i: int), cl_step ge q m q' m' -> ~ cl_halted q <> None.
Proof.
  intros.
  intro. apply H0.
  inv H; simpl; auto.
Qed.

Lemma cl_after_at_external_excl :
  forall retv q q', cl_after_external retv q = Some q' -> cl_at_external q' = None.
Proof.
intros until q'; intros H.
unfold cl_after_external in H.
destruct q; inv H. destruct f; inv H1. reflexivity.
Qed.

Program Definition cl_core_sem (ge: genv) :
  @CoreSemantics CC_core mem :=
  @Build_CoreSemantics _ _
    (*deprecated cl_init_mem*)
    (fun _ m c m' v args => cl_initial_core ge v args = Some c(* /\ Mem.arg_well_formed args m /\ m' = m *))
    (fun c _ => cl_at_external c)
    (fun ret c _ => cl_after_external ret c)
    (fun c _ =>  cl_halted c <> None)
    (cl_step ge)
    (cl_corestep_not_halted ge)
    (cl_corestep_not_at_external ge).

(*Clight_core is also a memsem!*)
Lemma alloc_variables_mem_step: forall cenv vars m e e2 m'
      (M: alloc_variables cenv e m vars e2 m'), mem_step m m'.
Proof. intros.
  induction M.
  apply mem_step_refl.
  eapply mem_step_trans.
    eapply mem_step_alloc; eassumption. eassumption.
Qed.

Lemma CC_core_to_State_mem:
    forall f STEP k e le m c m',
    Clight.State f STEP k e le m = CC_core_to_CC_state c m' ->
    m = m'.
  Proof.
    intros;
      destruct c; inversion H; auto.
  Qed.

Lemma bind_parameters_mem_step: forall cenv e m pars vargs m'
      (M: bind_parameters cenv e m pars vargs m'), mem_step m m'.
Proof. intros.
  induction M.
  apply mem_step_refl.
  inv H0.
+ eapply mem_step_trans; try eassumption. simpl in H2.
  eapply mem_step_store; eassumption.
+ eapply mem_step_trans; try eassumption.
  eapply mem_step_storebytes; eassumption.
Qed.

Lemma ev_elim_mem_step:
 forall m t m', ev_elim m t m' -> mem_step m m'.
Proof.
intros.
revert m m' H; induction t as [|[?|?|?|?]]; intros; inv H; auto.
- apply mem_step_refl.
- destruct H0.
   apply mem_step_trans with x; auto.
   apply mem_step_storebytes in H; auto.
- destruct H0.
   apply mem_step_trans with x; auto.
   apply mem_step_alloc in H; auto.
- destruct H0.
   apply mem_step_trans with x; auto.
   apply mem_step_freelist in H; auto.
Qed.

Lemma inline_external_call_mem_step:
   forall ef ge vargs m t vres m',
   ef_inline ef = true ->
   external_call ef ge vargs m t vres m' ->
   mem_step m m'.
Proof.
intros.
destruct (inline_external_call_mem_events _ _ _ _ _ _ _ H H0) as [tr ?].
apply ev_elim_mem_step in e; auto.
Qed.


Program Definition CLC_memsem (ge: genv):
  @MemSem (*(Genv.t fundef type)*) CC_core.
apply Build_MemSem with (csem := cl_core_sem ge).
  intros.
  induction CS;
  try apply mem_step_refl;
  try solve [eapply mem_step_freelist; eassumption].
*
 inv H2.
 unfold Mem.storev in H4. apply Mem.store_storebytes in H4.
 eapply mem_step_storebytes; eauto.
 eapply mem_step_storebytes; eauto.
*
 rewrite andb_true_iff in H; destruct H.
 eapply inline_external_call_mem_step; eauto.
*
  inv H.
  clear - H3.
  induction H3. apply mem_step_refl.
 eapply mem_step_trans. eapply mem_step_alloc; eassumption. auto.
*
 rewrite andb_true_iff in H; destruct H.
 eapply inline_external_call_mem_step; eauto.
Qed.

Definition at_external c := cl_at_external (fst (CC_state_to_CC_core c)). (* Temporary definition for compatibility between CompCert 3.3 and new-compcert *)
