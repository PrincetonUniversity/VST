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


Require Import Clight.
Require Import sepcomp.mem_lemmas. (*for mem_forward*)
Require Import sepcomp.core_semantics.

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
  | CL_Callstate fd args k => match fd with
                                  Internal f => None
                                | External ef targs tres => Some (ef, ef_sig ef, args)
                              end
  | CL_Returnstate v k => None
 end.

Definition CL_after_external (rv: option val) (c: CL_core) : option CL_core :=
  match c with
     CL_Callstate fd vargs k =>
        match fd with
          Internal _ => None
        | External ef tps tp =>
            match rv with
              Some v => Some(CL_Returnstate v k)
            | None  => Some(CL_Returnstate Vundef k)
            end
        end
   | _ => None
  end.
(*Previously we had this: but afterEtxernal clause in ChmgenproofEFF (MATCH)
  requires to have Returnstates
Definition CL_after_external (rv: option val) (c: CL_core) : option CL_core :=
  match c with
     CL_Callstate fd vargs (Clight.Kcall optid f e lenv k) =>
        match fd with
          Internal _ => None
        | External ef tps tp =>
            match rv, optid with
              Some v, _ => Some(CL_State f Sskip k e (set_opttemp optid v lenv))
            |   None, None    => Some(CL_State f Sskip k e lenv)
            | _ , _ => None
            end
        end
   | _ => None
  end.
*)
(*
Definition CL_after_external (vret: option val) (c: CL_core) : option CL_core :=
  match c with
    CL_Callstate fd args k =>
         match fd with
            Internal f => None
          | External ef targs tres => match vret with
                             None => Some (CL_Returnstate Vundef k)
                           | Some v => Some (CL_Returnstate v k)
                           end
         end
  | _ => None
  end.
*)
Definition CL_halted (q : CL_core): option val :=
    match q with
       CL_Returnstate v Kstop => Some v
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
      sem_cast v2 (typeof a2) (typeof a1) = Some v ->
      assign_loc (typeof a1) m loc ofs v m' ->
      clight_corestep (CL_State f (Sassign a1 a2) k e le) m
        (CL_State f Sskip k e le) m'

  | clight_corestep_set:   forall f id a k e le m v,
      eval_expr ge e le m a v ->
      clight_corestep (CL_State f (Sset id a) k e le) m
        (CL_State f Sskip k e (PTree.set id v le)) m

  | clight_corestep_call:   forall f optid a al k e le m tyargs tyres vf vargs fd,
      classify_fun (typeof a) = fun_case_f tyargs tyres ->
      eval_expr ge e le m a vf ->
      eval_exprlist ge e le m al tyargs vargs ->
      Genv.find_funct ge vf = Some fd ->
      type_of_fundef fd = Tfunction tyargs tyres ->
      clight_corestep (CL_State f (Scall optid a al) k e le) m
        (CL_Callstate fd vargs (Kcall optid f e le k)) m

(* WE DO NOT TREAT BUILTINS
  | clight_corestep_builtin:   forall f optid ef tyargs al k e le m vargs t vres m',
      eval_exprlist ge e le m al tyargs vargs ->
      external_call ef ge vargs m t vres m' ->
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
      bool_val v1 (typeof a) = Some b ->
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
      Mem.free_list m (blocks_of_env e) = Some m' ->
      clight_corestep (CL_State f (Sreturn None) k e le) m
        (CL_Returnstate Vundef (call_cont k)) m'
  | clight_corestep_return_1: forall f a k e le m v v' m',
      eval_expr ge e le m a v ->
      sem_cast v (typeof a) f.(fn_return) = Some v' ->
      Mem.free_list m (blocks_of_env e) = Some m' ->
      clight_corestep (CL_State f (Sreturn (Some a)) k e le) m
        (CL_Returnstate v' (call_cont k)) m'
  | clight_corestep_skip_call: forall f k e le m m',
      is_call_cont k ->
      Mem.free_list m (blocks_of_env e) = Some m' ->
      clight_corestep (CL_State f Sskip k e le) m
        (CL_Returnstate Vundef k) m'

  | clight_corestep_switch: forall f a sl k e le m n,
      eval_expr ge e le m a (Vint n) ->
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
(*no external step
  | step_external_function: forall ef targs tres vargs k m vres t m',
      external_call ef ge vargs m t vres m' ->
      clight_corestep (CL_Callstate (External ef targs tres) vargs k) m
         (CL_Returnstate vres k) m'
*)

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

Lemma CL_after_at_external_excl : forall retv q q',
      CL_after_external retv q = Some q' -> CL_at_external q' = None.
  Proof. intros.
       destruct q; simpl in *; try inv H.
       destruct fd; inv H1.
       destruct retv; inv H0; simpl; trivial.
(*       destruct o; inv H0; simpl; trivial.*)
Qed.

Definition CL_initial_core (v: val) (args:list val): option CL_core :=
   match v with
     | Vptr b i =>
          if Int.eq_dec i Int.zero
          then match Genv.find_funct_ptr ge b with
                 | None => None
                 | Some f => Some (CL_Callstate f args Kstop)
               end
          else None
     | _ => None
    end.
End SEMANTICS.

Definition CL_core_sem (FE:function -> list val -> mem -> env -> temp_env -> mem -> Prop)
         : CoreSemantics genv CL_core mem.
  eapply @Build_CoreSemantics with (at_external:=CL_at_external)
                  (after_external:=CL_after_external)
                  (corestep:=clight_corestep FE)
                  (halted:=CL_halted).
    apply CL_initial_core.
    apply CL_corestep_not_at_external.
    apply CL_corestep_not_halted.
    apply CL_at_external_halted_excl.
    apply CL_after_at_external_excl.
Defined.

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
          (*eapply external_call_mem_forward; eassumption.*)
         (*free*)
         eapply freelist_forward; eassumption.
         eapply freelist_forward; eassumption.
         eapply freelist_forward; eassumption.
       eapply HFE. apply H.
Qed.

Definition CL_coop_sem
           (FE:function -> list val -> mem -> env -> temp_env -> mem -> Prop)
           (HFE: forall f vargs m e le m', FE f vargs m e le m'-> mem_forward m m')
           : CoopCoreSem genv CL_core.
apply Build_CoopCoreSem with (coopsem := CL_core_sem FE).
  apply CL_forward. apply HFE.
Defined.

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

(*Definition clight_corestep1 (ge: genv) := clight_corestep function_entry1 ge.*)

Definition CL_core_sem1 := CL_core_sem function_entry1.
Definition CL_coop_sem1 : CoopCoreSem genv CL_core.
  eapply (CL_coop_sem function_entry1).
  apply function_entry1_forward.
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

(*Definition clight_corestep2 (ge: genv) := clight_corestep function_entry2 ge.*)

Definition CL_core_sem2 := CL_core_sem function_entry2.
Definition CL_coop_sem2 : CoopCoreSem genv CL_core.
  eapply (CL_coop_sem function_entry2).
  apply function_entry2_forward.
Defined.


