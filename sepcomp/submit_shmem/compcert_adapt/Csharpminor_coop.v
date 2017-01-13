Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import compcert.common.Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Maps.

Require Import sepcomp.Cminor_coop.
  (*to enable reuse of the lemmas eval_unop_valid and eval_binop_valid*)

Require Import sepcomp.Csharpminor.
Require Import sepcomp.mem_lemmas. (*for mem_forward*)
Require Import sepcomp.core_semantics.

(*Obtained from Cminor.state by deleting the memory components.*)
Inductive CSharpMin_core: Type :=
  | CSharpMin_State:                      (**r Execution within a function *)
      forall (f: function)              (**r currently executing function  *)
             (s: stmt)                  (**r statement under consideration *)
             (k: cont)                  (**r its continuation -- what to do next *)
             (e: Csharpminor.env)                   (**r current local environment *)
             (le: Csharpminor.temp_env),             (**r current temporary environment *)
      CSharpMin_core
  | CSharpMin_Callstate:                  (**r Invocation of a function *)
      forall (f: fundef)                (**r function to invoke *)
             (args: list val)           (**r arguments provided by caller *)
             (k: cont),                  (**r what to do next  *)
      CSharpMin_core
  | CSharpMin_Returnstate:                (**r Return from a function *)
      forall (v: val)                   (**r Return value *)
             (k: cont),                  (**r what to do next *)
      CSharpMin_core.

Definition ToState (q:CSharpMin_core) (m:mem): Csharpminor.state :=
  match q with
     CSharpMin_State f s k sp e => State f s k sp e m
   | CSharpMin_Callstate f args k => Callstate f args k m
   | CSharpMin_Returnstate v k => Returnstate v k m
  end.

Definition FromState (c: Csharpminor.state) : CSharpMin_core * mem :=
  match c with
     State f s k sp e m => (CSharpMin_State f s k sp e, m)
   | Callstate f args k m => (CSharpMin_Callstate f args k, m)
   | Returnstate v k m => (CSharpMin_Returnstate v k, m)
  end.

Definition CSharpMin_at_external (c: CSharpMin_core) : option (external_function * signature * list val) :=
  match c with
  | CSharpMin_State _ _ _ _ _ => None
  | CSharpMin_Callstate fd args k => match fd with
                                  Internal f => None
                                | External ef => Some (ef, ef_sig ef, args)
                              end
  | CSharpMin_Returnstate v k => None
 end.

Definition CSharpMin_after_external (vret: option val) (c: CSharpMin_core) : option CSharpMin_core :=
  match c with
    CSharpMin_Callstate fd args k =>
         match fd with
            Internal f => None
          | External ef => match vret with
                             None => Some (CSharpMin_Returnstate Vundef k)
                           | Some v => Some (CSharpMin_Returnstate v k)
                           end
         end
  | _ => None
  end.

Inductive CSharpMin_corestep (ge : genv) : CSharpMin_core -> mem -> CSharpMin_core ->  mem -> Prop :=
   csharpmin_corestep_skip_seq: forall f s k e le m,
      CSharpMin_corestep ge (CSharpMin_State f Sskip (Kseq s k) e le) m
        (CSharpMin_State f s k e le) m

  | csharpmin_corestep_skip_block: forall f k e le m,
      CSharpMin_corestep ge (CSharpMin_State f Sskip (Kblock k) e le) m
        (CSharpMin_State f Sskip k e le) m
  | csharpmin_corestep_skip_call: forall f k e le m m',
      is_call_cont k ->
      Mem.free_list m (blocks_of_env e) = Some m' ->
      CSharpMin_corestep ge (CSharpMin_State f Sskip k e le) m
        (CSharpMin_Returnstate Vundef k) m'

  | csharpmin_corestep_set: forall f id a k e le m v,
      eval_expr ge e le m a v ->
      CSharpMin_corestep ge (CSharpMin_State f (Sset id a) k e le) m
        (CSharpMin_State f Sskip k e (PTree.set id v le)) m

  | csharpmin_corestep_store: forall f chunk addr a k e le m vaddr v m',
      eval_expr ge e le m addr vaddr ->
      eval_expr ge e le m a v ->
      Mem.storev chunk m vaddr v = Some m' ->
      CSharpMin_corestep ge (CSharpMin_State f (Sstore chunk addr a) k e le) m
        (CSharpMin_State f Sskip k e le) m'

  | csharpmin_corestep_call: forall f optid sig a bl k e le m vf vargs fd,
      eval_expr ge e le m a vf ->
      eval_exprlist ge e le m bl vargs ->
      Genv.find_funct ge vf = Some fd ->
      funsig fd = sig ->
      CSharpMin_corestep ge (CSharpMin_State f (Scall optid sig a bl) k e le) m
        (CSharpMin_Callstate fd vargs (Kcall optid f e le k)) m

(* WE DO NOT TREAT BUILTINS
  | csharpmin_corestep_builtin: forall f optid ef bl k e le m vargs t vres m',
      eval_exprlist ge e le m bl vargs ->
      external_call ef ge vargs m t vres m' ->
      CSharpMin_corestep ge (CSharpMin_State f (Sbuiltin optid ef bl) k e le) m
         (CSharpMin_State f Sskip k e (Cminor.set_optvar optid vres le)) m'
*)

  | csharpmin_corestep_seq: forall f s1 s2 k e le m,
      CSharpMin_corestep ge (CSharpMin_State f (Sseq s1 s2) k e le) m
        (CSharpMin_State f s1 (Kseq s2 k) e le) m

  | csharpmin_corestep_ifthenelse: forall f a s1 s2 k e le m v b,
      eval_expr ge e le m a v ->
      Val.bool_of_val v b ->
      CSharpMin_corestep ge (CSharpMin_State f (Sifthenelse a s1 s2) k e le) m
        (CSharpMin_State f (if b then s1 else s2) k e le) m

  | csharpmin_corestep_loop: forall f s k e le m,
      CSharpMin_corestep ge (CSharpMin_State f (Sloop s) k e le) m
        (CSharpMin_State f s (Kseq (Sloop s) k) e le) m

  | csharpmin_corestep_block: forall f s k e le m,
      CSharpMin_corestep ge (CSharpMin_State f (Sblock s) k e le) m
        (CSharpMin_State f s (Kblock k) e le) m

  | csharpmin_corestep_exit_seq: forall f n s k e le m,
      CSharpMin_corestep ge (CSharpMin_State f (Sexit n) (Kseq s k) e le) m
        (CSharpMin_State f (Sexit n) k e le) m
  | csharpmin_corestep_exit_block_0: forall f k e le m,
      CSharpMin_corestep ge (CSharpMin_State f (Sexit O) (Kblock k) e le) m
        (CSharpMin_State f Sskip k e le) m
  | step_exit_block_S: forall f n k e le m,
      CSharpMin_corestep ge (CSharpMin_State f (Sexit (S n)) (Kblock k) e le) m
        (CSharpMin_State f (Sexit n) k e le) m

  | csharpmin_corestep_switch: forall f a cases k e le m n,
      eval_expr ge e le m a (Vint n) ->
      CSharpMin_corestep ge (CSharpMin_State f (Sswitch a cases) k e le) m
        (CSharpMin_State f (seq_of_lbl_stmt (select_switch n cases)) k e le) m

  | csharpmin_corestep_return_0: forall f k e le m m',
      Mem.free_list m (blocks_of_env e) = Some m' ->
      CSharpMin_corestep ge (CSharpMin_State f (Sreturn None) k e le) m
        (CSharpMin_Returnstate Vundef (call_cont k)) m'
  | csharpmin_corestep_return_1: forall f a k e le m v m',
      eval_expr ge e le m a v ->
      Mem.free_list m (blocks_of_env e) = Some m' ->
      CSharpMin_corestep ge (CSharpMin_State f (Sreturn (Some a)) k e le) m
        (CSharpMin_Returnstate v (call_cont k)) m'
  | csharpmin_corestep_label: forall f lbl s k e le m,
      CSharpMin_corestep ge (CSharpMin_State f (Slabel lbl s) k e le) m
        (CSharpMin_State f s k e le) m

  | csharpmin_corestep_goto: forall f lbl k e le m s' k',
      find_label lbl f.(fn_body) (call_cont k) = Some(s', k') ->
      CSharpMin_corestep ge (CSharpMin_State f (Sgoto lbl) k e le) m
        (CSharpMin_State f s' k' e le) m

  | csharpmin_corestep_internal_function: forall f vargs k m m1 e le,
      list_norepet (map fst f.(fn_vars)) ->
      list_norepet f.(fn_params) ->
      list_disjoint f.(fn_params) f.(fn_temps) ->
      alloc_variables empty_env m (fn_vars f) e m1 ->
      bind_parameters f.(fn_params) vargs (create_undef_temps f.(fn_temps)) = Some le ->
      CSharpMin_corestep ge (CSharpMin_Callstate (Internal f) vargs k) m
        (CSharpMin_State f f.(fn_body) k e le) m1
(*
  | csharpmin_corestep_external_function: forall ef vargs k m t vres m',
      external_call ef ge vargs m t vres m' ->
      step (Callstate (External ef) vargs k) m
         t (Returnstate vres k m')
*)
  | csharpmin_corestep_return: forall v optid f e le k m,
      CSharpMin_corestep ge (CSharpMin_Returnstate v (Kcall optid f e le k)) m
        (CSharpMin_State f Sskip k e (Cminor.set_optvar optid v le)) m.

Lemma CSharpMin_corestep_not_at_external:
       forall ge m q m' q', CSharpMin_corestep ge q m q' m' ->
       CSharpMin_at_external q = None.
  Proof. intros. inv H; reflexivity. Qed.

Definition CSharpMin_halted (q : CSharpMin_core): option val :=
    match q with
       CSharpMin_Returnstate v Kstop => Some v
     | _ => None
    end.

Lemma CSharpMin_corestep_not_halted : forall ge m q m' q',
       CSharpMin_corestep ge q m q' m' -> CSharpMin_halted q = None.
  Proof. intros. inv H; reflexivity. Qed.

Lemma CSharpMin_at_external_halted_excl :
       forall q, CSharpMin_at_external q = None \/ CSharpMin_halted q = None.
   Proof. intros. destruct q; auto. Qed.

Lemma CSharpMin_after_at_external_excl : forall retv q q',
      CSharpMin_after_external retv q = Some q' -> CSharpMin_at_external q' = None.
  Proof. intros.
       destruct q; simpl in *; try inv H.
       destruct f; try inv H1; simpl; trivial.
         destruct retv; inv H0; simpl; trivial.
Qed.

Definition CSharpMin_initial_core (ge:genv) (v: val) (args:list val): option CSharpMin_core :=
   match v with
     | Vptr b i =>
          if Int.eq_dec i Int.zero
          then match Genv.find_funct_ptr ge b with
                 | None => None
                 | Some f => Some (CSharpMin_Callstate f args Kstop)
               end
          else None
     | _ => None
    end.
 (*
Parameter CSharpMin_MainIdent:ident.

Definition CSharpMin_make_initial_core (ge:genv) (v: val) (args:list val): option CSharpMin_core :=
   match Genv.find_symbol ge CSharpMin_MainIdent with
        None => None
      | Some b => match Genv.find_funct_ptr ge b with
                              None => None
                            | Some f => match funsig f with
                                                   {| sig_args := sargs; sig_res := sres |} =>
                                                       match sargs, sres with
                                                          nil, Some Tint => Some (CSharpMin_Callstate f nil Kstop) (*args = nil???*)
                                                       | _ , _ => None
                                                       end
                                                 end
                            end
    end.*)
(*Original Csharpminor_semantics has this for initial states:
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      funsig f = mksignature nil (Some Tint) ->
      initial_state p (Callstate f nil Kstop m0).
 ie esseantially the same as Cminor*)

Definition CSharpMin_core_sem : CoreSemantics genv CSharpMin_core mem.
  eapply @Build_CoreSemantics with (at_external:=CSharpMin_at_external)
                  (after_external:=CSharpMin_after_external)
                  (corestep:=CSharpMin_corestep)
                  (halted:=CSharpMin_halted).
    apply CSharpMin_initial_core.
    apply CSharpMin_corestep_not_at_external.
    apply CSharpMin_corestep_not_halted.
    apply CSharpMin_at_external_halted_excl.
    apply CSharpMin_after_at_external_excl.
Defined.

(************************NOW SHOW THAT WE ALSO HAVE A COOPSEM******)
Lemma alloc_variables_forward: forall vars m e e2 m'
      (M: alloc_variables e m vars e2 m'),
      mem_forward m m'.
Proof. intros.
  induction M.
  apply mem_forward_refl.
  apply alloc_forward in H.
  eapply mem_forward_trans; eassumption.
Qed.

Lemma CSharpMin_forward : forall g c m c' m' (CS: CSharpMin_corestep g c m c' m'),
      mem_forward m m'.
Proof. intros.
     induction CS; try apply mem_forward_refl.
         eapply freelist_forward; eassumption.
         (*Storev*)
          destruct vaddr; simpl in H1; inv H1.
          eapply store_forward; eassumption.
         (*builtin*)
          (*eapply external_call_mem_forward; eassumption.*)
         eapply freelist_forward; eassumption.
         eapply freelist_forward; eassumption.
         eapply alloc_variables_forward; eassumption.
Qed.

Program Definition csharpmin_coop_sem :
  CoopCoreSem Csharpminor.genv CSharpMin_core.
apply Build_CoopCoreSem with (coopsem := CSharpMin_core_sem).
  apply CSharpMin_forward.
Defined.
(*
Definition coopstep g c m c' m' :=
   CSharpMin_corestep g c m c' m'.

Lemma csharpmin_coopstep_not_at_external: forall ge m q m' q',
  coopstep ge q m q' m' -> CSharpMin_at_external q = None.
Proof.
  intros.
  eapply CSharpMin_corestep_not_at_external. apply H.
Qed.

Lemma csharpmin_coopstep_not_halted :
  forall ge m q m' q', coopstep ge q m q' m' -> CSharpMin_halted q = None.
Proof.
  intros.
  eapply CSharpMin_corestep_not_halted. apply H.
Qed.

Program Definition csharpmin_core_sem :
  CoreSemantics Csharpminor.genv CSharpMin_core mem :=
  @Build_CoreSemantics _ _ _
    CSharpMin_initial_core
    CSharpMin_at_external
    CSharpMin_after_external
    CSharpMin_halted
    coopstep
    csharpmin_coopstep_not_at_external
    csharpmin_coopstep_not_halted
    CSharpMin_at_external_halted_excl
    CSharpMin_after_at_external_excl.

(************************NOW SHOW THAT WE ALSO HAVE A COOPSEM******)

Lemma csharpmin_coop_forward : forall g c m c' m' (CS: coopstep g c m c' m'),
      mem_lemmas.mem_forward m m'.
Proof. intros. eapply CSharpMin_forward. apply CS. Qed.

Program Definition csharpmin_coop_sem :
  CoopCoreSem Csharpminor.genv CSharpMin_core.
apply Build_CoopCoreSem with (coopsem := csharpmin_core_sem).
  apply csharpmin_coop_forward.
Defined.
*)