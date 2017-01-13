Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import compcert.common.Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.

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

Definition CSharpMin_corestep (ge : genv)  (q : CSharpMin_core) (m : mem) (q' : CSharpMin_core) (m' : mem) : Prop.
  destruct q; destruct q'.
  (*State - State*)
       apply (exists t, step ge (State f s k e le m)  t (State f0 s0 k0 e0 le0 m')).
  (*State - Callstate: one case: step_call*)
       apply (exists t, step ge (State f s k e le m)  t (Callstate f0 args k0 m')).
  (*State - Returnstate - three cases: step_skip_call, step_return_0, step_return_1*)
       apply (exists t, step ge (State f s k e le m)  t (Returnstate v k0 m')).
  (*Callstate - State: only case: step_internal_function*)
       apply (exists t, step ge (Callstate f args k m) t (State f0 s k0 e le m')).
  (*Callstate - Callstate: no case*)
       apply False.
  (*Callstate - Returnstate: one case: step_external_function : we don't want this as a step in this semantics, since
                    stepping should not happen at_external*)
       apply False.
  (*Returnstate - State: one case: step_return*)
       apply (exists t, step ge (Returnstate v k m) t (State f s k0 e le m')).
  (*Returnstate - Callstate: no case*)
       apply False.
  (*Returnstate - Returnstate: no case*)
       apply False.
Defined.

Lemma CSharpMin_corestep_not_at_external:
       forall ge m q m' q', CSharpMin_corestep ge q m q' m' -> CSharpMin_at_external q = None.
  Proof. intros.
     unfold CSharpMin_corestep in H.
     destruct q; destruct q'; simpl in *; try reflexivity.
       (*case step_internal_function*)
             destruct H as [t Ht]. inversion Ht; subst. reflexivity.
       (*Call - Call: no case*)
             contradiction.
       (*Call - Return: no case in Cmin_corestep*)
             contradiction.
  Qed.

Definition CSharpMin_halted (q : CSharpMin_core): option val :=
    match q with
       CSharpMin_Returnstate v Kstop => Some v
     | _ => None
    end.

Lemma CSharpMin_corestep_not_halted : forall ge m q m' q',
       CSharpMin_corestep ge q m q' m' -> CSharpMin_halted q = None.
  Proof. intros.
     unfold CSharpMin_corestep in H.
     destruct q; destruct q'; simpl in *; try reflexivity.
          (*case step_return*)
             destruct H as [t Ht]. inversion Ht; subst.
             destruct v; reflexivity.
       (*Returnstate - Callstate: no case*)
             contradiction.
       (*Returnstate - Returnstate: no case in Cmin_corestep*)
             contradiction.
  Qed.

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


Lemma CSharpMin_corestep_2_CompCertStep: forall (ge : genv)  (q : CSharpMin_core) (m : mem) (q' : CSharpMin_core) (m' : mem) ,
   CSharpMin_corestep ge q m q' m' ->
   exists t, step ge (ToState q m) t (ToState q' m').
Proof.
  intros. destruct q; destruct q'; induction H; simpl; eauto.
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

Lemma CSharpMin_forward : forall g c m c' m' (CS: CSharpMin_corestep g c m c' m'),
      mem_lemmas.mem_forward m m'.
  Proof. intros.
     unfold CSharpMin_corestep in CS.
     destruct c; destruct c'; simpl in *; try contradiction.
       destruct CS as [t CS].
         inv CS; try apply mem_forward_refl.
         (*Storev*)
          destruct vaddr; simpl in H14; inv H14.
          eapply store_forward; eassumption.
         (*builtin*)
          eapply external_call_mem_forward; eassumption.
       destruct CS as [t CS].
         inv CS; simpl; try apply mem_forward_refl.
       destruct CS as [t CS].
         inv CS; simpl; try apply mem_forward_refl.
         (*free*)
         eapply freelist_forward. apply H10.
         eapply freelist_forward. apply H6.
         eapply freelist_forward. apply H10.
       destruct CS as [t CS].
         inv CS; simpl; try apply mem_forward_refl.
         eapply alloc_variables_forward. apply H13.
       destruct CS as [t CS].
         inv CS; simpl; try apply mem_forward_refl.
Qed.

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