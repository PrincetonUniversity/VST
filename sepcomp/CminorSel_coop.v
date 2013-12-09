Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import compcert.common.Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.

Require Import sepcomp.CminorSel. 
Require Import sepcomp.mem_lemmas. (*for mem_forward*)
Require Import sepcomp.core_semantics.

(*Require Import Maps.
Require Import Cminor.
Require Import Op.
Require Import Switch.
Require Import Smallstep.*)

Inductive CMinSel_core: Type :=
  | CMinSel_State:                      (**r execution within a function *)
      forall (f: function)              (**r currently executing function  *)
             (s: stmt)                  (**r statement under consideration *)
             (k: cont)                  (**r its continuation -- what to do next *)
             (sp: val)                  (**r current stack pointer *)
             (e: Cminor.env),           (**r current local environment *)
      CMinSel_core
  | CMinSel_Callstate:                  (**r invocation of a fundef  *)
      forall (f: fundef)                (**r fundef to invoke *)
             (args: list val)           (**r arguments provided by caller *)
             (k: cont),                 (**r what to do next  *)
      CMinSel_core
  | CMinSel_Returnstate:
      forall (v: val)                   (**r return value *)
             (k: cont),                 (**r what to do next *)
      CMinSel_core.

Definition ToState (q:CMinSel_core) (m:mem): CminorSel.state :=
  match q with 
     CMinSel_State f s k sp e => State f s k sp e m
   | CMinSel_Callstate f args k => Callstate f args k m
   | CMinSel_Returnstate v k => Returnstate v k m 
  end.

Definition FromState (c: CminorSel.state) : CMinSel_core * mem :=
  match c with 
     State f s k sp e m => (CMinSel_State f s k sp e, m)
   | Callstate f args k m => (CMinSel_Callstate f args k, m)
   | Returnstate v k m => (CMinSel_Returnstate v k, m)
  end. 

Definition CMinSel_at_external (c: CMinSel_core) : option (external_function * signature * list val) :=
  match c with
  | CMinSel_State _ _ _ _ _ => None
  | CMinSel_Callstate fd args k => match fd with
                                  Internal f => None
                                | External ef => Some (ef, ef_sig ef, args)
                              end
  | CMinSel_Returnstate v k => None
 end.

Definition CMinSel_after_external (vret: option val) (c: CMinSel_core) : option CMinSel_core :=
  match c with 
    CMinSel_Callstate fd args k => 
         match fd with
            Internal f => None
          | External ef => match vret with
                             None => Some (CMinSel_Returnstate Vundef k)
                           | Some v => Some (CMinSel_Returnstate v k)
                           end
         end
  | _ => None
  end.

Definition CMinSel_corestep (ge : genv)  (q : CMinSel_core) (m : mem) (q' : CMinSel_core) (m' : mem) : Prop.
  destruct q; destruct q'.
  (*State - State*)
       apply (exists t, step ge (State f s k sp e m)  t (State f0 s0 k0 sp0 e0 m')).
  (*State - Callstate: one case: step_call*)
       apply (exists t, step ge (State f s k sp e m)  t (Callstate f0 args k0 m')).
  (*State - Returnstate - three cases: step_skip_call, step_return_0, step_return_1*)
       apply (exists t, step ge (State f s k sp e m)  t (Returnstate v k0 m')).
  (*Callstate - State: only case: step_internal_function*)
       apply (exists t, step ge (Callstate f args k m) t (State f0 s k0 sp e m')).
  (*Callstate - Callstate: no case*)
       apply False.
  (*Callstate - Returnstate: one case: step_external_function : we don't want this as a step in this semantics, since
                    stepping should not happen at_external*)
       apply False.
  (*Returnstate - State: one case: step_return*)
       apply (exists t, step ge (Returnstate v k m) t (State f s k0 sp e m')).
  (*Returnstate - Callstate: no case*)
       apply False.
  (*Returnstate - Returnstate: no case*)
       apply False.
Defined.

Lemma CMinSel_corestep_not_at_external:
       forall ge m q m' q', CMinSel_corestep ge q m q' m' -> CMinSel_at_external q = None.
  Proof. intros.
     unfold CMinSel_corestep in H. 
     destruct q; destruct q'; simpl in *; try reflexivity.
       (*case step_internal_function*)  
             destruct H as [t Ht]. inversion Ht; subst. reflexivity.
       (*Call - Call: no case*)
             contradiction.
       (*Call - Return: no case in CminorSel_corestep*)
             contradiction.
  Qed.

Definition CMinSel_halted (q : CMinSel_core): option val :=
    match q with 
       CMinSel_Returnstate v Kstop => Some v
     | _ => None
    end.

Lemma CMinSel_corestep_not_halted : forall ge m q m' q', 
       CMinSel_corestep ge q m q' m' -> CMinSel_halted q = None.
  Proof. intros.
     unfold CMinSel_corestep in H. 
     destruct q; destruct q'; simpl in *; try reflexivity.
          (*case step_return*) 
             destruct H as [t Ht]. inversion Ht; subst. 
             destruct v; reflexivity.
       (*Returnstate - Callstate: no case*)
             contradiction.
       (*Returnstate - Returnstate: no case in Cmin_corestep*)
             contradiction.
  Qed.
    
Lemma CMinSel_at_external_halted_excl :
       forall q, CMinSel_at_external q = None \/ CMinSel_halted q = None.
   Proof. intros. destruct q; auto. Qed.

Lemma CMinSel_after_at_external_excl : forall retv q q',
      CMinSel_after_external retv q = Some q' -> CMinSel_at_external q' = None.
  Proof. intros.
       destruct q; simpl in *; try inv H.
       destruct f; try inv H1; simpl; trivial.
         destruct retv; inv H0; simpl; trivial.
Qed.

Definition CMinSel_initial_core (ge:genv) (v: val) (args:list val): option CMinSel_core :=
   match v with
     | Vptr b i => 
          if Int.eq_dec i Int.zero 
          then match Genv.find_funct_ptr ge b with
                 | None => None
                 | Some f => Some (CMinSel_Callstate f args Kstop)
               end
          else None
     | _ => None
    end.

Definition CMinSel_core_sem : CoreSemantics genv CMinSel_core mem.
  eapply @Build_CoreSemantics with (at_external:=CMinSel_at_external)
                  (after_external:=CMinSel_after_external)
                  (corestep:=CMinSel_corestep)
                  (halted:=CMinSel_halted). 
    apply CMinSel_initial_core.
    apply CMinSel_corestep_not_at_external.
    apply CMinSel_corestep_not_halted.
    apply CMinSel_at_external_halted_excl.
    apply CMinSel_after_at_external_excl.
Defined.


Lemma CMinSel_corestep_2_CompCertStep: forall (ge : genv)  (q :CMinSel_core) (m : mem) (q' : CMinSel_core) (m' : mem) ,
   CMinSel_corestep ge q m q' m' -> 
   exists t, step ge (ToState q m) t (ToState q' m').
Proof.
  intros. destruct q; destruct q'; induction H; simpl; eauto. 
Qed.

Lemma CompCertStep_CMinSel_corestep: forall (ge : genv)  (q : CMinSel_core) (m : mem) (q' : CMinSel_core) (m' : mem)  t,
   step ge (ToState q m) t (ToState q' m') ->
   CMinSel_at_external q = None ->
   CMinSel_corestep ge q m q' m'.
Proof.
  intros. destruct q; destruct q'; simpl in *; try eexists; try eassumption; inv H; discriminate.
Qed.

Lemma CompCertStep_CMinSel_corestep': forall (ge : genv)  (q : CMinSel_core) (m : mem) c' t q' m',
   step ge (ToState q m) t c' ->
   CMinSel_at_external q = None ->
     q'= fst (FromState c') -> m' = snd (FromState c') -> 
     CMinSel_corestep ge q m q' m'.
Proof.
  intros. assert (c' = ToState q' m'). subst. destruct c'; simpl; trivial.
  rewrite H3 in H. clear H3. eapply CompCertStep_CMinSel_corestep; eassumption.
Qed.

Lemma CMinSel_forward : forall g c m c' m' (CS: CMinSel_corestep g c m c' m'), 
      mem_lemmas.mem_forward m m'.
  Proof. intros.
     unfold CMinSel_corestep in CS. 
     destruct c; destruct c'; simpl in *; try contradiction. 
       destruct CS as [t CS].
         inv CS; try apply mem_forward_refl.
         (*Storev*)
          destruct vaddr; simpl in H15; inv H15. 
          eapply store_forward. eassumption. 
         (*builtin*) 
          eapply external_call_mem_forward; eassumption.
       destruct CS as [t CS].
         inv CS; simpl; try apply mem_forward_refl.
         (*free*)
         eapply free_forward; eassumption.
       destruct CS as [t CS].
         inv CS; simpl.
         eapply free_forward; eassumption.
         eapply free_forward; eassumption.
         eapply free_forward; eassumption.
       destruct CS as [t CS].
         inv CS; simpl. 
         eapply alloc_forward; eassumption.
       destruct CS as [t CS].
         inv CS; simpl. apply mem_forward_refl.
Qed.

Definition coopstep g c m c' m' :=
   CMinSel_corestep g c m c' m'.

Lemma cminsel_coopstep_not_at_external: forall ge m q m' q',
  coopstep ge q m q' m' -> CMinSel_at_external q = None.
Proof.
  intros.
  eapply CMinSel_corestep_not_at_external. apply H. 
Qed.

Lemma cminsel_coopstep_not_halted :
  forall ge m q m' q', coopstep ge q m q' m' -> CMinSel_halted q = None.
Proof.
  intros.
  eapply CMinSel_corestep_not_halted. apply H.
Qed.

Program Definition cminsel_core_sem : 
  CoreSemantics genv CMinSel_core mem :=
  @Build_CoreSemantics _ _ _ 
    CMinSel_initial_core
    CMinSel_at_external
    CMinSel_after_external
    CMinSel_halted
    coopstep
    cminsel_coopstep_not_at_external
    cminsel_coopstep_not_halted 
    CMinSel_at_external_halted_excl
    CMinSel_after_at_external_excl.

(************************NOW SHOW THAT WE ALSO HAVE A COOPSEM******)

Lemma cminsel_coop_forward : forall g c m c' m' (CS: coopstep g c m c' m'), 
      mem_lemmas.mem_forward m m'.
Proof. intros. eapply CMinSel_forward. apply CS. Qed.

Program Definition cminsel_coop_sem : 
  CoopCoreSem genv CMinSel_core.
apply Build_CoopCoreSem with (coopsem := cminsel_core_sem).
  apply cminsel_coop_forward.
Defined.
