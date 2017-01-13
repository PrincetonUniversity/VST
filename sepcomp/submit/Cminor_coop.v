Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import compcert.common.Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.

Require Import sepcomp.Cminor.
Require Import sepcomp.mem_lemmas. (*for mem_forward and wd_mem*)
Require Import sepcomp.core_semantics.

(*Obtained from Cminor.state by deleting the memory components.*)
Inductive CMin_core: Type :=
  | CMin_State:                      (**r Execution within a function *)
      forall (f: function)              (**r currently executing function  *)
             (s: stmt)                  (**r statement under consideration *)
             (k: cont)                  (**r its continuation -- what to do next *)
             (sp: val)                  (**r current stack pointer *)
             (e: env),                   (**r current local environment *)
      CMin_core
  | CMin_Callstate:                  (**r Invocation of a function *)
      forall (f: fundef)                (**r function to invoke *)
             (args: list val)           (**r arguments provided by caller *)
             (k: cont),                  (**r what to do next  *)
      CMin_core
  | CMin_Returnstate:                (**r Return from a function *)
      forall (v: val)                   (**r Return value *)
             (k: cont),                  (**r what to do next *)
      CMin_core.

Definition ToState (q:CMin_core) (m:mem): Cminor.state :=
  match q with
     CMin_State f s k sp e => State f s k sp e m
   | CMin_Callstate f args k => Callstate f args k m
   | CMin_Returnstate v k => Returnstate v k m
  end.

Definition FromState (c: Cminor.state) : CMin_core * mem :=
  match c with
     State f s k sp e m => (CMin_State f s k sp e, m)
   | Callstate f args k m => (CMin_Callstate f args k, m)
   | Returnstate v k m => (CMin_Returnstate v k, m)
  end.
(*
Definition CMin_init_mem (ge:genv)  (m:mem) d:  Prop:=
   Genv.alloc_variables ge Mem.empty d = Some m.
(*Defined initial memory, by adapting the definition of Genv.init_mem*)
*)

(* initial_core : G -> val -> list val -> option C;*)
Definition CMin_initial_core (ge:Cminor.genv) (v: val) (args:list val): option CMin_core :=
   match v with
        Vptr b i =>
          if Int.eq_dec i  Int.zero
          then match Genv.find_funct_ptr ge b with
                 | None => None
                 | Some f => Some (CMin_Callstate f args Kstop)
               end
          else None
      | _ => None
   end.

(*
Parameter CMin_MainIdent:ident.

Definition CMin_make_initial_core (ge:genv) (v: val) (args:list val): option CMin_core :=
   match Genv.find_symbol ge CMin_MainIdent with
        None => None
      | Some b => match Genv.find_funct_ptr ge b with
                    None => None
                  | Some f => match funsig f with
                                           {| sig_args := sargs; sig_res := sres |} =>
                                                   match sargs, sres with
                                                      nil, Some Tint => Some (CMin_Callstate f nil Kstop) (*args = nil???*)
                                                   | _ , _ => None
                                                   end
                                       end
                  end
   end.
*)
(*Original Cminor_semantics has this for initial states:
Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      funsig f = mksignature nil (Some Tint) ->
      initial_state p (Callstate f nil Kstop m0).*)

Definition CMin_at_external (c: CMin_core) : option (external_function * signature * list val) :=
  match c with
  | CMin_State f s k sp e => None
  | CMin_Callstate fd args k => match fd with
                                  Internal f => None
                                | External ef => Some (ef, ef_sig ef, args)
                              end
  | CMin_Returnstate v k => None
 end.

Definition CMin_after_external (vret: option val) (c: CMin_core) : option CMin_core :=
  match c with
    CMin_Callstate fd args k =>
         match fd with
            Internal f => None
          | External ef => match vret with
                             None => Some (CMin_Returnstate Vundef k)
                           | Some v => Some (CMin_Returnstate v k)
                           end
         end
  | _ => None
  end.

Definition CMin_corestep (ge : genv)  (q : CMin_core) (m : mem) (q' : CMin_core) (m' : mem) : Prop.
  destruct q; destruct q'.
  (*State - State*)
       apply (exists t, Cminor.step ge (State f s k sp e m)  t (State f0 s0 k0 sp0 e0 m')).
  (*State - Callstate: two cases: step_call, step_tailcall*)
       apply (exists t, Cminor.step ge (State f s k sp e m)  t (Callstate f0 args k0 m')).
  (*State - Returnstate - three cases: step_skip_call, step_return_0, step_return_1*)
       apply (exists t, Cminor.step ge (State f s k sp e m)  t (Returnstate v k0 m')).
  (*Callstate - State: only case: step_internal_function*)
       apply (match f with
                Internal ff =>
                  exists t, Cminor.step ge (Callstate f args k m) t (State f0 s k0 sp e m')
              | External _ => False
              end).
  (*Callstate - Callstate: no case*)
       apply False.
  (*Callstate - Returnstate: one case: step_external_function : we don't want this as a step in this semantics, since
                    stepping should not happen at_external*)
       apply False.
  (*Returnstate - State: one case: step_return*)
       apply (exists t, Cminor.step ge (Returnstate v k m) t (State f s k0 sp e m')).
  (*Returnstate - Callstate: no case*)
       apply False.
  (*Returnstate - Returnstate: no case*)
       apply False.
Defined.

Lemma CMin_corestep_not_at_external:
       forall ge m q m' q', CMin_corestep ge q m q' m' -> CMin_at_external q = None.
  Proof. intros.
     unfold CMin_corestep in H.
     destruct q; destruct q'; simpl in *; try reflexivity.
       (*case step_internal_function*)
             destruct f; try contradiction.
             destruct H as [t Ht]. inversion Ht; subst. reflexivity.
       (*Call - Call: no case*)
             contradiction.
       (*Call - Return: no case in Cmin_corestep*)
             contradiction.
  Qed.

Definition CMin_halted (q : CMin_core): option val :=
    match q with
       CMin_Returnstate v Kstop => Some v
     | _ => None
    end.

Lemma CMin_corestep_not_halted : forall ge m q m' q',
       CMin_corestep ge q m q' m' -> CMin_halted q = None.
  Proof. intros.
     unfold CMin_corestep in H.
     destruct q; destruct q'; simpl in *; try reflexivity.
          (*case step_return*)
             destruct H as [t Ht]. inversion Ht; subst.
             destruct v; reflexivity.
       (*Returnstate - Callstate: no case*)
             contradiction.
       (*Returnstate - Returnstate: no case in Cmin_corestep*)
             contradiction.
  Qed.

Lemma CMin_at_external_halted_excl :
       forall q, CMin_at_external q = None \/ CMin_halted q = None.
   Proof. intros. destruct q; auto. Qed.

Lemma CMin_after_at_external_excl : forall retv q q',
      CMin_after_external retv q = Some q' -> CMin_at_external q' = None.
  Proof. intros.
       destruct q; simpl in *; try inv H.
       destruct f; try inv H1; simpl; trivial.
         destruct retv; inv H0; simpl; trivial.
Qed.

Definition CMin_core_sem : CoreSemantics genv CMin_core mem.
  eapply @Build_CoreSemantics with (at_external:=CMin_at_external)
                  (after_external:=CMin_after_external) (corestep:=CMin_corestep)
                  (halted:=CMin_halted).
    apply CMin_initial_core.
    apply CMin_corestep_not_at_external.
    apply CMin_corestep_not_halted.
    apply CMin_at_external_halted_excl.
    apply CMin_after_at_external_excl.
Defined.

(************************NOW SHOW THAT WE ALSO HAVE A COOPSEM******)

(*A global assumption we need on external calls, in particular builtins
mem_wd deprecated
Parameter external_call_mem_wd:
  forall (ef : external_function) (F V : Type) (ge : Genv.t F V)
    (vargs : list val) (m1 : mem) (t : trace) (vres : val) (m2 : mem),
    external_call ef ge vargs m1 t vres m2 -> mem_wd m1 -> mem_wd m2.
*)

Lemma CMin_forward : forall g c m c' m' (CS: CMin_corestep g c m c' m'),
      mem_lemmas.mem_forward m m'.
  Proof. intros.
     unfold CMin_corestep in CS.
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
         (*free*)
         eapply free_forward. apply H14.
       destruct CS as [t CS].
         inv CS; simpl; try apply mem_forward_refl.
         eapply free_forward. apply H10.
         eapply free_forward. apply H6.
         eapply free_forward. apply H10.
       destruct f; try contradiction.
         destruct CS as [t CS].
         inv CS; simpl; try apply mem_forward_refl.
         eapply alloc_forward. apply H4.
       destruct CS as [t CS].
         inv CS; simpl; try apply mem_forward_refl.
Qed.

Definition coopstep g c m c' m' :=
   CMin_corestep g c m c' m'.

Lemma cmin_coopstep_not_at_external: forall ge m q m' q',
  coopstep ge q m q' m' -> CMin_at_external q = None.
Proof.
  intros.
  eapply CMin_corestep_not_at_external. apply H.
Qed.

Lemma cmin_coopstep_not_halted :
  forall ge m q m' q', coopstep ge q m q' m' -> CMin_halted q = None.
Proof.
  intros.
  eapply CMin_corestep_not_halted. apply H.
Qed.

Program Definition cmin_core_sem :
  CoreSemantics Cminor.genv CMin_core mem :=
  @Build_CoreSemantics _ _ _ (*_*)
    (*cl_init_mem*)
    CMin_initial_core
    CMin_at_external
    CMin_after_external
    CMin_halted
    coopstep
    cmin_coopstep_not_at_external
    cmin_coopstep_not_halted
    CMin_at_external_halted_excl
    CMin_after_at_external_excl.

Lemma cmin_coop_forward : forall g c m c' m' (CS: coopstep g c m c' m'),
      mem_lemmas.mem_forward m m'.
Proof. intros. eapply CMin_forward. apply CS. Qed.

Program Definition cmin_coop_sem :
  CoopCoreSem Cminor.genv CMin_core.
apply Build_CoopCoreSem with (coopsem := cmin_core_sem).
  apply cmin_coop_forward.
Defined.

Lemma CMin_corestep_2_CompCertStep: forall (ge : genv)  (q : CMin_core) (m : mem) (q' : CMin_core) (m' : mem) ,
   CMin_corestep ge q m q' m' ->
   exists t, step ge (ToState q m) t (ToState q' m').
Proof.
  intros. destruct q; destruct q'; try assumption; try contradiction.
  unfold CMin_corestep in H.
     destruct f; try contradiction.
        apply H.
Qed.

Lemma CompCertStep_CMin_corestep: forall (ge : genv)  (q : CMin_core) (m : mem) (q' : CMin_core) (m' : mem)  t,
   step ge (ToState q m) t (ToState q' m') ->
   CMin_at_external q = None ->
   CMin_corestep ge q m q' m'.
Proof.
  intros. destruct q; destruct q'; simpl in *; try eexists; try eassumption.
     inv H. eexists. econstructor; trivial.
     inv H.
     inv H. inv H0.
     inv H.
     inv H.
Qed.

Lemma CompCertStep_CMin_corestep': forall (ge : genv)  (q : CMin_core) (m : mem) c' t,
   step ge (ToState q m) t c' ->
   CMin_at_external q = None ->
     CMin_corestep ge q m (fst (FromState c')) (snd (FromState c')).
Proof.
  intros. destruct q; destruct c'; simpl in *; try eexists; try eassumption.
     inv H. eexists. econstructor; trivial.
     inv H.
     inv H. inv H0.
     inv H.
     inv H.
Qed.
(*
Lemma CMin_corestepSN_2_CompCertStepStar: forall (ge : genv) n (q : CMin_core) (m : mem) (q' : CMin_core) (m' : mem),
   corestepN CMin_corestepN ge n q m q' m' ->
   exists t, Smallstep.star step ge (ToState q m) t (ToState q' m').
Proof.
  intros ge n.
  induction n; simpl; intros.
      inv H. eexists. apply Smallstep.star_refl.
  destruct H as [c2 [m2 [Step1 Steps]]].
     destruct (IHn _ _ _ _ Steps) as [t Ht].
     destruct (CMin_corestep_2_CompCertStep _ _ _ _ _ Step1) as [t1 Ht1].
     eexists. econstructor. eassumption. eassumption.
       reflexivity.
Qed.

Lemma CMin_corestepSN_2_CompCertStepPlus: forall (ge : genv) n (q : CMin_core) (m : mem) (q' : CMin_core) (m' : mem),
   corestepN CMin_CompcertCoreSem ge (S n) q m q' m' ->
   exists t, Smallstep.plus step ge (ToState q m) t (ToState q' m').
Proof.
  intros.
  destruct H as [c2 [m2 [H X]]].
  destruct (CMin_corestep_2_CompCertStep _ _ _ _ _ H) as [t1 Ht1]. clear H.
  destruct (CMin_corestepSN_2_CompCertStepStar _ _ _ _ _ _ X) as [t2 Ht2]. clear X.
  eexists. econstructor. eassumption. eassumption. reflexivity.
Qed.

Lemma CMin_corestep_plus_2_CompCertStep_plus: forall (ge : genv)  (q : CMin_core) (m : mem) (q' : CMin_core) (m' : mem) ,
   corestep_plus CMin_CompcertCoreSem ge q m q' m' ->
   exists t, Smallstep.plus step ge (ToState q m) t (ToState q' m').
Proof.
  intros. destruct H as [n Hn].
  eapply CMin_corestepSN_2_CompCertStepPlus. apply Hn.
Qed.

Lemma CMin_corestep_star_2_CompCertStep_star: forall (ge : genv)  (q : CMin_core) (m : mem) (q' : CMin_core) (m' : mem) ,
   corestep_star CMin_CompcertCoreSem ge q m q' m' ->
   exists t, Smallstep.star step ge (ToState q m) t (ToState q' m').
Proof.
  intros. destruct H as [n Hn].
  eapply CMin_corestepSN_2_CompCertStepStar. apply Hn.
Qed.
*)
Lemma CompCertStep_2_CMin_corestep: forall (ge : genv)  (q : CMin_core) (m : mem) t c',
   step ge (ToState q m) t c' ->
   CMin_at_external q = None ->
   exists q', exists m', c' = ToState q' m' /\ CMin_corestep ge q m q' m'.
Proof.
  intros. destruct q; destruct c'; simpl in *.
     exists (CMin_State f0 s0 k0 sp0 e0). exists m0; simpl. split. trivial. eexists. eassumption.
     exists (CMin_Callstate f0 args  k0). exists m0; simpl. split. trivial. eexists. eassumption.
     exists (CMin_Returnstate v k0). exists m0; simpl. split. trivial. eexists. eassumption.
     exists (CMin_State f0 s k0 sp e). exists m0; simpl. split. trivial.
        destruct f. eexists. eassumption.
        inv H0.
     inv H.
     inv H. inv H0.
     exists (CMin_State f s k0 sp e). exists m0; simpl. split. trivial. eexists. eassumption.
     inv H.
     inv H.
Qed.

Lemma CMin_core2state_injective: forall q m q' m',
 ToState q m = ToState q' m' -> q'=q /\ m'=m.
  Proof. intros.
    destruct q; destruct q'; simpl in *; inv H; split; trivial.
  Qed.



