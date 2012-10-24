Require Import compcert.Coqlib.
Require Import compcert.AST.
Require Import compcert.Integers.
Require Import compcert.Values.
Require Import compcert.Memory.
Require Import compcert.Events.
Require Import compcert.Globalenvs.
Require Import compcert.Cminor.
Require Import veric.sim.

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

Definition CMin_init_mem (ge:genv)  (m:mem) d:  Prop:=
   Genv.alloc_variables ge Mem.empty d = Some m.
(*Defined initial memory, by adapting the definition of Genv.init_mem*)

Definition CMin_make_initial_core (ge:genv) (v: val) (args:list val): option CMin_core :=
   match v with
        Vptr b i => if Int.eq_dec i  Int.zero 
                            then 
                            match Genv.find_funct_ptr ge b with
                             None => None
                           | Some f => match funsig f with
                                           {| sig_args := sargs; sig_res := sres |} => 
                                                   match sargs, sres with 
                                                      nil, Some Tint => Some (CMin_Callstate f nil Kstop) (*args = nil???*)
                                                   | _ , _ => None
                                                   end
                                              end
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
       apply (exists t, Cminor.step ge (Callstate f args k m) t (State f0 s k0 sp e m')).
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
             destruct H as [t Ht]. inversion Ht; subst. reflexivity.
       (*Call - Call: no case*)
             contradiction.
       (*Call - Return: no case in Cmin_corestep*)
             contradiction.
  Qed.

Definition CMin_safely_halted (ge:genv)  (q : CMin_core): option int :=
    match q with 
       CMin_Returnstate (Vint r) Kstop => Some r
     | _ => None
    end.

Lemma CMin_corestep_not_halted : forall ge m q m' q', 
       CMin_corestep ge q m q' m' -> CMin_safely_halted ge q = None.
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
       forall ge q, CMin_at_external q = None \/ CMin_safely_halted ge q = None.
   Proof. intros. destruct q; auto. Qed.

Definition CMin_core_sem : CoreSemantics genv CMin_core mem (list (ident * globvar unit)).
  eapply @Build_CoreSemantics with (at_external:=CMin_at_external)(corestep:=CMin_corestep)
                  (safely_halted:=CMin_safely_halted). 
    apply CMin_init_mem.
    apply CMin_make_initial_core.
    apply CMin_after_external.
    apply CMin_corestep_not_at_external.
    apply CMin_corestep_not_halted.
    apply CMin_at_external_halted_excl.
Defined.

(*Not sure whether this holds, but I do assume the leamms below, Cminor_step_fun to hold...*)
Parameter Mem_free_deterministic: forall m sp f m1 m2,
                   Mem.free m sp 0 (fn_stackspace f) = Some m1 ->
                   Mem.free m sp 0 (fn_stackspace f) = Some m2 -> m1=m2.

Parameter eval_expr_deterministic: forall ge sp e m a v1 v2,
                eval_expr ge sp e m a v1 ->
                eval_expr ge sp e m a v2 -> v1=v2.

Parameter Mem_storev_deterministic: forall ch m a v m1 m2,
                Mem.storev ch m a v = Some m1 -> Mem.storev ch m a v = Some m2 -> m1 = m2.

Lemma Cminor_step_fun: forall ge q q1 t1 (K1: Cminor.step ge q t1 q1) q2 t2 (K2:step ge q t2 q2), q1 = q2.
  Proof. intros g1 q q1 t1 K1.
     induction K1; intros.
          inv K2; simpl in *; try contradiction. trivial.
          inv K2; simpl in *; try contradiction. trivial.
          inv K2; simpl in *; try contradiction. rewrite (Mem_free_deterministic _ _ _ _ _ H1 H11). trivial.
          inv K2; simpl in *; try contradiction. rewrite (eval_expr_deterministic _ _ _ _ _ _ _ H H9).  trivial.
          inv K2; simpl in *; try contradiction. 
                  rewrite (eval_expr_deterministic _ _ _ _ _ _ _ H H12) in *. 
                  rewrite (eval_expr_deterministic _ _ _ _ _ _ _ H0 H13) in *. 
                  rewrite (Mem_storev_deterministic _ _ _ _ _ _ H1 H14)  in *. trivial.
  (*Continue in similar fashion*)
Admitted.

Lemma CMin_corestep_fun: forall ge m q m1 q1 m2 q2, 
       CMin_corestep ge q m q1 m1 ->
       CMin_corestep ge q m q2 m2 -> 
          (q1, m1) = (q2, m2).
  Proof.
    intros.
    destruct q; destruct q1; destruct q2; try inv H; try inv H0;
     try assert (X:= Cminor_step_fun _ _ _ _ H1 _ _ H); inv X; trivial.
  Qed.

Lemma CMin_allowed_modifications :
    forall ge q m q' m',
      CMin_corestep ge q m q' m' ->
      allowed_core_modification m m'.
  Proof. intros. assert (NotAtExt:= CMin_corestep_not_at_external _ _ _ _ _ H).
      destruct q; destruct q'; inv H.
         inv H0; try apply allowed_core_modification_refl.
         (*storev*)
              unfold Mem.storev in H15. destruct vaddr; try inv H15. eapply store_allowed_core_mod; eauto.
        (*external_call*) simpl in NotAtExt. (*wso we actuall have a builtin*)
                 assert (Pr:= external_call_spec ef). inv Pr.
                 split; intros.
                  eapply external_call_mem_forward; eauto.
                 split; intros. admit. 
                 split; intros.  admit. admit. 
      inv H0; try apply allowed_core_modification_refl. eapply free_allowed_core_mod; eassumption.
      inv H0; try eapply free_allowed_core_mod; eassumption.
      inv H0. eapply alloc_allowed_core_mod; eassumption.
      inv H0; try apply allowed_core_modification_refl. 
Qed.

Definition CMin_CompcertCoreSem : CompcertCoreSem genv CMin_core (list (ident * globvar unit)).
  eapply @Build_CompcertCoreSem with (csem:=CMin_core_sem). 
    apply CMin_corestep_fun.
    apply CMin_allowed_modifications.
Defined.

Lemma CMin_corestep_2_CompCertStep: forall (ge : genv)  (q : CMin_core) (m : mem) (q' : CMin_core) (m' : mem) ,
   CMin_corestep ge q m q' m' -> 
   exists t, step ge (ToState q m) t (ToState q' m').
Proof.
  intros. destruct q; destruct q'; induction H; simpl; eauto. 
Qed.

Lemma CompCertStep_CMin_corestep: forall (ge : genv)  (q : CMin_core) (m : mem) (q' : CMin_core) (m' : mem)  t,
   step ge (ToState q m) t (ToState q' m') ->
   CMin_at_external q = None ->
   CMin_corestep ge q m q' m'.
Proof.
  intros. destruct q; destruct q'; simpl in *; try eexists; try eassumption.
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
     inv H.
     inv H. inv H0.
     inv H.
     inv H.
Qed.

Lemma CMin_corestepSN_2_CompCertStepStar: forall (ge : genv) n (q : CMin_core) (m : mem) (q' : CMin_core) (m' : mem),
   corestepN CMin_CompcertCoreSem ge n q m q' m' -> 
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

Lemma CompCertStep_2_CMin_corestep: forall (ge : genv)  (q : CMin_core) (m : mem) t c',
   step ge (ToState q m) t c' ->
   CMin_at_external q = None ->
   exists q', exists m', c' = ToState q' m' /\ CMin_corestep ge q m q' m'.
Proof.
  intros. destruct q; destruct c'; simpl in *.
     exists (CMin_State f0 s0 k0 sp0 e0). exists m0; simpl. split. trivial. eexists. eassumption.
     exists (CMin_Callstate f0 args  k0). exists m0; simpl. split. trivial. eexists. eassumption.
     exists (CMin_Returnstate v k0). exists m0; simpl. split. trivial. eexists. eassumption.
     exists (CMin_State f0 s k0 sp e). exists m0; simpl. split. trivial. eexists. eassumption.
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

(*
Lemma CompCertStepStar_2_CMin_corestepStar: forall (ge : genv)  (q : CMin_core) (m : mem) c' t,
   Smallstep.star step ge (ToState q m) t c' ->
  exists q', exists m', c' =  ToState q' m' /\
            corestep_star CMin_CompcertCoreSem   ge q m q' m'.
  Proof. intros.
     remember (ToState q m)  as c. 
    generalize dependent m. generalize dependent q.
     induction H; intros; subst.
         exists q. exists m. split. reflexivity.  exists O. simpl. reflexivity.
    clear H0.
       assert (X: CMin_at_external q = None). admit. (*doesn't hold ie result only hoilds if all intermediate states are not atexternal*)
       destruct (CompCertStep_2_CMin_corestep _ _ _ _ _ H X) as [qq' [mm' [? Step]]]. subst.
       destruct (IHstar _ _ (refl_equal _)) as [q' [m' [? Y]]]. subst. clear IHstar H.
       exists q'. exists m'. split; trivial.
       eapply corestep_star_trans.
           eapply corestep_star_one. eassumption.
           assumption.
Qed.

Lemma CompCertStepPlus_2_CMin_corestepPlus: forall (ge : genv)  (q : CMin_core) (m : mem) c' t,
   Smallstep.plus step ge (ToState q m) t c' ->
   CMin_at_external q = None ->
   exists q', exists m', c' =  ToState q' m' /\
            corestep_plus CMin_CompcertCoreSem   ge q m q' m'.
  Proof. intros.
    inv H.
    destruct (CompCertStep_2_CMin_corestep _ _ _ _ _ H1 H0) as [q'' [m'' [X Step]]]. subst. clear H0 H1.
    destruct (CompCertStepStar_2_CMin_corestepStar _ _ _ _ _ H2) as [q' [m' [? X]]]. subst.
    exists q'. exists m'. split. trivial.
    eapply corestep_plus_star_trans; try eassumption.
         eapply corestep_plus_one. assumption.
Qed.
  *)
     
