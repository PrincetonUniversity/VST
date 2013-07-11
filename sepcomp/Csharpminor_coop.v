Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import compcert.common.Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.

Require Import sepcomp.Csharpminor.
Require Import sepcomp.mem_lemmas. (*for mem_forward and wd_mem*)
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
        Vptr b i => if Int.eq_dec i  Int.zero 
                            then 
                            match Genv.find_funct_ptr ge b with
                              None => None
                            | Some f => match funsig f with
                                                   {| sig_args := sargs; sig_res := sres |} => 
                                                       match sargs, sres with 
                                                          nil, Some Tint => Some (CSharpMin_Callstate f nil Kstop) (*args = nil???*)
                                                       | _ , _ => None
                                                       end
                                                 end
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

Lemma alloc_variables_mem_wd: forall vars m e e2 m'
      (M: alloc_variables e m vars e2 m')
      (WD: mem_wd m), mem_wd m'.
Proof. intros.
  induction M; trivial.
  apply IHM.
  eapply mem_wd_alloc; eassumption.
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


Definition valid_env (e:Csharpminor.env) (m:mem) :=
  forall id b z , Maps.PTree.get id e = Some (b, z) ->
                  Mem.valid_block m b. 

Definition valid_tempenv (t:temp_env) (m:mem) :=
  forall id v , Maps.PTree.get id t = Some v -> val_valid v m.

Lemma eval_var_addr_val_valid: forall ge e id b m
   (VE: valid_env e m) (GE: valid_genv ge m),
   eval_var_addr ge e id b -> Mem.valid_block m b.
Proof. intros.
  inv H.
    eapply VE; eassumption.
    eapply GE; eassumption.
  Qed.

Lemma eval_expr_val_valid:
  forall ge te e m
    (TE: valid_tempenv te m)
    (VE: valid_env e m) (GE: valid_genv ge m)
    (WD : mem_wd m),
    (forall a v, Csharpminor.eval_expr ge e te m a v -> val_valid v m). 
Proof.
 intros ge te e m TE VE GE WD.
 apply eval_expr_ind; simpl; intros.
    eapply TE; eassumption.
    eapply eval_var_addr_val_valid; eassumption.
    destruct cst; try inv H; simpl in *; trivial.

    admit. (*unary operators - should be similar to Clight case*)
    admit. (*binary operators - should be similar to Clight case*)
      
  destruct v1; try inv H1; simpl in *.
    eapply mem_wd_load; eassumption.
Qed. 

Definition valid_corestate (c: CSharpMin_core) (m:mem) : Prop :=
  match c with
    CSharpMin_State f s k e le => valid_env e m /\ valid_tempenv le m
  | CSharpMin_Callstate f args k => 
            (forall v, In v args -> val_valid v m) 
  | CSharpMin_Returnstate v k => val_valid v m  
  end.

Definition coopstep g c m c' m' :=
   valid_genv g m /\ (*valid_genv g m' /\*)
   valid_corestate c m /\ (*valid_corestate c' m' /\*)
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
  @Build_CoreSemantics _ _ _ (*_*)
    (*cl_init_mem*)
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
(*A global assumption we need on external calls, in particular builtins*)
Parameter external_call_mem_wd:
  forall (ef : external_function) (F V : Type) (ge : Genv.t F V)
    (vargs : list val) (m1 : mem) (t : trace) (vres : val) (m2 : mem),
    external_call ef ge vargs m1 t vres m2 -> mem_wd m1 -> mem_wd m2.
 

Lemma csharpmin_coop_forward : forall g c m c' m' (CS: coopstep g c m c' m'), 
      mem_lemmas.mem_forward m m'.
Proof. intros. destruct CS as [GE [VS Step]].
  eapply CSharpMin_forward. apply Step.
Qed.

Lemma csharpmin_coop_mem_wd: forall g c m c' m'
  (CS: coopstep g c m c' m') (WD: mem_wd m), mem_wd m'.
Proof. intros. destruct CS as [GE [VS Step]].
   unfold CSharpMin_corestep in Step. 
   destruct c; destruct c'; simpl in *; try contradiction.
   destruct VS as [VE VSP].   
     destruct Step as [t CS].
       inv CS; simpl in *; try eauto.
       destruct vaddr; simpl in H14; inv H14. 
         eapply mem_wd_store; try eassumption.
         eapply eval_expr_val_valid; eassumption.
       eapply external_call_mem_wd; eassumption. 
   destruct VS as [VE VSP].    
     destruct Step as [t CS].
       inv CS; simpl in *; try eauto.
   destruct VS as [VE VSP].    
     destruct Step as [t CS].
       inv CS; simpl in *; try eauto.
       eapply freelist_mem_wd; eassumption.
       eapply freelist_mem_wd; eassumption.
       eapply freelist_mem_wd; eassumption.
   destruct Step as [t CS].
       inv CS; simpl in *; try eauto.
       eapply alloc_variables_mem_wd; eassumption.
   destruct Step as [t CS].
       inv CS; simpl in *; try eauto.
Qed. 

Program Definition csharpmin_coop_sem : 
  CoopCoreSem Csharpminor.genv CSharpMin_core.
apply Build_CoopCoreSem with (coopsem := csharpmin_core_sem).
  apply csharpmin_coop_forward.
  apply csharpmin_coop_mem_wd.
Qed.
(*
Lemma CSharpMin_corestepSN_2_CompCertStepStar: forall (ge : genv) n (q : CSharpMin_core) (m : mem) (q' : CSharpMin_core) (m' : mem),
   corestepN CSharpMin_CompcertCoreSem ge n q m q' m' -> 
   exists t, Smallstep.star step ge (ToState q m) t (ToState q' m').
Proof.
  intros ge n.
  induction n; simpl; intros.
      inv H. eexists. apply Smallstep.star_refl.
  destruct H as [c2 [m2 [Step1 Steps]]].
     destruct (IHn _ _ _ _ Steps) as [t Ht].
     destruct (CSharpMin_corestep_2_CompCertStep _ _ _ _ _ Step1) as [t1 Ht1].
     eexists. econstructor. eassumption. eassumption.
       reflexivity.
Qed.
 
Lemma CSharpMin_corestepSN_2_CompCertStepPlus: forall (ge : genv) n (q : CSharpMin_core) (m : mem) (q' : CSharpMin_core) (m' : mem),
   corestepN CSharpMin_CompcertCoreSem ge (S n) q m q' m' -> 
   exists t, Smallstep.plus step ge (ToState q m) t (ToState q' m').
Proof.
  intros.
  destruct H as [c2 [m2 [H X]]].
  destruct (CSharpMin_corestep_2_CompCertStep _ _ _ _ _ H) as [t1 Ht1]. clear H.
  destruct (CSharpMin_corestepSN_2_CompCertStepStar _ _ _ _ _ _ X) as [t2 Ht2]. clear X.
  eexists. econstructor. eassumption. eassumption. reflexivity.
Qed. 

Lemma CSharpMin_corestep_plus_2_CompCertStep_plus: forall (ge : genv)  (q : CSharpMin_core) (m : mem) (q' : CSharpMin_core) (m' : mem) ,
   corestep_plus CSharpMin_CompcertCoreSem ge q m q' m' -> 
   exists t, Smallstep.plus step ge (ToState q m) t (ToState q' m').
Proof.
  intros. destruct H as [n Hn].
  eapply CSharpMin_corestepSN_2_CompCertStepPlus. apply Hn. 
Qed.

Lemma CSharpMin_corestep_star_2_CompCertStep_star: forall (ge : genv)  (q : CSharpMin_core) (m : mem) (q' : CSharpMin_core) (m' : mem) ,
   corestep_star CSharpMin_CompcertCoreSem ge q m q' m' -> 
   exists t, Smallstep.star step ge (ToState q m) t (ToState q' m').
Proof.
  intros. destruct H as [n Hn].
  eapply CSharpMin_corestepSN_2_CompCertStepStar. apply Hn. 
Qed.

Lemma CompCertStep_2_CSharpMin_corestep: forall (ge : genv)  (q : CSharpMin_core) (m : mem) t c',
   step ge (ToState q m) t c' ->
   CSharpMin_at_external q = None ->
   exists q', exists m', c' = ToState q' m' /\ CSharpMin_corestep ge q m q' m'.
Proof.
  intros. destruct q; destruct c'; simpl in *.
     exists (CSharpMin_State f0 s0 k0 e0 le0). exists m0; simpl. split. trivial. eexists. eassumption.
     exists (CSharpMin_Callstate f0 args  k0). exists m0; simpl. split. trivial. eexists. eassumption.
     exists (CSharpMin_Returnstate v k0). exists m0; simpl. split. trivial. eexists. eassumption.
     exists (CSharpMin_State f0 s k0 e le). exists m0; simpl. split. trivial. eexists. eassumption.
     inv H.
     inv H. inv H0. 
     exists (CSharpMin_State f s k0 e le). exists m0; simpl. split. trivial. eexists. eassumption.
     inv H. 
     inv H.
Qed.

Lemma CSharpMin_core2state_injective: forall q m q' m', 
 ToState q m = ToState q' m' -> q'=q /\ m'=m.
  Proof. intros.
    destruct q; destruct q'; simpl in *; inv H; split; trivial.
  Qed.*)
(*
Lemma CompCertStepStar_2_CSharpMin_corestepStar: forall (ge : genv)  (q : CSharpMin_core) (m : mem) c' t,
   Smallstep.star step ge (ToState q m) t c' ->
  exists q', exists m', c' =  ToState q' m' /\
            corestep_star CSharpMin_CompcertCoreSem   ge q m q' m'.
  Proof. intros.
     remember (ToState q m)  as c. 
    generalize dependent m. generalize dependent q.
     induction H; intros; subst.
         exists q. exists m. split. reflexivity.  exists O. simpl. reflexivity.
    clear H0.
       assert (X: CSharpMin_at_external q = None). admit. (*this admit is ok - Lemma comented out doesn't hold ie result only hoilds if all intermediate states are not atexternal*)
       destruct (CompCertStep_2_CSharpMin_corestep _ _ _ _ _ H X) as [qq' [mm' [? Step]]]. subst.
       destruct (IHstar _ _ (refl_equal _)) as [q' [m' [? Y]]]. subst. clear IHstar H.
       exists q'. exists m'. split; trivial.
       eapply corestep_star_trans.
           eapply corestep_star_one. eassumption.
           assumption.
Qed.

Lemma CompCertStepPlus_2_CSharpMin_corestepPlus: forall (ge : genv)  (q : CSharpMin_core) (m : mem) c' t,
   Smallstep.plus step ge (ToState q m) t c' ->
   CSharpMin_at_external q = None ->
   exists q', exists m', c' =  ToState q' m' /\
            corestep_plus CSharpMin_CompcertCoreSem   ge q m q' m'.
  Proof. intros.
    inv H.
    destruct (CompCertStep_2_CSharpMin_corestep _ _ _ _ _ H1 H0) as [q'' [m'' [X Step]]]. subst. clear H0 H1.
    destruct (CompCertStepStar_2_CSharpMin_corestepStar _ _ _ _ _ H2) as [q' [m' [? X]]]. subst.
    exists q'. exists m'. split. trivial.
    eapply corestep_plus_star_trans; try eassumption.
         eapply corestep_plus_one. assumption.
Qed.
*)    
     
(*
(*Not sure whether this holds, but I do assume the leamms below, Csharpminor_step_fun to hold...*)
Parameter Mem_freelist_deterministic: forall m e m1 m2,
                   Mem.free_list m (blocks_of_env e)  = Some m1 ->
                   Mem.free_list m (blocks_of_env e) = Some m2 -> m1=m2.

Parameter eval_expr_deterministic: forall ge sp e m a v1 v2,
                eval_expr ge sp e m a v1 ->
                eval_expr ge sp e m a v2 -> v1=v2.

Parameter  exec_assign_deterministic: forall ge e m id v m1 m2,
                  exec_assign ge e m id v m1 -> exec_assign ge e m id v m2 -> m1=m2.

Parameter Mem_storev_deterministic: forall ch m a v m1 m2,
                Mem.storev ch m a v = Some m1 -> Mem.storev ch m a v = Some m2 -> m1 = m2.

Lemma eval_exprlist_deterministic: forall ge sp e m a v1 v2,
                eval_exprlist ge sp e m a v1 ->
                eval_exprlist ge sp e m a v2 -> v1=v2.
  intros until a. induction a; simpl; intros. inv H. inv H0. trivial.
      inv H. inv H0. rewrite (eval_expr_deterministic _ _ _ _ _ _ _ H3 H2). rewrite (IHa _ _ H5 H6). trivial.
Qed.

Lemma Csharpminor_step_fun: forall ge q q1 t1
 (K1: Csharpminor.step ge q t1 q1) q2 t2 (K2:Csharpminor.step ge q t2 q2) c m
  (Hq: q = ToState c m) (Hext: CSharpMin_at_external c = None), q1 = q2.
  Proof. intros g1 q q1 t1 K1.
     induction K1; intros.
          inv K2; simpl in *; try contradiction. trivial.
          inv K2; simpl in *; try contradiction. trivial.
          inv K2; simpl in *; try contradiction. rewrite (Mem_freelist_deterministic _ _ _ _ H1 H11). trivial.
          inv K2; simpl in *; try contradiction. rewrite (eval_expr_deterministic _ _ _ _ _ _ _ H H10) in *. rewrite (exec_assign_deterministic _ _ _ _ _ _ _ H0 H11). trivial.
          inv K2; simpl in *; try contradiction. rewrite (eval_expr_deterministic _ _ _ _ _ _ _  H H9). trivial.
          inv K2; simpl in *; try contradiction. rewrite (eval_expr_deterministic _ _ _ _ _ _ _ H13 H0) in *.  rewrite (eval_expr_deterministic _ _ _ _ _ _ _ H12 H) in *.
                                                  rewrite (Mem_storev_deterministic _ _ _ _ _ _ H1 H14). trivial.
          inv K2; simpl in *; try contradiction. rewrite (eval_expr_deterministic _ _ _ _ _ _ _ H14 H) in *. rewrite H16 in H1. inv H1.  rewrite (eval_exprlist_deterministic _ _ _ _ _ _ _ H15 H0) in *. trivial. 
          inv K2; simpl in *; try contradiction.
              destruct c; unfold ToState in *; try inv Hq. 
                  
  (*Continue in similar fashion*)
Admitted. this admit is ok - Lemma comented out
*)
(*
Lemma alloc_variables_det: forall vars e m e1 m1 e2 m2 
     (K1: alloc_variables e m vars e1 m1)  (K2: alloc_variables e m vars e2 m2), e1=e2 /\ m1 =m2.
  Proof. intro vars.
   induction vars; intros. inv K1. inv K2. auto.
     inv K1. inv K2.  
*)
(*
Lemma CSharpMin_corestep_fun: forall ge m q m1 q1 m2 q2
       (K1: CSharpMin_corestep ge q m q1 m1)
       (K2: CSharpMin_corestep ge q m q2 m2)
       (KK: CSharpMin_at_external q = None),
          (q1, m1) = (q2, m2).
  Proof.
    intros.
    destruct q; destruct q1; destruct q2; try inv K1; try inv K2; simpl in *. clear KK.
      Focus 10. destruct f.  inv H; inv H0.  
(*      Focus  destruct f. destruct q1. destruct K1. inv H.  Focus 2.
        inv H0; inv H; trivial.
           rewrite (eval_expr_deterministic _ _ _ _ _ _ _ H8 H9) in *. rewrite (exec_assign_deterministic _ _ _ _ _ _ _ H15 H17). trivial.
           rewrite (eval_expr_deterministic _ _ _ _ _ _ _ H8 H9) in *. trivial.
           rewrite (eval_expr_deterministic _ _ _ _ _ _ _ H15 H19) in *. rewrite (eval_expr_deterministic _ _ _ _ _ _ _ H10 H8) in *.  rewrite (Mem_storev_deterministic _ _ _ _ _ _ H16 H20). trivial.
          rewrite (eval_exprlist_deterministic _ _ _ _ _ _ _ H8 H10) in *. simpl in *.  trivial. 
     try assert (X:= Csharpminor_step_fun _ _ _ _ H1 _ _ H); inv X; trivial.
*)
Admitted. this admit is ok - Lemma comented out

Lemma CSharpMin_allowed_modifications :
    forall ge q m q' m',
      CSharpMin_corestep ge q m q' m' ->
      allowed_core_modification m m'.
  Proof. intros. assert (NotAtExt:= CSharpMin_corestep_not_at_external _ _ _ _ _ H).
      destruct q; destruct q'; inv H.
         inv H0; try apply allowed_core_modification_refl.
        (*assign*) admit. this admit is ok - Lemma comented out
         (*storev*)
              unfold Mem.storev in H15. destruct vaddr; try inv H15. eapply store_allowed_core_mod; eauto.
        (*external_call*) simpl in NotAtExt. (*wso we actuall have a builtin*)
                 assert (Pr:= external_call_spec ef). inv Pr.
                 split; intros.
                  eapply external_call_mem_forward; eauto.
                 split; intros. admit. this admit is ok - Lemma comented out
                 split; intros.  admit. admit. this admit is ok - Lemma comented out
      inv H0; try apply allowed_core_modification_refl.
      inv H0; try apply allowed_core_modification_refl. admit this admit is ok - Lemma comented out(*freelist*).  (* eapply free_allowed_core_mod; eassumption.*)
            admit. admit. this admit is ok - Lemma comented out
      inv H0. admit. this admit is ok - Lemma comented out(*bind/alloc*)(*  try eapply free_allowed_core_mod; eassumption.*)
      inv H0; try apply allowed_core_modification_refl. 
Qed.

Definition CSharpMin_CompcertCoreSem : CompcertCoreSem genv CSharpMin_core (list (ident * globvar var_kind)).
  eapply @Build_CompcertCoreSem with (csem:=CSharpMin_core_sem). 
      intros. apply (CSharpMin_corestep_fun ge m q _ _ _ _ H H0). 
        eapply  CSharpMin_corestep_not_at_external; eauto.
    apply CSharpMin_allowed_modifications.
Defined.*)