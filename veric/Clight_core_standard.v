Require Import VST.sepcomp.semantics.
Require Import VST.veric.Clight_base.
Require Import VST.veric.Clight_lemmas.
Require compcert.common.Globalenvs.
Require Import compcert.common.Events.
Require Import compcert.cfrontend.Clight.

(*To prove memsem*)
Require Import VST.sepcomp.semantics.
Require Import VST.sepcomp.semantics_lemmas.
Require Import VST.sepcomp.mem_lemmas.

Inductive CC_core : Type :=
    CC_core_State : function ->
            statement -> cont -> env -> temp_env -> CC_core
  | CC_core_Callstate : fundef -> list val -> cont -> CC_core
  | CC_core_Returnstate : val -> cont -> CC_core.

Definition CC_core_to_CC_state (c:CC_core) (m:mem) : state :=
  match c with
     CC_core_State f st k e te => State f st k e te m
  |  CC_core_Callstate fd args k => Callstate fd args k m
  | CC_core_Returnstate v k => Returnstate v k m
 end.
Definition CC_state_to_CC_core (c:state): CC_core * mem :=
  match c with
     State f st k e te m => (CC_core_State f st k e te, m)
  |  Callstate fd args k m => (CC_core_Callstate fd args k, m)
  | Returnstate v k m => (CC_core_Returnstate v k, m)
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
             exists (CC_core_State f s k e le). exists m; reflexivity.
             exists (CC_core_Callstate fd args k). exists m; reflexivity.
             exists (CC_core_Returnstate res k). exists m; reflexivity.
  Qed.

Lemma CC_core_to_CC_state_inj: forall c m c' m',
     CC_core_to_CC_state c m = CC_core_to_CC_state c' m' -> (c',m')=(c,m).
  Proof. intros.
       apply  CC_core_CC_state_3 in H. rewrite  CC_core_CC_state_1 in H.  inv H. trivial.
  Qed.

Definition cl_halted (c: CC_core) : option val := None.

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
        Some (CC_core_State empty_function 
                    (Scall None
                                 (Etempvar 1%positive (type_of_fundef f))
                                 (map (fun x => Etempvar (fst x) (snd x))
                                      (params_of_types 2%positive
                                                       (params_of_fundef f))))
                     (Kseq (Sloop Sskip Sskip) Kstop)
             empty_env
             (temp_bindings 1%positive (v::args)))
      | _ => None end
    else None
  | _ => None
  end.

Definition stuck_signature : signature := mksignature nil None cc_default.

Definition cl_at_external (c: CC_core) : option (external_function * list val) :=
  match c with
  | CC_core_Callstate (External ef _ _ _) args _ => Some (ef, args)
  | CC_core_State _ (Sbuiltin _ ef _ args) _ _ _ => Some (EF_external "stuck" stuck_signature, nil)
  | _ => None
end.

Definition cl_after_external (vret: option val) (c: CC_core) : option CC_core :=
   match c with
   | CC_core_Callstate (External ef _ _ _) _ k => 
        Some (CC_core_Returnstate (match vret with Some v => v | _ => Vundef end) k)
   | _ => None
   end.

Definition cl_step ge (q: CC_core) (m: mem) (q': CC_core) (m': mem) : Prop :=
    cl_at_external q = None /\ 
     Clight.step ge (Clight.function_entry2 ge)
      (CC_core_to_CC_state q m) Events.E0 (CC_core_to_CC_state q' m').

Lemma cl_corestep_not_at_external:
  forall ge m q m' q', 
          cl_step ge q m q' m' -> cl_at_external q = None.
Proof.
  intros.
  unfold cl_step in H. destruct H; auto.  
Qed.

Lemma cl_corestep_not_halted :
  forall ge m q m' q', cl_step ge q m q' m' -> cl_halted q = None.
Proof.
  intros.
  simpl; auto.
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
    (fun c _ =>  False (*cl_halted c <> None*))
    (cl_step ge)
    _
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
    State f STEP k e le m = CC_core_to_CC_state c m' ->
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

Program Definition CLNC_memsem (ge: genv):
  @MemSem (*(Genv.t fundef type)*) CC_core.
apply Build_MemSem with (csem := cl_core_sem ge).
  intros.
  induction CS. simpl in H0.
  inversion H0;
  try solve [do 2 match goal with
    | [ H: State _ _ _ _ _ ?m = CC_core_to_CC_state _ _ |- _ ] => apply CC_core_to_State_mem in H
             end; subst; try apply mem_step_refl; trivial];
  destruct c; inv H1; destruct c'; inv H2;
  try apply mem_step_refl;
  try ( eapply mem_step_freelist; eassumption).
*
 inv H6.
 unfold Mem.storev in H2. apply Mem.store_storebytes in H2.
 eapply mem_step_storebytes; eauto.
 eapply mem_step_storebytes; eauto. 
*
  inv H.
*
 inv H3.
 clear - H5.
 induction H5.
 apply mem_step_refl.
 eapply mem_step_trans. eapply mem_step_alloc; eassumption. auto.
*
 inv H.
*
 simpl in H4. inv H4.
 apply mem_step_refl.
*
 inv H4.
*
 inv H4.
Qed.

Definition at_external c := cl_at_external (fst (CC_state_to_CC_core c)). (* Temporary definition for compatibility between CompCert 3.3 and new-compcert *)

