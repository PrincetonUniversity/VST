Load loadpath.
Require Import 
 msl.base 
 veric.sim veric.step_lemmas veric.base veric.expr
 veric.extension veric.extspec.

Set Implicit Arguments.
Local Open Scope nat_scope.

Module CompCertModule. Section CompCertModule.
Variables F V C: Type.

Inductive Sig: Type := Make: forall
 (ge: Genv.t F V)
 (csem: CoreSemantics (Genv.t F V) C mem (list (ident * globdef F V))),
 Sig.

End CompCertModule. End CompCertModule.

Definition get_module_genv F V C (ccm: CompCertModule.Sig F V C): Genv.t F V :=
  match ccm with CompCertModule.Make g _ => g end.

Definition get_module_csem F V C (ccm: CompCertModule.Sig F V C) :=
  match ccm with CompCertModule.Make _ sem => sem end.

Inductive frame (cT: nat -> Type) (num_modules: nat): Type := mkFrame: 
 forall (i: nat) (PF: i < num_modules) (c: cT i), frame cT num_modules.
Implicit Arguments mkFrame [cT num_modules].

Definition call_stack (cT: nat -> Type) (num_modules: nat) := list (frame cT num_modules).

Section LinkerCoreState.
Variables (F V: Type) (ge: Genv.t F V).

Inductive linker_corestate: Type := mkLinkerCoreState: forall
 (cT: nat -> Type)
 (fT: nat -> Type)
 (vT: nat -> Type)
 (num_modules: nat)
 (procedure_linkage_table: ident -> option nat)
 (plt_ok: 
   forall (id: ident) (i: nat), 
   procedure_linkage_table id = Some i -> i < num_modules)
 (stack: call_stack cT num_modules)
 (modules: forall i: nat, i < num_modules -> CompCertModule.Sig (fT i) (vT i) (cT i)),
 linker_corestate.

Definition get_cT (s: linker_corestate) :=
  match s with mkLinkerCoreState cT _ _ _ _ _ _ _ => cT end.
Definition get_fT (s: linker_corestate) :=
  match s with mkLinkerCoreState _ fT _ _ _ _ _ _ => fT end.
Definition get_vT (s: linker_corestate) :=
  match s with mkLinkerCoreState _ _ vT _ _ _ _ _ => vT end.
Definition get_num_modules (s: linker_corestate): nat :=
  match s with mkLinkerCoreState _ _ _ n _ _ _ _ => n end.
Definition get_PLT (s: linker_corestate): ident -> option nat :=
  match s with mkLinkerCoreState _ _ _ _ plt _ _ _ => plt end.
Program Definition get_PLT_ok (s: linker_corestate):
   forall (id: ident) (i: nat), get_PLT s id = Some i -> i < get_num_modules s :=
  match s with mkLinkerCoreState _ _ _ _ _ plt_ok _ _ => plt_ok end.
Definition get_callstack (s: linker_corestate): call_stack (get_cT s) (get_num_modules s) :=
  match s with mkLinkerCoreState _ _ _ _ _ _ stk _ => stk end.
Program Definition get_modules (s: linker_corestate): 
   forall i: nat, i < get_num_modules s -> 
   CompCertModule.Sig (get_fT s i) (get_vT s i) (get_cT s i) :=
  match s with mkLinkerCoreState _ _ _ _ _ _ _ m => m end.

End LinkerCoreState.
Implicit Arguments mkLinkerCoreState [].
Implicit Arguments get_modules [].

Definition genvs_agree (F1 F2 V1 V2: Type) (ge1: Genv.t F1 V1) (ge2: Genv.t F2 V2) :=
  (forall id: ident, Genv.find_symbol ge1 id=Genv.find_symbol ge2 id) /\
  (forall b v1 v2,
    ZMap.get b (Genv.genv_vars ge1) = Some v1 -> ZMap.get b (Genv.genv_vars ge2) = Some v2 ->  
    gvar_init v1=gvar_init v2).

Section LinkerCoreStep.
Variables (F V: Type).

Inductive linker_corestep: Genv.t F V -> linker_corestate -> mem -> linker_corestate -> mem -> Prop :=
(** coresteps of the 'top' core *)                    
| link_step: forall ge cT fT vT num_modules PLT PLT_OK (stack: call_stack cT num_modules) modules
                    i c m (pf_i: i < num_modules) c' m',
  (forall (k: nat) (pf_k: k<num_modules), genvs_agree ge (get_module_genv (modules k pf_k))) ->
  (forall (k: nat) (pf_k: k<num_modules), genvs_domain_eq ge (get_module_genv (modules k pf_k))) ->
  corestep (get_module_csem (modules i pf_i)) (get_module_genv (modules i pf_i)) c m c' m' ->
  linker_corestep ge
   (mkLinkerCoreState cT fT vT num_modules PLT PLT_OK (mkFrame i pf_i c :: stack) modules) m
   (mkLinkerCoreState cT fT vT num_modules PLT PLT_OK (mkFrame i pf_i c' :: stack) modules) m'

(** 'link' steps *)
| link_call: forall ge cT fT vT num_modules (PLT: ident -> option nat) stack modules
                    i j args id sig b (c: cT i) m (pf_i: i < num_modules) c'
   (PLT_OK: forall (id: ident) (i: nat), PLT id = Some i -> i < num_modules)
   (LOOKUP: PLT id = Some j)
   (AT_EXT: at_external (get_module_csem (modules i pf_i)) c = 
     Some (EF_external id sig, sig, args)),
  (forall (k: nat) (pf_k: k<num_modules), genvs_agree ge (get_module_genv (modules k pf_k))) ->
  (forall (k: nat) (pf_k: k<num_modules), genvs_domain_eq ge (get_module_genv (modules k pf_k))) ->
  Genv.find_symbol ge id = Some b -> 
  make_initial_core 
   (get_module_csem (modules j (PLT_OK id j LOOKUP)))
   (get_module_genv (modules j (PLT_OK id j LOOKUP))) (Vptr b (Int.repr 0)) args = Some c' -> 

  linker_corestep ge
   (mkLinkerCoreState cT fT vT num_modules PLT PLT_OK (mkFrame i pf_i c :: stack) modules) m
   (mkLinkerCoreState cT fT vT num_modules PLT PLT_OK
    (mkFrame j (PLT_OK id j LOOKUP) c' :: mkFrame i pf_i c :: stack) modules) m

(** 'return' steps *)
| link_return: forall ge cT fT vT num_modules (PLT: ident -> option nat) stack modules
                      i j id c m (pf_i: i < num_modules) c' c'' retv
   (PLT_OK: forall (id: ident) (i: nat), PLT id = Some i -> i < num_modules)
   (LOOKUP: PLT id = Some j)
   (HALTED: safely_halted (get_module_csem (modules j (PLT_OK id j LOOKUP))) c' = Some retv),
  (forall (k: nat) (pf_k: k<num_modules), genvs_agree ge (get_module_genv (modules k pf_k))) ->
  (forall (k: nat) (pf_k: k<num_modules), genvs_domain_eq ge (get_module_genv (modules k pf_k))) ->
  after_external (get_module_csem (modules i pf_i)) (Some retv) c = Some c'' -> 
  linker_corestep ge
   (mkLinkerCoreState cT fT vT num_modules PLT PLT_OK 
     (mkFrame j (PLT_OK id j LOOKUP) c' :: mkFrame i pf_i c :: stack) modules) m
   (mkLinkerCoreState cT fT vT num_modules PLT PLT_OK (mkFrame i pf_i c'' :: stack) modules) m.

End LinkerCoreStep.

Definition linker_at_external (s: linker_corestate) := 
  match s with
  | mkLinkerCoreState cT fT vT num_modules PLT PLT_OK nil modules => None
  | mkLinkerCoreState cT fT vT num_modules PLT PLT_OK (mkFrame i pf_i c :: call_stack) modules =>
     match at_external (get_module_csem (modules i pf_i)) c with
     | Some (EF_external id sig, ef_sig, args) => 
       match PLT id with 
       | None => Some (EF_external id sig, ef_sig, args)
       | Some module_id => None
       end
     | Some (ef, sig, args) => Some (ef, sig, args)
     | None => None
     end
  end.

Definition linker_after_external (retv: option val) (s: linker_corestate) :=
  match s with
  | mkLinkerCoreState cT fT vT num_modules PLT PLT_OK nil modules => None
  | mkLinkerCoreState cT fT vT num_modules PLT PLT_OK (mkFrame i pf_i c :: call_stack) modules =>
     match at_external (get_module_csem (modules i pf_i)) c with
     | None => None
     | Some _ => match after_external (get_module_csem (modules i pf_i)) retv c with
                 | None => None
                 | Some c' => Some (mkLinkerCoreState cT fT vT num_modules PLT PLT_OK 
                                     (mkFrame i pf_i c' :: call_stack) modules)
                 end
     end
   end.

Definition linker_safely_halted (s: linker_corestate) :=
  match s with
  | mkLinkerCoreState cT fT vT num_modules PLT PLT_OK nil modules => None
  | mkLinkerCoreState cT fT vT num_modules PLT PLT_OK (mkFrame i pf_i c :: nil) modules =>
     safely_halted (get_module_csem (modules i pf_i)) c
  | mkLinkerCoreState cT fT vT num_modules PLT PLT_OK (mkFrame i pf_i c :: call_stack) modules => None
  end.

Definition main_id := 1%positive. (*hardcoded*)

Section LinkerCoreSemantics.
Variables (F V: Type).
Variables
 (init_cT: nat -> Type)
 (init_fT: nat -> Type)
 (init_vT: nat -> Type)
 (init_num_modules: nat)
 (init_procedure_linkage_table: ident -> option nat)
 (init_plt_ok: 
   forall (id: ident) (i: nat), 
   init_procedure_linkage_table id = Some i -> i < init_num_modules)
 (init_stack: call_stack init_cT init_num_modules)
 (init_modules: forall i: nat, i < init_num_modules -> 
   CompCertModule.Sig (init_fT i) (init_vT i) (init_cT i)).

Definition linker_initial_mem (ge: Genv.t F V) (m: mem) (init_data: list (ident * globdef F V)) := 
  Genv.alloc_globals ge Mem.empty init_data = Some m.

Program Definition linker_make_initial_core (ge: Genv.t F V) (f: val) (args: list val) :=
  match f, Genv.find_symbol ge main_id with
  | Vptr b ofs, Some b' => 
    if Z_eq_dec b b' then 
       match init_procedure_linkage_table main_id with
       | None => None (** no module defines 'main' *)
       | Some i => 
         match make_initial_core (get_module_csem (init_modules (@init_plt_ok main_id i _))) 
                 (get_module_genv (init_modules (@init_plt_ok main_id i _))) f args with
         | None => None
         | Some c => Some (mkLinkerCoreState init_cT init_fT init_vT init_num_modules 
                       init_procedure_linkage_table init_plt_ok (mkFrame i _ c :: nil) init_modules)
         end
       end
     else None
   | _, _ => None (** either no 'main' was defined or [f] is not a [Vptr] *)
   end.
Next Obligation. solve[eapply init_plt_ok; eauto]. Qed.

Program Definition linker_core_semantics: 
  CoreSemantics (Genv.t F V) linker_corestate mem (list (ident * globdef F V)) :=
 Build_CoreSemantics _ _ _ _ 
  linker_initial_mem 
  linker_make_initial_core
  linker_at_external
  linker_after_external
  linker_safely_halted
  (@linker_corestep F V) _ _ _ _.
Next Obligation.
inv H.
apply corestep_not_at_external in H2.
solve[simpl; rewrite H2; auto].
solve[simpl; rewrite AT_EXT, LOOKUP; auto].
simpl.
destruct (at_external_halted_excl (get_module_csem (modules j (PLT_OK id j LOOKUP))) c')
 as [H3|H3].
solve[rewrite H3; auto].
solve[rewrite H3 in HALTED; congruence].
Qed.
Next Obligation.
inv H.
apply corestep_not_halted in H2.
simpl; destruct stack; auto.
destruct (at_external_halted_excl (get_module_csem (modules i pf_i)) c) 
 as [H4|H4].
simpl; destruct stack; auto.
solve[rewrite AT_EXT in H4; congruence].
solve[simpl; destruct stack; auto].
solve[auto].
Qed.
Next Obligation.
destruct q; simpl.
destruct stack; auto.
destruct f; auto.
case_eq (at_external (get_module_csem (modules i PF)) c); [intros [[ef sig] args]|intros].
destruct ef; auto.
intros.
destruct (procedure_linkage_table name).
solve[left; auto].
destruct stack; auto.
destruct (at_external_halted_excl (get_module_csem (modules i PF)) c) 
 as [H3|H3].
solve[rewrite H in H3; congruence].
solve[right; auto].
intros H1; destruct (at_external_halted_excl (get_module_csem (modules i PF)) c) 
 as [H3|H3].
solve[rewrite H1 in H3; congruence].
solve[destruct stack; auto].
intros H1; destruct (at_external_halted_excl (get_module_csem (modules i PF)) c) 
 as [H3|H3].
solve[rewrite H1 in H3; congruence].
solve[destruct stack; auto].
intros H1; destruct (at_external_halted_excl (get_module_csem (modules i PF)) c) 
 as [H3|H3].
solve[rewrite H1 in H3; congruence].
solve[destruct stack; auto].
intros H1; destruct (at_external_halted_excl (get_module_csem (modules i PF)) c) 
 as [H3|H3].
solve[rewrite H1 in H3; congruence].
solve[destruct stack; auto].
intros H1; destruct (at_external_halted_excl (get_module_csem (modules i PF)) c) 
 as [H3|H3].
solve[rewrite H1 in H3; congruence].
solve[destruct stack; auto].
intros H1; destruct (at_external_halted_excl (get_module_csem (modules i PF)) c) 
 as [H3|H3].
solve[rewrite H1 in H3; congruence].
solve[destruct stack; auto].
intros H1; destruct (at_external_halted_excl (get_module_csem (modules i PF)) c) 
 as [H3|H3].
solve[rewrite H1 in H3; congruence].
solve[destruct stack; auto].
intros H1; destruct (at_external_halted_excl (get_module_csem (modules i PF)) c) 
 as [H3|H3].
solve[rewrite H1 in H3; congruence].
solve[destruct stack; auto].
intros H1; destruct (at_external_halted_excl (get_module_csem (modules i PF)) c) 
 as [H3|H3].
solve[rewrite H1 in H3; congruence].
solve[destruct stack; auto].
intros H1; destruct (at_external_halted_excl (get_module_csem (modules i PF)) c) 
 as [H3|H3].
solve[rewrite H1 in H3; congruence].
solve[destruct stack; auto].
solve[left; auto].
Qed.
Next Obligation.
destruct q; simpl in H|-*.
destruct stack; try solve[inversion H].
destruct f; try solve[inversion H].
case_eq (at_external (get_module_csem (modules i PF)) c). 
intros [[ef sig] args] H1.
rewrite H1 in H.
case_eq (after_external (get_module_csem (modules i PF)) retv c).
intros c' H2; rewrite H2 in H.
inv H; apply after_at_external_excl in H2.
simpl; rewrite H2; auto.
case_eq (after_external (get_module_csem (modules i PF)) retv c).
solve[intros c' H2; rewrite H2 in H; intro; congruence].
intros H2 H3.
solve[rewrite H2 in H; congruence].
solve[intros H1; rewrite H1 in H; congruence].
Qed.

End LinkerCoreSemantics.