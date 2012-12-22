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

Section LinkerCoreSemantics.
Variables (F V: Type) (ge: Genv.t F V) (num_modules: nat).
Variables (cT fT vT: nat -> Type)
 (procedure_linkage_table: ident -> option nat)
 (plt_ok: 
   forall (id: ident) (i: nat), 
   procedure_linkage_table id = Some i -> i < num_modules)
 (modules: forall i: nat, i < num_modules -> CompCertModule.Sig (fT i) (vT i) (cT i)).

Implicit Arguments plt_ok [].

Inductive linker_corestate: Type := mkLinkerCoreState: forall
 (stack: call_stack cT num_modules)
 (stack_nonempty: length stack >= 1),
 linker_corestate.

Implicit Arguments mkLinkerCoreState [].

Definition genvs_agree (F1 F2 V1 V2: Type) (ge1: Genv.t F1 V1) (ge2: Genv.t F2 V2) :=
  (forall id: ident, Genv.find_symbol ge1 id=Genv.find_symbol ge2 id) /\
  (forall b v1 v2,
    ZMap.get b (Genv.genv_vars ge1) = Some v1 -> ZMap.get b (Genv.genv_vars ge2) = Some v2 ->  
    gvar_init v1=gvar_init v2).

Lemma length_cons {A: Type}: forall (a: A) (l: list A), length (a :: l) >= 1.
Proof. solve[intros; simpl; omega]. Qed.

Inductive linker_corestep: 
  Genv.t F V -> linker_corestate -> mem -> linker_corestate -> mem -> Prop :=
(** coresteps of the 'top' core *)                    
| link_step: forall ge (stack: call_stack cT num_modules) 
                    i c m (pf_i: i < num_modules) c' m' pf,
  (forall (k: nat) (pf_k: k<num_modules), genvs_agree ge (get_module_genv (modules pf_k))) ->
  (forall (k: nat) (pf_k: k<num_modules), genvs_domain_eq ge (get_module_genv (modules pf_k))) ->
  corestep (get_module_csem (modules pf_i)) (get_module_genv (modules pf_i)) c m c' m' ->
  linker_corestep ge
   (mkLinkerCoreState (mkFrame i pf_i c :: stack) pf) m
   (mkLinkerCoreState (mkFrame i pf_i c' :: stack) pf) m'

(** 'link' steps *)
| link_call: forall ge stack i j args id sig b (c: cT i) m (pf_i: i < num_modules) c' 
   (LOOKUP: procedure_linkage_table id = Some j)
   (AT_EXT: at_external (get_module_csem (modules pf_i)) c = 
     Some (EF_external id sig, sig, args)) pf,
  (forall (k: nat) (pf_k: k<num_modules), genvs_agree ge (get_module_genv (modules pf_k))) ->
  (forall (k: nat) (pf_k: k<num_modules), genvs_domain_eq ge (get_module_genv (modules pf_k))) ->
  Genv.find_symbol ge id = Some b -> 
  make_initial_core 
   (get_module_csem (modules (plt_ok id j LOOKUP)))
   (get_module_genv (modules (plt_ok id j LOOKUP))) (Vptr b (Int.repr 0)) args = Some c' -> 

  linker_corestep ge
   (mkLinkerCoreState (mkFrame i pf_i c :: stack) pf) m
   (mkLinkerCoreState 
     (mkFrame j (plt_ok id j LOOKUP) c' :: mkFrame i pf_i c :: stack) (length_cons _ _)) m

(** 'return' steps *)
| link_return: forall ge stack i j id c m (pf_i: i < num_modules) c' c'' retv
   (LOOKUP: procedure_linkage_table id = Some j)
   (HALTED: safely_halted (get_module_csem (modules (plt_ok id j LOOKUP))) c' = Some retv) pf,
  (forall (k: nat) (pf_k: k<num_modules), genvs_agree ge (get_module_genv (modules pf_k))) ->
  (forall (k: nat) (pf_k: k<num_modules), genvs_domain_eq ge (get_module_genv (modules pf_k))) ->
  after_external (get_module_csem (modules pf_i)) (Some retv) c = Some c'' -> 
  linker_corestep ge
   (mkLinkerCoreState 
     (mkFrame j (plt_ok id j LOOKUP) c' :: mkFrame i pf_i c :: stack) pf) m
   (mkLinkerCoreState (mkFrame i pf_i c'' :: stack) (length_cons _ _)) m.

Definition linker_at_external (s: linker_corestate) := 
  match s with
  | mkLinkerCoreState nil _ => None
  | mkLinkerCoreState (mkFrame i pf_i c :: call_stack) _ =>
     match at_external (get_module_csem (modules pf_i)) c with
     | Some (EF_external id sig, ef_sig, args) => 
       match procedure_linkage_table id with 
       | None => Some (EF_external id sig, ef_sig, args)
       | Some module_id => None
       end
     | Some (ef, sig, args) => Some (ef, sig, args)
     | None => None
     end
  end.

Definition linker_after_external (retv: option val) (s: linker_corestate) :=
  match s with
  | mkLinkerCoreState nil _ => None
  | mkLinkerCoreState (mkFrame i pf_i c :: call_stack) _ =>
     match at_external (get_module_csem (modules pf_i)) c with
     | None => None
     | Some _ => match after_external (get_module_csem (modules pf_i)) retv c with
                 | None => None
                 | Some c' => Some (mkLinkerCoreState 
                                     (mkFrame i pf_i c' :: call_stack) (length_cons _ _))
                 end
     end
   end.

Definition linker_safely_halted (s: linker_corestate) :=
  match s with
  | mkLinkerCoreState nil _ => None
  | mkLinkerCoreState (mkFrame i pf_i c :: nil) _ =>
     safely_halted (get_module_csem (modules pf_i)) c
  | mkLinkerCoreState (mkFrame i pf_i c :: call_stack) _ => None
  end.

Definition main_id := 1%positive. (*hardcoded*)

Definition linker_initial_mem (ge: Genv.t F V) (m: mem) (init_data: list (ident * globdef F V)) := 
  Genv.alloc_globals ge Mem.empty init_data = Some m.

Program Definition linker_make_initial_core (ge: Genv.t F V) (f: val) (args: list val) :=
  match f, Genv.find_symbol ge main_id with
  | Vptr b ofs, Some b' => 
    if Z_eq_dec b b' then 
       match procedure_linkage_table main_id with
       | None => None (** no module defines 'main' *)
       | Some i => 
         match make_initial_core (get_module_csem (modules (@plt_ok main_id i _))) 
                 (get_module_genv (modules (@plt_ok main_id i _))) f args with
         | None => None
         | Some c => Some (mkLinkerCoreState (mkFrame i _ c :: nil) (length_cons _ _))
         end
       end
     else None
   | _, _ => None (** either no 'main' was defined or [f] is not a [Vptr] *)
   end.
Next Obligation. solve[eapply plt_ok; eauto]. Qed.

Program Definition linker_core_semantics: 
  CoreSemantics (Genv.t F V) linker_corestate mem (list (ident * globdef F V)) :=
 Build_CoreSemantics _ _ _ _ 
  linker_initial_mem 
  linker_make_initial_core
  linker_at_external
  linker_after_external
  linker_safely_halted
  linker_corestep _ _ _ _.
Next Obligation.
inv H.
apply corestep_not_at_external in H2.
solve[simpl; rewrite H2; auto].
simpl; rewrite AT_EXT, LOOKUP; auto.
simpl.
destruct (at_external_halted_excl (get_module_csem (modules (plt_ok id j LOOKUP))) c')
 as [H3|H3].
solve[rewrite H3; auto].
solve[rewrite H3 in HALTED; congruence].
Qed.
Next Obligation.
inv H.
apply corestep_not_halted in H2.
simpl; destruct stack; auto.
destruct (at_external_halted_excl (get_module_csem (modules pf_i)) c) 
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
case_eq (at_external (get_module_csem (modules PF)) c); [intros [[ef sig] args]|intros].
destruct ef; auto.
intros.
destruct (procedure_linkage_table name).
solve[left; auto].
destruct stack; auto.
destruct (at_external_halted_excl (get_module_csem (modules PF)) c) 
 as [H3|H3].
solve[rewrite H in H3; congruence].
solve[right; auto].
intros H1; destruct (at_external_halted_excl (get_module_csem (modules PF)) c) 
 as [H3|H3].
solve[rewrite H1 in H3; congruence].
solve[destruct stack; auto].
intros H1; destruct (at_external_halted_excl (get_module_csem (modules PF)) c) 
 as [H3|H3].
solve[rewrite H1 in H3; congruence].
solve[destruct stack; auto].
intros H1; destruct (at_external_halted_excl (get_module_csem (modules PF)) c) 
 as [H3|H3].
solve[rewrite H1 in H3; congruence].
solve[destruct stack; auto].
intros H1; destruct (at_external_halted_excl (get_module_csem (modules PF)) c) 
 as [H3|H3].
solve[rewrite H1 in H3; congruence].
solve[destruct stack; auto].
intros H1; destruct (at_external_halted_excl (get_module_csem (modules PF)) c) 
 as [H3|H3].
solve[rewrite H1 in H3; congruence].
solve[destruct stack; auto].
intros H1; destruct (at_external_halted_excl (get_module_csem (modules PF)) c) 
 as [H3|H3].
solve[rewrite H1 in H3; congruence].
solve[destruct stack; auto].
intros H1; destruct (at_external_halted_excl (get_module_csem (modules PF)) c) 
 as [H3|H3].
solve[rewrite H1 in H3; congruence].
solve[destruct stack; auto].
intros H1; destruct (at_external_halted_excl (get_module_csem (modules PF)) c) 
 as [H3|H3].
solve[rewrite H1 in H3; congruence].
solve[destruct stack; auto].
intros H1; destruct (at_external_halted_excl (get_module_csem (modules PF)) c) 
 as [H3|H3].
solve[rewrite H1 in H3; congruence].
solve[destruct stack; auto].
intros H1; destruct (at_external_halted_excl (get_module_csem (modules PF)) c) 
 as [H3|H3].
solve[rewrite H1 in H3; congruence].
solve[destruct stack; auto].
solve[left; auto].
Qed.
Next Obligation.
destruct q; simpl in H|-*.
destruct stack; try solve[inversion H].
destruct f; try solve[inversion H].
case_eq (at_external (get_module_csem (modules PF)) c). 
intros [[ef sig] args] H1.
rewrite H1 in H.
case_eq (after_external (get_module_csem (modules PF)) retv c).
intros c' H2; rewrite H2 in H.
inv H; apply after_at_external_excl in H2.
simpl; rewrite H2; auto.
case_eq (after_external (get_module_csem (modules PF)) retv c).
solve[intros c' H2; rewrite H2 in H; intro; congruence].
intros H2 H3.
solve[rewrite H2 in H; congruence].
solve[intros H1; rewrite H1 in H; congruence].
Qed.

End LinkerCoreSemantics.

Section LinkingExtension.
Variables (F V: Type).
Variables
 (Z: Type) (** external states *) (cT fT vT: nat -> Type)
 (num_modules: nat) (procedure_linkage_table: ident -> option nat)
 (plt_ok: 
   forall (id: ident) (i: nat), 
   procedure_linkage_table id = Some i -> i < num_modules)
 (modules: forall i: nat, i < num_modules -> 
   CompCertModule.Sig (fT i) (vT i) (cT i))
 (csig: ext_spec Z) (esig: ext_spec Z)
 (handled: list AST.external_function).

(** Consistency conditions on handled functions and the procedure linkage table *)

(*APPARENTLY NOT REQUIRED
 Variable handled_in_plt:
 forall ef, In ef handled -> 
 exists id, exists sig, exists i,
  ef = EF_external id sig /\ procedure_linkage_table id = Some i.*)

Variable plt_in_handled:
 forall i j (pf: i < num_modules) c sig sig2 args id,
 at_external (get_module_csem (modules pf)) c = Some (EF_external id sig, sig2, args) ->
 procedure_linkage_table id = Some j -> In (EF_external id sig) handled.

Variable at_external_not_handled:
 forall ef sig args s,
 linker_at_external fT vT procedure_linkage_table modules s = Some (ef, sig, args) ->
 IN ef handled = false.

Variable linkable_csig_esig: linkable (fun z : Z => z) handled csig esig.

Definition genv_map: nat -> Type := fun i: nat => Genv.t (fT i) (vT i).

Program Definition trivial_core_semantics: forall i: nat, 
 CoreSemantics (genv_map i) (cT i) mem (list (ident * globdef (fT i) (vT i))) :=
 fun i: nat => Build_CoreSemantics _ _ _ _ 
  (fun _ _ _ => False) (fun _ _ _ => None) (fun _ => None) 
  (fun _ _ => None) (fun _ => None) (fun _ _ _ _ _ => False) _ _ _ _.

Definition csem_map: forall i: nat, 
 CoreSemantics (genv_map i) (cT i) mem (list (ident * globdef (fT i) (vT i))) :=
 fun i: nat => match lt_dec i num_modules with
               | left pf => get_module_csem (modules pf)
               | right _ => trivial_core_semantics i
               end.

Import TruePropCoercion.

Definition init_data := fun i: nat => list (ident * globdef (fT i) (vT i)).

Definition linker_proj_core (i: nat) (s: linker_corestate num_modules cT): option (cT i) :=
  match s with
  | mkLinkerCoreState nil _ => None
  | mkLinkerCoreState (mkFrame j pf_j c :: call_stack) _ =>
     match eq_nat_dec i j with 
     | left pf => Some (eq_rect j (fun x => cT x) c i (sym_eq pf))
     | right _ => None
     end
  end.

Definition linker_active (s: linker_corestate num_modules cT): nat :=
  match s with
  | mkLinkerCoreState nil _ => 0
  | mkLinkerCoreState (mkFrame i pf_i c :: call_stack) _ => i
  end.

Program Definition linking_extension: 
 @Extension.Sig (Genv.t F V) (list (ident * globdef F V)) 
        (linker_corestate num_modules cT) genv_map cT mem init_data Z unit Z
        (linker_core_semantics F V cT fT vT procedure_linkage_table plt_ok modules)
        csem_map csig esig handled :=
 Extension.Make genv_map (fun i: nat => list (ident * globdef (fT i) (vT i)))
  (linker_core_semantics F V cT fT vT procedure_linkage_table plt_ok modules)
  csem_map csig esig handled num_modules
  linker_proj_core _  
  linker_active _ 
  (fun _ => tt) (fun z: Z => z) (fun (_:unit) (z: Z) => z)
  _ _ _ _ _.
Next Obligation.
unfold linker_proj_core.
destruct s. destruct stack; auto. destruct f; auto.
destruct (eq_nat_dec i i0); auto. subst.
solve[elimtype False; omega].
Qed.
Next Obligation.
unfold linker_proj_core, linker_active.
destruct s; simpl.
destruct stack; simpl.
solve[simpl in stack_nonempty; elimtype False; omega].
destruct f; simpl.
destruct (eq_nat_dec i i); try solve[elimtype False; auto].
exists c; f_equal.
unfold eq_rect, eq_sym.
Admitted. (*dependent types*)
Next Obligation.
unfold linker_proj_core in H.
destruct s.
destruct stack; try solve[congruence].
destruct f; try solve[congruence].
destruct (eq_nat_dec i i0); try solve[congruence].
unfold eq_rect, eq_sym in H.
destruct e. 
inv H.
simpl in H1.
case_eq (at_external (get_module_csem (modules PF)) c); 
 try solve[congruence].
destruct p as [[ef' sig'] args'].
destruct ef'; try solve[congruence
 |intros H2; rewrite H2 in H1; try solve[congruence]].
case_eq (procedure_linkage_table name); try solve[congruence].
intros n H2 H3.
rewrite H3 in H1.
unfold csem_map in H0.
destruct (lt_dec i num_modules).
assert (PF = l) by apply proof_irr.
subst. unfold genv_map in H0. rewrite H0 in H3; inv H3.
solve[apply ListSet.set_mem_correct2; eapply plt_in_handled; eauto].
elimtype False; auto.
solve[intros H2 H3; rewrite H3, H2 in H1; congruence].
intros H2; rewrite H2 in H1.
unfold csem_map in H0.
destruct (lt_dec i num_modules); [|solve[elimtype False; auto]].
assert (PF = l) by apply proof_irr.
subst. unfold genv_map in H0. 
solve[rewrite H0 in H2; inv H2].
Qed.
Next Obligation. solve[eapply at_external_not_handled; eauto]. Qed.
  
End LinkingExtension.  
  
