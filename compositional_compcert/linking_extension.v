Load loadpath.
Require Import msl.base. (*for spec tac*)

Require Import compositional_compcert.core_semantics.
Require Import compositional_compcert.forward_simulations.
Require Import compositional_compcert.rg_forward_simulations.
Require Import compositional_compcert.step_lemmas.
Require Import compositional_compcert.extspec.
Require Import compositional_compcert.extension.
Require Import compositional_compcert.extension_simulations.
Require Import compositional_compcert.extension_proof.
Require Import compositional_compcert.Address.
Require Import compositional_compcert.mem_lemmas.
Require Import veric.juicy_mem. (*TODO: need to eliminate this dependency*)
Require Import veric.juicy_extspec. (*TODO: need to eliminate this dependency*)
Require Import veric.Coqlib2. (*TODO: need to eliminate this dependency*)

Require Import Axioms.
Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Maps.

Set Implicit Arguments.
Local Open Scope nat_scope.

Module CompCertModule. Section CompCertModule.
Variables F V C: Type.

Inductive Sig: Type := Make: forall
 (ge: Genv.t F V)
 (csem: CoopCoreSem (Genv.t F V) C (list (ident * globdef F V))),
 Sig.

End CompCertModule. End CompCertModule.

Definition get_module_genv F V C (ccm: CompCertModule.Sig F V C): Genv.t F V :=
  match ccm with CompCertModule.Make g _ => g end.

Definition get_module_csem F V C (ccm: CompCertModule.Sig F V C): 
  CoopCoreSem (Genv.t F V) C (list (ident * globdef F V)) :=
  match ccm with CompCertModule.Make _ sem => sem end.

Definition get_module_rgsem F V C (ccm: CompCertModule.Sig F V C): 
  CoopCoreSem (Genv.t F V) (blockmap*C) (list (ident * globdef F V)) :=
  match ccm with CompCertModule.Make _ sem => RelyGuaranteeSemantics sem end.

Inductive frame (cT: nat -> Type) (num_modules: nat): Type := mkFrame: 
 forall (i: nat) (PF: i < num_modules) (fc: blockmap*cT i), frame cT num_modules.
Implicit Arguments mkFrame [cT num_modules].

Definition call_stack (cT: nat -> Type) (num_modules: nat) := list (frame cT num_modules).

Section LinkerCoreSemantics.
Variables (F V: Type) (ge: Genv.t F V) (num_modules: nat).
Variables (cT fT vT: nat -> Type)
 (procedure_linkage_table: ident -> option nat)
 (plt_ok: 
   forall (id: ident) (i: nat), 
   procedure_linkage_table id = Some i -> i < num_modules)
 (modules: forall i: nat, i < num_modules -> CompCertModule.Sig (fT i) (vT i) (cT i))
 (entry_points: list (val*val*signature)).

Implicit Arguments plt_ok [].

Definition all_at_external (l: call_stack cT num_modules) :=
 List.Forall (fun f => match f with mkFrame i pf_i c => 
  exists ef, exists sig, exists args,
   at_external (get_module_rgsem (modules pf_i)) c = Some (ef, sig, args)
  end) l.

Inductive linker_corestate: Type := mkLinkerCoreState: forall
 (stack: call_stack cT num_modules)
 (stack_nonempty: length stack >= 1)
 (callers_at_external: all_at_external (List.tail stack)),
 linker_corestate.

Implicit Arguments mkLinkerCoreState [].

Definition genvs_agree (F1 F2 V1 V2: Type) (ge1: Genv.t F1 V1) (ge2: Genv.t F2 V2) :=
  (forall id: ident, Genv.find_symbol ge1 id=Genv.find_symbol ge2 id) /\
  (forall b v1 v2,
    ZMap.get b (Genv.genv_vars ge1) = Some v1 -> ZMap.get b (Genv.genv_vars ge2) = Some v2 ->  
    gvar_init v1=gvar_init v2).

Lemma length_cons {A: Type}: forall (a: A) (l: list A), length (a :: l) >= 1.
Proof. solve[intros; simpl; omega]. Qed.

Lemma all_at_external_consnil: forall f, all_at_external (List.tail (f::nil)).
Proof.
unfold all_at_external; intros; simpl.
solve[apply Forall_nil].
Qed.

Lemma all_at_external_cons: forall f l, all_at_external (f::l) -> all_at_external l.
Proof.
intros f l; revert f; destruct l; simpl; auto.
solve[intros f H1; constructor].
intros f' H1.
unfold all_at_external in H1.
inversion H1; subst; auto.
Qed.

Inductive linker_corestep: 
  Genv.t F V -> linker_corestate -> mem -> linker_corestate -> mem -> Prop :=
(** coresteps of the 'top' core *)                    
| link_step: forall ge (stack: call_stack cT num_modules) 
                    i c m (pf_i: i < num_modules) c' m' pf ext_pf,
  (forall (k: nat) (pf_k: k<num_modules), genvs_agree ge (get_module_genv (modules pf_k))) ->
  (forall (k: nat) (pf_k: k<num_modules), genvs_domain_eq ge (get_module_genv (modules pf_k))) ->
  corestep (get_module_rgsem (modules pf_i)) (get_module_genv (modules pf_i)) c m c' m' ->
  linker_corestep ge
   (mkLinkerCoreState (mkFrame i pf_i c :: stack) pf ext_pf) m
   (mkLinkerCoreState (mkFrame i pf_i c' :: stack) pf ext_pf) m'

(** 'link' steps *)
| link_call: forall ge stack i j args id sig b (c: (blockmap*cT i)%type) m (pf_i: i < num_modules) c'
   (LOOKUP: procedure_linkage_table id = Some j) 
   (NEQ_IJ: i<>j) (** 'external' functions cannot be defined within this module *)
   (AT_EXT: at_external (get_module_rgsem (modules pf_i)) c =
     Some (EF_external id sig, sig, args)) pf ext_pf ext_pf',
  (forall (k: nat) (pf_k: k<num_modules), genvs_agree ge (get_module_genv (modules pf_k))) ->
  (forall (k: nat) (pf_k: k<num_modules), genvs_domain_eq ge (get_module_genv (modules pf_k))) ->
  Genv.find_symbol ge id = Some b -> 
  In (Vptr b (Int.repr 0), Vptr b (Int.repr 0), sig) entry_points -> 
  make_initial_core 
   (get_module_rgsem (modules (plt_ok id j LOOKUP)))
   (get_module_genv (modules (plt_ok id j LOOKUP))) (Vptr b (Int.repr 0)) args = Some c' -> 

  linker_corestep ge
   (mkLinkerCoreState (mkFrame i pf_i c :: stack) pf ext_pf) m
   (mkLinkerCoreState 
     (mkFrame j (plt_ok id j LOOKUP) c' :: mkFrame i pf_i c :: stack) 
     (length_cons _ _) ext_pf') m

(** 'return' steps *)
| link_return: forall ge stack i j id c m (pf_i: i < num_modules) c' c'' retv
   (LOOKUP: procedure_linkage_table id = Some j)
   (HALTED: safely_halted (get_module_rgsem (modules (plt_ok id j LOOKUP))) c' = Some retv) 
   pf ext_pf ext_pf',
  (forall (k: nat) (pf_k: k<num_modules), genvs_agree ge (get_module_genv (modules pf_k))) ->
  (forall (k: nat) (pf_k: k<num_modules), genvs_domain_eq ge (get_module_genv (modules pf_k))) ->
  after_external (get_module_rgsem (modules pf_i)) (Some retv) c = Some c'' -> 
  linker_corestep ge
   (mkLinkerCoreState 
     (mkFrame j (plt_ok id j LOOKUP) c' :: mkFrame i pf_i c :: stack) pf ext_pf) m
   (mkLinkerCoreState (mkFrame i pf_i c'' :: stack) (length_cons _ _) ext_pf') m.

Definition linker_at_external (s: linker_corestate) := 
  match s with
  | mkLinkerCoreState nil _ _ => None
  | mkLinkerCoreState (mkFrame i pf_i c :: call_stack) _ _ =>
     match at_external (get_module_rgsem (modules pf_i)) c with
     | Some (EF_external id sig, ef_sig, args) => 
       match procedure_linkage_table id with 
       | None => Some (EF_external id sig, ef_sig, args)
       | Some module_id => None
       end
     | Some (ef, sig, args) => Some (ef, sig, args)
     | None => None
     end
  end.
Implicit Arguments linker_at_external [].

Definition linker_after_external (retv: option val) (s: linker_corestate) :=
  match s with
  | mkLinkerCoreState nil _ _ => None
  | mkLinkerCoreState (mkFrame i pf_i c :: call_stack) _ ext_pf =>
    match after_external (get_module_rgsem (modules pf_i)) retv c with
    | None => None
    | Some c' => Some (mkLinkerCoreState (mkFrame i pf_i c' :: call_stack) 
       (length_cons _ _) ext_pf)
    end
  end.

Definition linker_safely_halted (s: linker_corestate) :=
  match s with
  | mkLinkerCoreState nil _ _ => None
  | mkLinkerCoreState (mkFrame i pf_i c :: nil) _ _ =>
     safely_halted (get_module_rgsem (modules pf_i)) c
  | mkLinkerCoreState (mkFrame i pf_i c :: call_stack) _ _ => None
  end.

Definition main_id := 1%positive. (*hardcoded*)

Definition linker_initial_mem (ge: Genv.t F V) (m: mem) (init_data: list (ident * globdef F V)) := 
  Genv.alloc_globals ge Mem.empty init_data = Some m.

Definition linker_make_initial_core (ge: Genv.t F V) (fptr: val) (args: list val) :=
  match fptr, Genv.find_symbol ge main_id with
  | Vptr b ofs, Some b' => 
    if Z_eq_dec b b' then 
       (match procedure_linkage_table main_id as x 
          return (x = procedure_linkage_table main_id -> option linker_corestate) with
       | None => fun _ => None (** no module defines 'main' *)
       | Some i => fun pf => 
         match make_initial_core 
                 (get_module_rgsem (modules (@plt_ok main_id i (eq_sym pf))))
                 (get_module_genv (modules (@plt_ok main_id i (eq_sym pf)))) fptr args with
         | None => None
         | Some c => 
             Some (mkLinkerCoreState (mkFrame i (plt_ok main_id i (eq_sym pf)) c :: nil) 
                    (length_cons _ _) (all_at_external_consnil _))
         end 
       end) (refl_equal _)
     else None
   | _, _ => None (** either no 'main' was defined or [f] is not a [Vptr] *)
   end.

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
solve[simpl in *; rewrite H2; auto].
solve[simpl; rewrite AT_EXT, LOOKUP; auto].
destruct (at_external_halted_excl (get_module_rgsem (modules (plt_ok id j LOOKUP))) c')
 as [H3|H3]; simpl.
solve[rewrite H3; auto].
solve[rewrite H3 in HALTED; congruence].
Qed.
Next Obligation.
inv H.
apply corestep_not_halted in H2.
simpl; destruct stack; auto.
destruct (at_external_halted_excl (get_module_rgsem (modules pf_i)) c)
 as [H5|H5].
simpl; destruct stack; auto.
solve[rewrite AT_EXT in H5; congruence].
solve[simpl; destruct stack; auto].
solve[auto].
Qed.
Next Obligation.
destruct q; simpl.
destruct stack; auto.
destruct f; auto.
case_eq (at_external (get_module_rgsem (modules PF)) fc); [intros [[ef sig] args]|intros].
destruct ef; auto.
intros.
destruct (procedure_linkage_table name).
solve[left; auto].
destruct stack; auto.
destruct (at_external_halted_excl (get_module_rgsem (modules PF)) fc) 
 as [H3|H3].
solve[rewrite H in H3; congruence].
solve[right; auto].
intros H1; destruct (at_external_halted_excl (get_module_rgsem (modules PF)) fc) 
 as [H3|H3].
solve[rewrite H1 in H3; congruence].
solve[destruct stack; auto].
intros H1; destruct (at_external_halted_excl (get_module_rgsem (modules PF)) fc) 
 as [H3|H3].
solve[rewrite H1 in H3; congruence].
solve[destruct stack; auto].
intros H1; destruct (at_external_halted_excl (get_module_rgsem (modules PF)) fc) 
 as [H3|H3].
solve[rewrite H1 in H3; congruence].
solve[destruct stack; auto].
intros H1; destruct (at_external_halted_excl (get_module_rgsem (modules PF)) fc) 
 as [H3|H3].
solve[rewrite H1 in H3; congruence].
solve[destruct stack; auto].
intros H1; destruct (at_external_halted_excl (get_module_rgsem (modules PF)) fc) 
 as [H3|H3].
solve[rewrite H1 in H3; congruence].
solve[destruct stack; auto].
intros H1; destruct (at_external_halted_excl (get_module_rgsem (modules PF)) fc) 
 as [H3|H3].
solve[rewrite H1 in H3; congruence].
solve[destruct stack; auto].
intros H1; destruct (at_external_halted_excl (get_module_rgsem (modules PF)) fc) 
 as [H3|H3].
solve[rewrite H1 in H3; congruence].
solve[destruct stack; auto].
intros H1; destruct (at_external_halted_excl (get_module_rgsem (modules PF)) fc) 
 as [H3|H3].
solve[rewrite H1 in H3; congruence].
solve[destruct stack; auto].
intros H1; destruct (at_external_halted_excl (get_module_rgsem (modules PF)) fc) 
 as [H3|H3].
solve[rewrite H1 in H3; congruence].
solve[destruct stack; auto].
intros H1; destruct (at_external_halted_excl (get_module_rgsem (modules PF)) fc) 
 as [H3|H3].
solve[rewrite H1 in H3; congruence].
solve[destruct stack; auto].
intros H1; destruct (at_external_halted_excl (get_module_rgsem (modules PF)) fc) 
 as [H3|H3].
solve[rewrite H1 in H3; congruence].
solve[destruct stack; auto].
solve[left; auto].
Qed.
Next Obligation.
destruct q; simpl in H|-*.
destruct stack; try solve[inversion H].
destruct f; try solve[inversion H].
case_eq (after_external (get_module_rgsem (modules PF)) retv fc).
intros c' H2; rewrite H2 in H.
destruct c' as [? ?]; simpl in *.
inv H; apply after_at_external_excl in H2.
simpl; rewrite H2; auto.
case_eq (after_external (get_module_rgsem (modules PF)) retv fc).
solve[intros c' H2; rewrite H2 in H; intro; congruence].
intros H2 H3.
solve[rewrite H2 in H; congruence].
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
 (entry_points: list (val*val*signature)).

Definition genv_map: nat -> Type := fun i: nat => Genv.t (fT i) (vT i).

Program Definition trivial_core_semantics: forall i: nat, 
 CoreSemantics (genv_map i) (cT i) mem (list (ident * globdef (fT i) (vT i))) :=
 fun i: nat => Build_CoreSemantics _ _ _ _
  (fun _ _ _ => False) (fun _ _ _ => None) (fun _ => None) 
  (fun _ _ => None) (fun _ => None) (fun _ _ _ _ _ => False) _ _ _ _.

Program Definition trivial_coop_coresem: forall i: nat, 
 CoopCoreSem (genv_map i) (cT i) (list (ident * globdef (fT i) (vT i))) :=
 fun i: nat => Build_CoopCoreSem _ _ _ (trivial_core_semantics i) _ _ _.
Next Obligation. elimtype False; auto. Qed.
Next Obligation. elimtype False; auto. Qed.
Next Obligation. elimtype False; auto. Qed.

Definition csem_map: forall i: nat, 
 CoopCoreSem (genv_map i) (blockmap*cT i) (list (ident * globdef (fT i) (vT i))) :=
 fun i: nat => match lt_dec i num_modules with
               | left pf => get_module_rgsem (modules pf)
               | right _ => RelyGuaranteeSemantics (trivial_coop_coresem i)
               end.

Definition linker_proj_core (i: nat) (s: linker_corestate cT _ _ modules): 
  option (blockmap*cT i) :=
  match s with
  | mkLinkerCoreState nil _ _ => None
  | mkLinkerCoreState (mkFrame j pf_j c :: call_stack) _ _ =>
     match eq_nat_dec i j with 
     | left pf => Some (eq_rect j (fun x => (blockmap*cT x)%type) c i (sym_eq pf))
     | right _ => None
     end
  end.

Definition linker_active (s: linker_corestate cT _ _ modules): nat :=
  match s with
  | mkLinkerCoreState nil _ _ => 0
  | mkLinkerCoreState (mkFrame i pf_i c :: call_stack) _ _ => i
  end.

Definition handled (ef: AST.external_function): Prop := 
 forall s c sig args,
 linker_proj_core (linker_active s) s = Some c ->
 at_external (csem_map (linker_active s)) c = Some (ef, sig, args) ->
 linker_at_external procedure_linkage_table s = None.

(** Consistency conditions on handled functions and the procedure linkage table *)

Variable plt_in_handled:
 forall i j (pf: i < num_modules) c sig sig2 args id,
 at_external (get_module_csem (modules pf)) c = Some (EF_external id sig, sig2, args) ->
 procedure_linkage_table id = Some j -> handled (EF_external id sig).

Implicit Arguments linker_at_external [num_modules cT].

Variable at_external_not_handled:
 forall ef sig args s,
 linker_at_external fT vT procedure_linkage_table modules s = Some (ef, sig, args) ->
 ~handled ef.

Program Definition trivial_genv (i: nat): Genv.t (fT i) (vT i) :=
 Genv.mkgenv (PTree.empty block) (ZMap.init None) (ZMap.init None) (Zgt_pos_0 1) 
 _ _ _ _ _.
Next Obligation. solve[rewrite PTree.gempty in H; congruence]. Qed.
Next Obligation. solve[rewrite ZMap.gi in H; congruence]. Qed.
Next Obligation. solve[rewrite ZMap.gi in H; congruence]. Qed.
Next Obligation. solve[rewrite ZMap.gi in H; congruence]. Qed.
Next Obligation. solve[rewrite PTree.gempty in H; congruence]. Qed.

Definition genvs: forall i: nat, Genv.t (fT i) (vT i) :=
 fun i: nat => match lt_dec i num_modules with
               | left pf => get_module_genv (modules pf)
               | right _ => trivial_genv i
               end.

Definition init_data := fun i: nat => list (ident * globdef (fT i) (vT i)).

Implicit Arguments linker_corestate [fT vT].

Lemma dependent_types_nonsense: forall i (c: (blockmap*cT i)%type) (e: i=i), 
 eq_rect i (fun x => (blockmap*cT x)%type) c i (eq_sym e) = c.
Proof.
intros; rewrite <-Eqdep_dec.eq_rect_eq_dec; auto.
apply eq_nat_dec.
Qed.

Variable linkable_csig_esig: linkable (fun z : Z => z) 
  (fun (ef: AST.external_function) => forall s fc sig args,
    linker_proj_core (linker_active s) s = Some fc -> 
    at_external (csem_map (linker_active s)) fc = Some (ef, sig, args) ->
    linker_at_external _ _ procedure_linkage_table _ s = None)
  csig esig.

Lemma handled_lem: 
 forall s fc ef sig args,
 linker_proj_core (linker_active s) s = Some fc -> 
 at_external (csem_map (linker_active s)) fc = Some (ef, sig, args) ->
 linker_at_external _ _ procedure_linkage_table _ s = None -> 
 exists id, exists sig, 
  ef = EF_external id sig /\
  exists b, procedure_linkage_table id = Some b.
Proof.
intros.
unfold linker_at_external in H1.
destruct s; simpl in H1.
destruct stack; try solve[congruence].
simpl in H; congruence.
destruct f.
simpl in H0.
unfold csem_map in H0.
destruct (lt_dec i num_modules); try solve[elimtype False; omega].
assert (Heq: PF = l) by apply proof_irr.
rewrite Heq in *.
simpl in H.
destruct (eq_nat_dec i i); try solve[elimtype False; omega].
rewrite dependent_types_nonsense in H.
inversion H; subst fc; clear H.
unfold genv_map in *; simpl in *. 
rewrite H0 in H1.
destruct ef; try solve[congruence].
exists name.
destruct (procedure_linkage_table name); try solve[congruence].
solve[eexists; split; eauto].
Qed.

Lemma handled_invar: 
 forall s fc s' f'c' ef sig args sig' args',
 linker_proj_core (linker_active s) s = Some fc -> 
 at_external (csem_map (linker_active s)) fc = Some (ef, sig, args) ->
 linker_at_external _ _ procedure_linkage_table _ s = None -> 
 linker_proj_core (linker_active s') s' = Some f'c' -> 
 at_external (csem_map (linker_active s')) f'c' = Some (ef, sig', args') ->
 linker_at_external _ _ procedure_linkage_table _ s' = None.
Proof.
intros.
unfold linker_at_external.
destruct s'.
destruct stack; auto.
destruct f; auto.
simpl in H3.
unfold csem_map in H3.
destruct (lt_dec i num_modules); try solve[elimtype False; omega].
assert (PF = l) as -> by apply proof_irr.
simpl in H2.
destruct (eq_nat_dec i i); try solve[elimtype False; omega].
rewrite dependent_types_nonsense in H2.
inversion H2; subst f'c'; clear H2.
unfold genv_map in *; simpl; rewrite H3.
assert (exists id, exists sig, 
 ef = EF_external id sig /\
 exists b, procedure_linkage_table id = Some b) as [id [sig'' [-> [b ->]]]].
 solve[eapply handled_lem; eauto].
auto.
Qed. 

Program Definition linking_extension: 
 @Extension.Sig _ _ _ _ (Genv.t F V) (list (ident * globdef F V)) 
     (linker_corestate num_modules cT modules) 
     (linker_core_semantics F V cT fT vT procedure_linkage_table plt_ok modules entry_points)
     esig _ _ (fun i => (blockmap*cT i)%type) csem_map csig :=
 Extension.Make 
  (linker_core_semantics F V cT fT vT procedure_linkage_table plt_ok modules entry_points)
  esig _ _ csem_map csig 
  (const num_modules)
  linker_proj_core _  
  linker_active _ 
  (fun _ => tt) (fun z: Z => z) (fun (_:unit) (z: Z) => z)
  _ _ linkable_csig_esig handled_invar.
Next Obligation.
unfold linker_proj_core.
destruct s. destruct stack; auto. destruct f; auto.
destruct (eq_nat_dec i i0); auto. subst.
unfold const in *.
solve[elimtype False; omega].
Qed.
Next Obligation.
unfold linker_proj_core, linker_active.
destruct s; simpl.
destruct stack; simpl.
solve[simpl in stack_nonempty; elimtype False; omega].
destruct f; simpl.
destruct (eq_nat_dec i i); try solve[elimtype False; auto].
exists fc; f_equal.
solve[rewrite dependent_types_nonsense; auto].
Qed.

Lemma linker_stepN s c m c' m' n ge 
 (genvs_agree: forall (k : nat) (pf_k : k < num_modules),
  genvs_agree ge (get_module_genv (modules pf_k)))
 (genvs_domain_eq: forall (k : nat) (pf_k : k < num_modules),
  genvs_domain_eq ge (get_module_genv (modules pf_k))) :
 linker_proj_core (linker_active s) s = Some c -> 
 corestepN (csem_map (linker_active s)) (genvs (linker_active s)) n c m c' m' ->
 exists s', corestepN 
  (linker_core_semantics F V cT fT vT procedure_linkage_table plt_ok modules entry_points) 
  ge n s m s' m' /\ linker_active s=linker_active s /\
  linker_proj_core (linker_active s) s' = Some c'.
Proof.
revert s c m c' m'.
induction n; simpl.
intros s c m c' m' H1 H2; inv H2.
solve[exists s; split; auto].
intros s c m c' m' H1 [c2 [m2 [STEP12 STEP23]]].
destruct s; simpl in *.
destruct stack; try solve[congruence].
destruct f.
specialize (IHn 
 (mkLinkerCoreState (mkFrame i PF c2 :: stack) 
   stack_nonempty callers_at_external)
 c2 m2 c' m').
simpl in IHn; spec IHn.
destruct (eq_nat_dec i i); try solve[elimtype False; omega].
solve[rewrite dependent_types_nonsense; auto].
destruct IHn as [s' [STEP23' [_ PROJ]]]; auto.
destruct (eq_nat_dec i i); try solve[elimtype False; omega].
rewrite dependent_types_nonsense in H1.
inversion H1; rewrite H0 in *; clear H0 H1.
exists s'; split; auto.
exists (mkLinkerCoreState (mkFrame i PF c2 :: stack) 
  stack_nonempty callers_at_external).
exists m2.
split; auto.
constructor; auto.
unfold csem_map, genvs in STEP12.
destruct (lt_dec i num_modules); try solve[elimtype False; omega].
solve[assert (PF=l) as -> by apply proof_irr; auto].
Qed.

Lemma linker_core_compatible: forall (ge: Genv.t F V) 
   (agree: forall (k : nat) (pf_k : k < num_modules),
   genvs_agree ge (get_module_genv (modules pf_k)))
   (domain_eq: forall (k : nat) (pf_k : k < num_modules),
     genvs_domain_eq ge (get_module_genv (modules pf_k)))
   (csem_fun: forall i: nat, corestep_fun (csem_map i)),
 @core_compatible _ _ _ _ (Genv.t F V) (list (ident*globdef F V)) 
        (linker_corestate num_modules cT modules) 
        (linker_core_semantics F V cT fT vT procedure_linkage_table plt_ok modules entry_points) 
        esig (fun i => Genv.t (fT i) (vT i)) init_data (fun i => (blockmap*cT i)%type)
        csem_map csig ge genvs linking_extension.
Proof.
intros; constructor.

intros until c; simpl; intros H1 H2 H3.
inv H3; simpl in H2|-*.
destruct (eq_nat_dec i i); try solve[elimtype False; auto].
inv H2.
simpl in H1.
exists c'.
unfold csem_map, genvs.
destruct (lt_dec i num_modules); try solve[elimtype False; omega].
split.
assert (l = pf_i) by apply proof_irr.
rewrite H2.
solve[rewrite dependent_types_nonsense; auto].
solve[rewrite dependent_types_nonsense; split; auto].
unfold runnable, csem_map in H1.
simpl in H1.
destruct (lt_dec i num_modules); try solve[elimtype False; omega].
destruct (eq_nat_dec i i); try solve[elimtype False; auto].
inv H2.
rewrite dependent_types_nonsense in H1.
assert (H2: l = pf_i) by apply proof_irr. 
rewrite H2 in H1.
solve[unfold init_data, genv_map in H1; rewrite AT_EXT in H1; congruence].
destruct (eq_nat_dec j j); try solve[elimtype False; omega].
rewrite dependent_types_nonsense in H2.
inversion H2. 
rewrite H5 in *; clear H5 H2 e.
unfold runnable in H1; simpl in H1.
unfold init_data in H1.
destruct (@at_external (Genv.t (fT j) (vT j)) (blockmap*cT j) Mem.mem
             (list (prod ident (globdef (fT j) (vT j)))) 
             (csem_map j) c).
congruence.
unfold csem_map in H1.
generalize LOOKUP as LOOKUP'; intro.
apply plt_ok in LOOKUP'.
destruct (lt_dec j num_modules); try solve[elimtype False; omega].
assert (H2: l = plt_ok LOOKUP) by apply proof_irr.
rewrite H2 in H1.
unfold genv_map in *; rewrite HALTED in H1.
congruence.

intros until m'; simpl; intros H1 H2 H3.
inv H3; simpl in *.
assert (Heq: c0 = c). 
 destruct (eq_nat_dec i i); try solve[elimtype False; omega].
 solve[rewrite dependent_types_nonsense in H1; inv H1; auto].
subst c0.
clear H1.
split; auto.
destruct (eq_nat_dec i i); try solve[elimtype False; omega].
rewrite dependent_types_nonsense.
generalize (csem_fun i).
unfold csem_map, genvs in H2|-*.
destruct (lt_dec i num_modules); try solve[elimtype False; omega].
assert (H3: l = pf_i) by apply proof_irr.
rewrite H3 in H2|-*.
clear H3 e.
intros csem_fun'.
f_equal.
eapply csem_fun' in H2.
spec H2; eauto.
inv H2; auto.
assert (Heq: c0 = c). 
 destruct (eq_nat_dec i i); try solve[elimtype False; omega].
 solve[rewrite dependent_types_nonsense in H1; inv H1; auto].
subst c0.
clear H1.
unfold csem_map in H2.
destruct (lt_dec i num_modules); try solve[elimtype False; omega].
apply corestep_not_at_external in H2.
assert (H3: l = pf_i) by apply proof_irr.
rewrite H3 in H2; clear H3.
unfold init_data, genv_map in *; rewrite H2 in AT_EXT.
congruence.
assert (Heq: c'0 = c). 
 destruct (eq_nat_dec j j); try solve[elimtype False; omega].
 solve[rewrite dependent_types_nonsense in H1; inv H1; auto].
subst c'0.
clear H1.
unfold csem_map in H2.
generalize LOOKUP as LOOKUP'; intro.
apply plt_ok in LOOKUP'.
destruct (lt_dec j num_modules); try solve[elimtype False; omega].
apply corestep_not_halted in H2.
assert (H3: l = plt_ok LOOKUP) by apply proof_irr.
rewrite H3 in H2; clear H3.
unfold init_data, genv_map in *; rewrite H2 in HALTED.
congruence.

intros until m'; intros H1 H2.
simpl in *.
destruct s.
destruct stack; simpl in *.
congruence.
destruct f.
destruct (eq_nat_dec i i); try solve[congruence].
rewrite dependent_types_nonsense in H1.
inv H1.
clear e.
exists (mkLinkerCoreState (mkFrame i PF c' :: stack)
    stack_nonempty callers_at_external).
constructor; auto.
unfold csem_map, genvs in H2.
destruct (lt_dec i num_modules); try solve[elimtype False; omega].
assert (H3: l = PF) by apply proof_irr.
solve[rewrite H3 in H2; auto].

intros until m'; intros H1 H2 H3 H4 j H5.
inv H4; simpl in *.
destruct (eq_nat_dec i i); try solve[elimtype False; omega|auto].
destruct (eq_nat_dec j i); try solve[elimtype False; omega|auto].
subst; destruct (eq_nat_dec j j0); try solve[elimtype False; omega].
subst; destruct (eq_nat_dec j i); try solve[elimtype False; omega].
solve[auto].

intros until n; intros H1 H2 H3 j H4.
admit. (*tedious*)

intros until retv; intros H1 H2 H3.
destruct s; destruct s'; simpl in H3.
destruct stack; try solve[inv H3].
destruct f.
unfold csem_map in H2; simpl in H2.
destruct (lt_dec i num_modules); try solve[elimtype False; congruence].
assert (H4: l = PF) by apply proof_irr; auto.
rewrite H4 in H2.
unfold init_data in *.
simpl in H1.
destruct (eq_nat_dec i i); try solve[elimtype False; omega].
rewrite dependent_types_nonsense in H1; inversion H1; subst c.
unfold genv_map in H2; rewrite H2 in H3; inversion H3.
solve[subst stack0; auto].

intros until retv; intros H1 H2.
destruct s; simpl in *.
destruct stack; try solve[congruence].
destruct f.
destruct (eq_nat_dec i i); try solve[elimtype False; omega].
rewrite dependent_types_nonsense in H1.
inv H1.
clear e.
exists (mkLinkerCoreState (mkFrame i PF c' :: stack) stack_nonempty callers_at_external).
unfold csem_map in H2.
destruct (lt_dec i num_modules); try solve[elimtype False; omega].
assert (H: l = PF) by apply proof_irr; auto.
rewrite H in H2.
unfold init_data, genv_map in *; rewrite H2.
simpl.
destruct (eq_nat_dec i i); try solve[elimtype False; omega].
split; auto.
repeat f_equal; auto.
solve[rewrite dependent_types_nonsense; auto].

intros until retv; intros H1 j H2.
destruct s; destruct s'; simpl in *.
destruct stack; try solve[inv H1].
destruct f.
destruct (eq_nat_dec j i); try solve[elimtype False; omega].
destruct (after_external (get_module_rgsem (modules PF)) retv fc).
inv H1.
destruct (eq_nat_dec j i); try solve[elimtype False; omega].
auto.
congruence.

intros until args; intros H1.
destruct s; simpl in *|-.
destruct stack; try solve[congruence].
destruct f.
exists fc; simpl.
destruct (eq_nat_dec i i); try solve[elimtype False; omega].
split.
rewrite dependent_types_nonsense; auto.
unfold csem_map.
destruct (lt_dec i num_modules); try solve[elimtype False; omega].
assert (l = PF) as -> by apply proof_irr; auto.
unfold init_data.
unfold genv_map.
destruct (at_external (get_module_rgsem (modules PF)) fc).
2: congruence.
destruct p as [[ef' sig'] args'].
destruct ef'; auto.
destruct (procedure_linkage_table name); try solve[congruence].
Qed.

End LinkingExtension.

Section LinkerCompilable.
Variables 
 (F_S F_T V_S V_T: Type) 
 (geS: Genv.t F_S V_S) (geT: Genv.t F_T V_T) (num_modules: nat).
Variables 
 (cS cT fS fT vS vT: nat -> Type)
 (procedure_linkage_table: ident -> option nat)
 (plt_ok: 
   forall (id: ident) (i: nat), 
   procedure_linkage_table id = Some i -> i < num_modules)
 (modules_S: forall i: nat, i < num_modules -> CompCertModule.Sig (fS i) (vS i) (cS i))
 (modules_T: forall i: nat, i < num_modules -> CompCertModule.Sig (fT i) (vT i) (cT i)) 
 (csig: ext_spec Z) (esig: ext_spec Z).

(** Conditions required to construct a linking extension *)

Definition handled_S := handled cS fS vS procedure_linkage_table modules_S. 
Definition handled_T := handled cT fT vT procedure_linkage_table modules_T. 

Variable linkableS_csig_esig: linkable (fun z : Z => z) handled_S csig esig.
Variable linkableT_csig_esig: linkable (fun z : Z => z) handled_T csig esig.

Variable plt_in_handled_S:
 forall i j (pf: i < num_modules) c sig sig2 args id,
 at_external (get_module_csem (modules_S pf)) c = Some (EF_external id sig, sig2, args) ->
 procedure_linkage_table id = Some j -> handled_S (EF_external id sig).
Variable plt_in_handled_T:
 forall i j (pf: i < num_modules) c sig sig2 args id,
 at_external (get_module_csem (modules_T pf)) c = Some (EF_external id sig, sig2, args) ->
 procedure_linkage_table id = Some j -> handled_T (EF_external id sig).

Implicit Arguments linker_at_external [num_modules cT].

Variable at_external_not_handled_S:
 forall ef sig args s,
 linker_at_external fS vS procedure_linkage_table modules_S s = Some (ef, sig, args) ->
 ~handled_S ef.
Variable at_external_not_handled_T:
 forall ef sig args s,
 linker_at_external fT vT procedure_linkage_table modules_T s = Some (ef, sig, args) ->
 ~handled_T ef.

(** Begin compilability proof *)

Definition csem_map_S := csem_map cS fS vS modules_S.
Definition csem_map_T := csem_map cT fT vT modules_T.

Variable agree_S: forall (k : nat) (pf_k : k < num_modules),
 genvs_agree geS (get_module_genv (modules_S pf_k)).
Variable agree_T: forall (k : nat) (pf_k : k < num_modules),
 genvs_agree geT (get_module_genv (modules_T pf_k)). 
Variable agree_ST: forall (k : nat) (pf_k : k < num_modules),
 genvs_agree (get_module_genv (modules_S pf_k)) (get_module_genv (modules_T pf_k)).

Definition genv_mapS := genvs cS fS vS modules_S. 
Definition genv_mapT := genvs cT fT vT modules_T. 

Variable domain_eq: genvs_domain_eq geS geT.
Variable domain_eq_S: forall (i: nat), genvs_domain_eq geS (genv_mapS i).
Variable domain_eq_T: forall (i: nat), genvs_domain_eq geT (genv_mapT i).

Variable csem_fun_S: forall i: nat, corestep_fun (csem_map_S i).
Variable csem_fun_T: forall i: nat, corestep_fun (csem_map_T i).

Import ExtensionCompilability.
Import Forward_simulation_inj_exposed.

Variable core_data: nat -> Type.
Variable match_state: forall i: nat,
 core_data i ->  meminj -> (blockmap*cS i) -> mem -> (blockmap*cT i) -> mem -> Prop.
Variable core_ord: forall i: nat, core_data i -> core_data i -> Prop.
Variable threads_max: nat. 
Variable threads_max_nonzero: (O < threads_max)%nat. (*Required by defn. of core_ords*)

Variable RGsim: forall i: nat,
 RelyGuaranteeSimulation.Sig (csem_map_S i) (csem_map_T i) (genv_mapS i) (@match_state i).

Variable entry_points: list (val*val*signature).

Variable core_simulations: forall i: nat,
 Forward_simulation_inject
  (list (ident * globdef (fS i) (vS i)))
  (list (ident * globdef (fT i) (vT i))) (csem_map_S i) 
  (csem_map_T i) (genv_mapS i) (genv_mapT i) entry_points 
  (core_data i) (@match_state i) (@core_ord i).

Implicit Arguments linker_corestate [fT vT].

Fixpoint stack_inv j m1 m2 
    (stack1: call_stack cS num_modules) (stack2: call_stack cT num_modules) := 
 match stack1, stack2 with
 | nil, nil => True
 | mkFrame i pf_i c_i :: stack1', mkFrame k pf_k c_k :: stack2' => 
   exists pf: k=i,
   (exists cd, @match_state i cd j c_i m1 
        (eq_rect k (fun x => (blockmap*cT x)%type) c_k i pf) m2) /\
   stack_inv j m1 m2 stack1' stack2'
 | _, _ => False
 end.

Lemma stack_inv_length_eq: 
 forall j m1 m2 stack1 stack2,
 stack_inv j m1 m2 stack1 stack2 -> length stack1=length stack2.
Proof.
intros until stack2.
revert stack2; induction stack1; simpl; auto.
destruct stack2; auto.
solve[intros; elimtype False; auto].
intros stack2.
destruct a.
destruct stack2.
solve[intros; elimtype False; auto].
destruct f.
intros.
simpl.
f_equal.
apply IHstack1.
solve[destruct H as [? [? H]]; auto].
Qed.

Definition R_inv (j:meminj) (x:linker_corestate num_modules cS modules_S) (m1:mem) 
                            (y:linker_corestate num_modules cT modules_T) (m2:mem) := 
 match x, y with
 | mkLinkerCoreState stack1 _ _, mkLinkerCoreState stack2 _ _ => 
    stack_inv j m1 m2 stack1 stack2
 end.

(*Remember: globals aren't injected; we should be able to show that entry points 
  remain equal across compilation phases.*)

Variable entry_points_eq: 
 forall v1 v2 sig,
 List.In (v1, v2, sig) entry_points -> 
 exists b, exists ofs, v1 = Vptr b ofs /\ v2 = Vptr b ofs.

Lemma linker_step_lem1: 
 forall i c2 m2 c2' m2' s2' pf_i stack pf1 pf2,
 corestep (csem_map_S i) (genv_mapS i) c2 m2 c2' m2' -> 
 corestep (linker_core_semantics F_S V_S cS fS vS procedure_linkage_table
             plt_ok modules_S entry_points) geS  
           (mkLinkerCoreState (mkFrame i pf_i c2::stack) pf1 pf2) m2 s2' m2' ->
  s2' = mkLinkerCoreState (mkFrame i pf_i c2'::stack) pf1 pf2.
Proof.
intros until pf2; intros STEP12 STEP12'.
inv STEP12'.
assert (pf_i1 = pf_i) as -> by apply proof_irr.
assert (c' = c2').
 generalize (@csem_fun_S i).
 unfold corestep_fun, csem_map_S, csem_map, genv_mapS, genvs in *.
 destruct (lt_dec i num_modules); try solve[elimtype False; omega].
 apply Eqdep_dec.inj_pair2_eq_dec in H0; [|solve[apply eq_nat_dec]]; subst c2.
 assert (l = pf_i1) by apply proof_irr.
 subst.
 intros H10; specialize (H10 _ _ _ _ _ _ _ H8 STEP12).
 solve[inv H10; auto].
assert (pf0 = pf1) as -> by apply proof_irr; auto.
assert (ext_pf0 = pf2) as -> by apply proof_irr; auto.
solve[subst; auto].
apply corestep_not_at_external in STEP12.
unfold csem_map_S, csem_map in STEP12.
destruct (lt_dec i num_modules); try solve[elimtype False; omega].
assert (l = pf_i1) by apply proof_irr.
subst.
apply Eqdep_dec.inj_pair2_eq_dec in H0.
subst.
clear - AT_EXT STEP12.
solve[unfold genv_map in *; congruence].
solve[apply eq_nat_dec].
apply corestep_not_halted in STEP12.
unfold csem_map_S, csem_map in STEP12.
destruct (lt_dec i num_modules); try solve[elimtype False; omega].
assert (l = plt_ok LOOKUP0) by apply proof_irr.
subst.
apply Eqdep_dec.inj_pair2_eq_dec in H0.
subst.
clear - HALTED STEP12.
solve[unfold genv_map in *; congruence].
solve[apply eq_nat_dec].
Qed.

Lemma linker_step_lem2: 
 forall n i c2 m2 c2' m2' s2' pf_i stack pf1 pf2,
 corestepN (csem_map_T i) (genv_mapT i) n c2 m2 c2' m2' -> 
 corestepN (linker_core_semantics F_T V_T cT fT vT procedure_linkage_table
             plt_ok modules_T entry_points) geT n 
           (mkLinkerCoreState (mkFrame i pf_i c2::stack) pf1 pf2) m2 s2' m2' ->
  s2' = mkLinkerCoreState (mkFrame i pf_i c2'::stack) pf1 pf2.
Proof.
intros until pf2; intros H1 H2.
revert c2 m2 pf1 pf2 H1 H2.
induction n; intros.
solve[inv H1; inv H2; auto].
destruct H1 as [c3 [m3 [STEP12 STEP23]]].
destruct H2 as [s3 [m3' [STEP12' STEP23']]].
specialize (IHn c3 m3 pf1 pf2 STEP23).
inversion STEP12'; subst m.
subst m'.
assert (c' = c3).
 generalize (@csem_fun_T i).
 unfold corestep_fun, csem_map_T, csem_map, genv_mapT, genvs in *.
 destruct (lt_dec i num_modules); try solve[elimtype False; omega].
 apply Eqdep_dec.inj_pair2_eq_dec in H0; [|solve[apply eq_nat_dec]]. 
 clear IHn; subst c2.
 assert (l = pf_i1) by apply proof_irr.
 rewrite H0 in *.
 intros H10; specialize (H10 _ _ _ _ _ _ _ H8 STEP12).
 solve[inversion H10; auto].
assert (m3' = m3). 
 generalize (@csem_fun_T i).
 unfold corestep_fun, csem_map_T, csem_map, genv_mapT, genvs in *.
 destruct (lt_dec i num_modules); try solve[elimtype False; omega].
 apply Eqdep_dec.inj_pair2_eq_dec in H0; [|solve[apply eq_nat_dec]].
 clear IHn; subst c2.
 assert (l = pf_i1) by apply proof_irr.
 rewrite H0 in *.
 intros H10; specialize (H10 _ _ _ _ _ _ _ H8 STEP12).
 solve[inversion H10; auto].
subst c'; subst m3'.
spec IHn; eauto.
assert (pf_i = pf_i1) as -> by apply proof_irr.
rewrite <-H5 in STEP23'.
subst stack0.
assert (pf1 = pf0) as -> by apply proof_irr.
assert (pf2 = ext_pf0) as -> by apply proof_irr.
solve[apply STEP23'].
apply corestep_not_at_external in STEP12.
unfold csem_map_T, csem_map in STEP12.
destruct (lt_dec i num_modules); try solve[elimtype False; omega].
assert (l = pf_i1) by apply proof_irr.
subst.
apply Eqdep_dec.inj_pair2_eq_dec in H0.
subst.
clear - AT_EXT STEP12.
solve[unfold genv_map in *; congruence].
solve[apply eq_nat_dec].
apply corestep_not_halted in STEP12.
unfold csem_map_T, csem_map in STEP12.
destruct (lt_dec i num_modules); try solve[elimtype False; omega].
assert (l = plt_ok LOOKUP0) by apply proof_irr.
subst.
apply Eqdep_dec.inj_pair2_eq_dec in H0.
subst.
clear - HALTED STEP12.
solve[unfold genv_map in *; congruence].
solve[apply eq_nat_dec].
Qed.

Lemma linking_extension_compilable 
  (cd_init: CompilabilityInvariant.core_datas core_data):
 CompilableExtension.Sig 
 (@linker_core_semantics F_S V_S num_modules cS fS vS 
   procedure_linkage_table plt_ok modules_S entry_points)
 (@linker_core_semantics F_T V_T num_modules cT fT vT 
   procedure_linkage_table plt_ok modules_T entry_points)
 geS geT entry_points.
Proof.
set (R := R_inv).
destruct (@ExtensionCompilability 
 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
 (@linker_core_semantics F_S V_S num_modules cS fS vS 
   procedure_linkage_table plt_ok modules_S entry_points)
 (@linker_core_semantics F_T V_T num_modules cT fT vT 
   procedure_linkage_table plt_ok modules_T entry_points)
 csem_map_S csem_map_T csig esig
 geS geT genv_mapS genv_mapT 
 (@linking_extension F_S V_S Z cS fS vS 
   num_modules procedure_linkage_table plt_ok modules_S csig esig 
   entry_points linkableS_csig_esig)
 (@linking_extension F_T V_T Z cT fT vT 
   num_modules procedure_linkage_table plt_ok modules_T csig esig 
   entry_points linkableT_csig_esig)
 entry_points core_data match_state core_ord threads_max R)
 as [LEM].
apply LEM; auto.
apply linker_core_compatible; auto. 
 clear - domain_eq_S.
 unfold genv_mapS, genvs in domain_eq_S.
 intros k pf_k.
 specialize (domain_eq_S k).
 destruct (lt_dec k num_modules); try solve[elimtype False; omega].
 solve[assert (pf_k = l) as -> by apply proof_irr; auto]. 
apply linker_core_compatible; auto. 
 clear - domain_eq_T.
 unfold genv_mapT, genvs in domain_eq_T.
 intros k pf_k.
 specialize (domain_eq_T k).
 destruct (lt_dec k num_modules); try solve[elimtype False; omega].
 solve[assert (pf_k = l) as -> by apply proof_irr; auto].
clear LEM; constructor; simpl.

(*1*)
intros until cd'; intros H1 H2 [RR [H3 H4]] H5 H6 H7 H8 STEP1 STEP2 ESTEP1 ESTEP2 MATCH'.
simpl in *.
unfold R, R_inv.
destruct s1; destruct s2; simpl in *.
destruct stack.
solve[congruence].
intros; destruct f; simpl in *.
destruct stack0; simpl in RR.
solve[elimtype False; auto].
destruct f; simpl in *.
subst.
destruct (eq_nat_dec i0 i0); try solve[elimtype False; omega].
rewrite <-Eqdep_dec.eq_rect_eq_dec in H1, H2;
 try solve[apply eq_nat_dec].
inv H1; inv H2.
destruct RR as [? [[cd'' MATCH] STACK]]. 
rewrite <-Eqdep_dec.eq_rect_eq_dec in MATCH;
 try solve[apply eq_nat_dec].
generalize STEP2 as STEP2'; intro.
(*unfold csem_map_T, csem_map in STEP2.
destruct (lt_dec i0 num_modules); try solve[elimtype False; omega].
unfold get_module_csem in STEP2.
destruct (modules_T l).*)
apply linker_step_lem2 
 with (s2' := s2') (stack := stack0) (pf_i := PF0) (pf1 := stack_nonempty0)
  (pf2 := callers_at_external0) in STEP2; auto.
subst.
generalize STEP1 as STEP1'; intro.
eapply linker_step_lem1 
 with (stack := stack) (pf_i := PF) (pf1 := stack_nonempty)
  (pf2 := callers_at_external) in STEP1; eauto.
subst.
simpl.
destruct (RGsim i0).
exists (@refl_equal _ i0).
split.
assert
 (Events.mem_unchanged_on (Events.loc_unmapped j) m1 m1' /\
  Events.mem_unchanged_on (Events.loc_out_of_reach j m1) m2 m2') as [MEM1 MEM2].
solve[split; auto].
solve[exists cd'; auto].

clear - H5 H6 H7 H8 PF MATCH' MATCH STACK RGsim H H0.
revert stack0 STACK; induction stack.
intros stack0; destruct stack0; simpl; auto.
intros stack0; destruct stack0; simpl; auto.
destruct a; destruct f.
intros [PF' [[cd MATCH''] STACK']].
subst.
rewrite <-Eqdep_dec.eq_rect_eq_dec in MATCH''; try solve[apply eq_nat_dec].
exists (@refl_equal _ i).
split; auto.
destruct (RGsim i).
rewrite <-Eqdep_dec.eq_rect_eq_dec; try solve[apply eq_nat_dec].
exists cd.
eapply rely; eauto.
rewrite meminj_preserves_genv2blocks.
generalize match_state_preserves_globals.
unfold genv_mapS, genvs.
intros GENVS.
destruct (lt_dec i num_modules); try solve[elimtype False; omega].
assert (l = PF1) by apply proof_irr; subst.
solve[eapply GENVS; eauto].
destruct (RGsim i0).
solve[apply match_state_inj0 with (cd := cd') (c1 := c1') (c2 := c2'); auto].

(*2*)
intros until args1; intros [RR [H1 H2]]; simpl in *.
intros H3 H4 H5 H6 H7 H8 H9 AT_EXT H10 H11.
unfold R, R_inv in *.
destruct s1; destruct s2; simpl in *.
destruct stack.
simpl in stack_nonempty; elimtype False; omega.
destruct f; simpl in *.
destruct stack0.
simpl in stack_nonempty0; elimtype False; omega.
destruct f; simpl in *.
subst.
case_eq (after_external (get_module_rgsem (modules_S PF)) ret1 fc).
2: solve[intros Heq; rewrite Heq in H10; congruence].
intros c1 Heq1.
rewrite Heq1 in H10.
inv H10.
case_eq (after_external (get_module_rgsem (modules_T PF0)) ret2 fc0).
2: solve[intros Heq; rewrite Heq in H11; congruence].
intros c2 Heq2.
rewrite Heq2 in H11.
inv H11.
simpl in *.
destruct RR as [RR1 [[cd' MATCH] RR2]].
exists RR1.
split; auto.
destruct (core_simulations i0).
clear core_ord_wf0 core_diagram0 core_initial0 core_halted0 core_at_external0.
cut (match_state cd' j' fc m1' fc0 m2').
intros MATCH'.
case_eq (at_external (get_module_rgsem (modules_S PF)) fc).
2: solve[intros AT_EXT'; rewrite AT_EXT' in AT_EXT; congruence].
intros [[ef' sig'] args'] AT_EXT'.
rewrite AT_EXT' in AT_EXT.
assert (exists ret1', ret1 = Some ret1') as [ret1' RET1] by admit. (*fix after_external to allow None retval*)
assert (exists ret2', ret2 = Some ret2') as [ret2' RET2] by admit. (*fix after_external to allow None retval*)
assert (val_inject j' ret1' ret2'). 
 unfold val_inject_opt in H1.
 rewrite RET1, RET2 in H1.
 solve[auto].
specialize (core_after_external0 cd' j' j' fc fc0 m1' ef' args' ret1' m1' m2' m2' ret2' sig').
specialize (RGsim i0); destruct RGsim.
spec core_after_external0.
solve[eapply match_state_inj; eauto].
spec core_after_external0; auto.
spec core_after_external0; auto.
unfold csem_map_S, csem_map.
destruct (lt_dec i0 num_modules); try solve[elimtype False; omega].
solve[assert (l = PF) as -> by apply proof_irr; auto].
spec core_after_external0; auto.
solve[eapply match_state_preserves_globals; eauto].
spec core_after_external0; auto.
spec core_after_external0; auto.
solve[apply inject_separated_same_meminj].
spec core_after_external0; eauto.
spec core_after_external0; auto.
spec core_after_external0; auto.
solve[unfold mem_forward; intros; split; auto].
spec core_after_external0.
solve[unfold Events.mem_unchanged_on; split; auto].
spec core_after_external0.
solve[unfold mem_forward; intros; split; auto].
spec core_after_external0.
solve[unfold Events.mem_unchanged_on; split; auto].
spec core_after_external0.
unfold val_has_type_opt in H0.
rewrite RET2 in H0; auto.
admit. (*typing precondition: use "ef_sig e" instead of sig' everywhere*)
destruct core_after_external0 as [cd'' [st1' [st2' [EQ1 [EQ2 MATCH2]]]]].
exists cd''; auto.
rewrite <-RET1, <-RET2 in *.
clear - Heq1 Heq2 EQ1 EQ2 PF MATCH2.
unfold csem_map_S, csem_map_T, csem_map in *|-.
destruct (lt_dec i0 num_modules); try solve[elimtype False; omega].
assert (l = PF) as -> by apply proof_irr.
assert (PF0 = PF) as -> by apply proof_irr.
unfold genv_map in EQ1.
rewrite Heq1 in EQ1; inv EQ1.
unfold genv_map in EQ2.
rewrite Heq2 in EQ2; inv EQ2.
rewrite <-Eqdep_dec.eq_rect_eq_dec; auto.
solve[apply eq_nat_dec].
destruct (RGsim i0).
apply rely with (ge1 := get_module_genv (modules_S PF)) (m1 := m1) (f := j) (m2 := m2); auto.
solve[eapply match_state_inj; eauto].
rewrite meminj_preserves_genv2blocks.
generalize match_state_preserves_globals.
unfold genv_mapS, genvs.
intros GENVS.
destruct (lt_dec i0 num_modules); try solve[elimtype False; omega].
assert (PF = l) as -> by apply proof_irr.
solve[eapply GENVS; eauto].
rewrite <-Eqdep_dec.eq_rect_eq_dec in MATCH; auto.
solve[apply eq_nat_dec].
clear H2 AT_EXT.
clear - RR2 H3 H4 H5 H6 H7 H8 H9 PF RGsim.
revert stack0 RR2; induction stack; auto.
intros stack0 RR2; destruct stack0; simpl in RR2. 
solve[destruct a; elimtype False; auto].
destruct a; destruct f.
destruct RR2 as [PF' [[cd' MATCH] INV]].
subst.
simpl.
exists (@refl_equal _ i).
split; auto.
exists cd'.
rewrite <-Eqdep_dec.eq_rect_eq_dec in *; auto; 
 try solve[apply eq_nat_dec].
destruct (RGsim i).
apply rely with (ge1 := get_module_genv (modules_S PF0)) (m1 := m1) (f := j) (m2 := m2); auto.
solve[eapply match_state_inj; eauto].
rewrite meminj_preserves_genv2blocks.
generalize match_state_preserves_globals.
unfold genv_mapS, genvs.
intros GENVS.
destruct (lt_dec i num_modules); try solve[elimtype False; omega].
assert (PF0 = l) as -> by apply proof_irr.
solve[eapply GENVS; eauto].

(*3: extension_diagram*)
unfold CompilabilityInvariant.match_states; simpl. 
intros until j; intros H1 H2 H3 H4 H5 H6; intros [RR [H7 H8]] H9 H10 H11 H12 STEP.
inv STEP; simpl in *; subst.
(*'run' case*)
elimtype False.
clear - H1 H5 H13 pf_i.
unfold csem_map_S in H5.
apply corestep_not_at_external in H13.
unfold csem_map in H5.
destruct (lt_dec (linker_active s2) num_modules); try solve[omega].
destruct (eq_nat_dec (linker_active s2) (linker_active s2)); try solve[omega].
rewrite dependent_types_nonsense in H1; inv H1.
assert (Heq: l = pf_i) by apply proof_irr; auto.
solve[subst; unfold init_data, genv_map in *; rewrite H5 in H13; congruence].

(*'link' case*)
destruct (eq_nat_dec (linker_active s2) (linker_active s2)); try solve[omega].
rewrite dependent_types_nonsense in H1; inv H1.
rename j0 into k.
destruct (core_simulations k).
specialize (core_initial0 (Vptr b (Int.repr 0)) (Vptr b (Int.repr 0)) sig).
spec core_initial0; auto.
assert (sig = sig0) as ->.
 clear - H5 AT_EXT.
 unfold csem_map_S, csem_map in H5.
 destruct (lt_dec (linker_active s2) num_modules); try solve[elimtype False; omega].
 assert (Heq: l = pf_i) by apply proof_irr; auto; subst.
 unfold init_data, genv_map in *.
 solve[rewrite H5 in AT_EXT; inv AT_EXT; auto].
solve[auto].
specialize (core_initial0 args1 c' m1' j args2 m2).
spec core_initial0; auto.
clear - H5 AT_EXT H15.
unfold csem_map_S, csem_map in H5.
destruct (lt_dec (linker_active s2) num_modules); try solve[elimtype False; omega].
assert (Heq: l = pf_i) by apply proof_irr; auto.
unfold init_data, genv_map in *.
subst; rewrite H5 in AT_EXT; inv AT_EXT.
unfold csem_map_S, csem_map, genv_mapS, genvs.
generalize (plt_ok LOOKUP) as plt_ok'; intro.
destruct (lt_dec k num_modules); try solve[elimtype False; omega].
assert (Heq: l = plt_ok LOOKUP) by apply proof_irr; auto.
solve[subst; auto].
spec core_initial0; auto.
spec core_initial0; auto.
spec core_initial0; auto.
destruct core_initial0 as [cd' [c'' [INIT MATCH]]].
destruct s2; simpl in H2; induction stack0.
solve[simpl in stack_nonempty; elimtype False; omega].
destruct a.
destruct (eq_nat_dec i i); try solve[elimtype False; omega].
rewrite dependent_types_nonsense in H2.
inversion H2; rewrite H7 in *; clear H7.
simpl in *.
destruct RR as [RR1 [RR2 STACK_INV]].
generalize STACK_INV as STACK_INV'; intro.
apply stack_inv_length_eq in STACK_INV. 
assert (CALLERS: 
 all_at_external fT vT modules_T (List.tail (mkFrame k (plt_ok LOOKUP) c'' :: 
  mkFrame i pf_i c2 :: stack0))).
 simpl.
 apply List.Forall_cons.
 exists ef; exists sig; exists args2.
 generalize H6.
 unfold csem_map_T, csem_map.
 destruct (lt_dec i num_modules); try solve[elimtype False; omega].
 solve[assert (l = pf_i) as -> by apply proof_irr; auto].
 solve[apply callers_at_external].
exists (mkLinkerCoreState (mkFrame k (plt_ok LOOKUP) c'' :: 
  mkFrame i pf_i c2 :: stack0) (length_cons _ _) CALLERS).
exists m2.
exists (@ExtendedSimulations.core_datas_upd _ k cd' cd).
exists j.
split; auto.
split; auto.
solve[apply inject_separated_same_meminj].
split.
split.
inv STACK_INV.
rewrite H7 in *.
exists (@refl_equal _ k).
destruct RR2 as [cd'' RR2].
split.
solve[eexists; eauto].
exists RR1; split.
solve[exists cd''; eauto].
solve[auto].

split; auto.
intros.
destruct (eq_nat_dec i0 k).
subst.
rewrite dependent_types_nonsense in H1.
inv H1.
exists c''.
split; auto.
simpl.
destruct (eq_nat_dec k k); try solve[elimtype False; omega].
solve[rewrite dependent_types_nonsense; auto].
solve[rewrite ExtendedSimulations.core_datas_upd_same; auto].
congruence.

split. solve[unfold mem_unchanged_on; split; auto].
split. solve[unfold mem_unchanged_on; split; auto].

left.
exists O; simpl.
exists (mkLinkerCoreState 
 (mkFrame k (plt_ok LOOKUP) c'' :: mkFrame i pf_i c2 :: stack0) (length_cons _ _) CALLERS).
exists m2.
split; auto.
assert (Heq: pf_i = PF) by apply proof_irr; auto.
subst pf_i.
apply link_call 
 with (args := args2) (sig := sig) (b := b); auto.
specialize (H8 i c1).
spec H8.
destruct (eq_nat_dec i i); try solve[elimtype False; omega].
solve[rewrite dependent_types_nonsense; auto].
destruct H8 as [c2' H8].
destruct (eq_nat_dec i i); try solve[elimtype False; omega].
rewrite dependent_types_nonsense in H8.
destruct H8 as [H8 H16].
inv H8.
unfold csem_map_T, csem_map in H6.
destruct (lt_dec i num_modules); try solve[elimtype False; omega].
assert (l = PF) as -> by apply proof_irr; auto.
clear - H5 AT_EXT H6. 
unfold csem_map_S, csem_map in H5.
destruct (lt_dec i num_modules); try solve[elimtype False; omega].
assert (l = PF) by apply proof_irr; auto; subst.
unfold genv_map, init_data in *.
solve[rewrite H5 in AT_EXT; inv AT_EXT; auto].
clear - domain_eq_T.
unfold genv_mapT, genvs in domain_eq_T.
intros k pf_k.
specialize (domain_eq_T k).
destruct (lt_dec k num_modules); try solve[elimtype False; omega].
solve[assert (pf_k = l) as -> by apply proof_irr; auto].
clear - agree_S agree_ST agree_T H13 LOOKUP plt_ok.
unfold genvs_agree in agree_S, agree_ST, agree_T.
destruct (agree_S (plt_ok LOOKUP)) as [H1 _].
destruct (agree_ST (plt_ok LOOKUP)) as [H2 _].
destruct (agree_T (plt_ok LOOKUP)) as [H3 _].
specialize (H1 id).
rewrite H1 in H13.
specialize (H2 id).
rewrite H13 in H2.
specialize (H3 id).
solve[rewrite <-H2 in H3; auto].
assert (sig = sig0) as ->.
 clear - H5 AT_EXT.
 unfold csem_map_S, csem_map in H5.
 destruct (lt_dec i num_modules); try solve[elimtype False; omega].
 assert (Heq: l = PF) by apply proof_irr; auto; subst.
 unfold genv_map, init_data in *.
 solve[rewrite H5 in AT_EXT; inv AT_EXT; auto].
solve[auto].
unfold csem_map_T, csem_map, genv_mapT, genvs in INIT.
generalize (plt_ok LOOKUP) as plt_ok'; intro.
destruct (lt_dec k num_modules); try solve[elimtype False; omega].
solve[assert (plt_ok' = l) as -> by apply proof_irr; auto].
congruence. 

(*'return' case*)
destruct (eq_nat_dec (linker_active s2) (linker_active s2)); try solve[omega].
inv H1.
rewrite dependent_types_nonsense in H3, H5.
edestruct (@at_external_halted_excl 
 (Genv.t (fS (linker_active s2)) (vS (linker_active s2)))
 (blockmap*cS (linker_active s2)) mem 
 (list (ident * globdef (fS (linker_active s2)) (vS (linker_active s2)))) 
 (csem_map_S (linker_active s2)) c').
congruence.
elimtype False; clear - HALTED LOOKUP H1 plt_ok.
generalize (plt_ok LOOKUP) as plt_ok'; intro.
unfold csem_map_S, csem_map in H1.
destruct (lt_dec (linker_active s2) num_modules); try solve[omega].
assert (Heq: l = plt_ok LOOKUP) by apply proof_irr; auto.
unfold genv_map, init_data in *.
solve[subst; congruence].
congruence.

(*4: at_external_match*)
intros until j; intros H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12.
destruct s1; destruct s2; simpl in *.
destruct stack; try solve[congruence].
destruct stack0; try solve[congruence].
destruct f; destruct f0.
unfold csem_map_S, csem_map_T, csem_map in *.
destruct (lt_dec i num_modules); try solve[elimtype False; omega].
assert (l = PF) by apply proof_irr; auto; subst.
destruct (eq_nat_dec i0 i0); try solve[elimtype False; omega].
rewrite dependent_types_nonsense in H2, H3.
inv H2; inv H3.
unfold genv_map, init_data in *.
rewrite H6 in H5.
assert (PF = PF0) as -> by apply proof_irr; auto.
rewrite H12.
destruct ef; auto.
solve[destruct (procedure_linkage_table name); try solve[congruence]].

(*5: make_initial_core_diagram*)
intros until sig; intros H1 H2 H3 H4 H5.
destruct s1; simpl in *.
unfold linker_make_initial_core in H2.
case_eq v1.
solve[intros V; rewrite V in *; try solve[congruence]].
intros i V.
rewrite V in H2.
destruct v1; try solve[congruence].
intros f V.
rewrite V in H2.
congruence.
intros b i V.
rewrite V in H2.
case_eq (Genv.find_symbol geS main_id).
2: solve[intros H6; rewrite H6 in H2; destruct v1; congruence].
intros b' H6.
rewrite H6 in H2.
if_tac in H2; try solve[congruence].
case_eq (procedure_linkage_table main_id); try solve[congruence].
intros n PLT.
case_eq
 (make_initial_core (get_module_rgsem (modules_S (plt_ok PLT)))
   (get_module_genv (modules_S (plt_ok PLT))) 
   (Vptr b i) vals1); try solve[congruence].
intros c Heq; inv Heq.
destruct (core_simulations n).
specialize (core_initial0 (Vptr b' i) v2 sig H1 vals1 c m1 j vals2 m2).
spec core_initial0; auto.
unfold csem_map_S, csem_map, genv_mapS, genvs.
generalize (plt_ok PLT); intro.
destruct (lt_dec n num_modules); try solve[elimtype False; omega].
solve[assert (l = plt_ok PLT) as -> by apply proof_irr; auto].
spec core_initial0; auto.
spec core_initial0; auto.
spec core_initial0; auto.
destruct core_initial0 as [cd' [c2 [INIT MATCH]]].
assert (exists cd: CompilabilityInvariant.core_datas core_data, True) as [cd _].
 solve[eexists; eauto].
exists (ExtendedSimulations.core_datas_upd _ n cd' cd).
exists (mkLinkerCoreState (mkFrame n (plt_ok PLT) c2 :: nil) (length_cons _ _)
 (all_at_external_consnil _ _ _ _)).
simpl; split; auto.
unfold linker_make_initial_core.
case_eq v2.
clear - entry_points_eq H1.
specialize (entry_points_eq (Vptr b' i) v2 sig H1).
destruct entry_points_eq as [b [ofs [VPTR1 VPTR2]]].
solve[rewrite VPTR2; intros; congruence].
specialize (entry_points_eq (Vptr b' i) v2 sig H1).
destruct entry_points_eq as [b [ofs [VPTR1 VPTR2]]].
solve[rewrite VPTR2; intros; congruence].
specialize (entry_points_eq (Vptr b' i) v2 sig H1).
destruct entry_points_eq as [b [ofs [VPTR1 VPTR2]]].
solve[rewrite VPTR2; intros; congruence].
intros b ofs V.
rewrite V in *.
assert (Genv.find_symbol geT main_id = Some b) as ->.
 cut (b' = b).
 intros <-.
 clear - H6 agree_S agree_ST agree_T PLT plt_ok.
 specialize (agree_S (plt_ok PLT)).
 unfold genvs_agree in *.
 destruct agree_S as [H1 H2].
 rewrite H1 in H6.
 specialize (agree_ST (plt_ok PLT)).
 destruct agree_ST as [H3 H4].
 rewrite H3 in H6.
 specialize (agree_T (plt_ok PLT)).
 destruct agree_T as [H5 H7].
 solve[rewrite <-H5 in H6; auto].
 clear - H6 H1 entry_points_eq.  
 specialize (entry_points_eq (Vptr b' i) (Vptr b ofs) sig H1). 
 destruct entry_points_eq as [b0 [ofs0 [EQ1 EQ2]]].
 solve[inv EQ1; inv EQ2; auto].
if_tac; try solve[elimtype False; omega].
generalize (refl_equal (procedure_linkage_table main_id)).
generalize PLT.
pattern (procedure_linkage_table main_id) at 0 2 4.
rewrite PLT in *.
intros ? ?.
unfold csem_map_T, csem_map, genv_mapT, genvs in INIT.
generalize (plt_ok PLT); intro.
destruct (lt_dec n num_modules); try solve[elimtype False; omega].
assert (plt_ok (eq_sym e) = l) as -> by apply proof_irr; auto.
unfold genv_map in INIT.
rewrite INIT.
solve[assert (l = plt_ok PLT0) as -> by apply proof_irr; auto].

revert H2.
generalize (refl_equal (procedure_linkage_table main_id)).
generalize PLT.
pattern (procedure_linkage_table main_id) at 0 2 4.
rewrite PLT in *.
intros ? e.
assert (plt_ok (eq_sym e) = plt_ok PLT) as -> by apply proof_irr.
rewrite H7.
inversion 1; subst.
split.
unfold R, R_inv; simpl.
exists (@refl_equal _ n).
split; auto.
exists cd'; auto.
simpl.
split; auto.
intros i0 c1 H10.
destruct (eq_nat_dec i0 n); try solve[congruence]; subst.
rewrite dependent_types_nonsense in H10.
inv H10.
exists c2.
split; auto.
solve[rewrite ExtendedSimulations.core_datas_upd_same; auto].

intros H7.
revert H2.
generalize (refl_equal (procedure_linkage_table main_id)).
generalize PLT.
pattern (procedure_linkage_table main_id) at 0 2 4.
rewrite PLT in *.
intros ? e.
assert (plt_ok (eq_sym e) = plt_ok PLT) as -> by apply proof_irr.
rewrite H7.
solve[intros; congruence].

intros H7.
revert H2.
generalize (refl_equal (procedure_linkage_table main_id)).
generalize H7.
pattern (procedure_linkage_table main_id) at 0 2 4.
rewrite H7 in *.
intros ? e.
solve[intros; congruence].

(*6: safely_halted_step*)
intros until v1.
intros H1 H2.
unfold linker_safely_halted in H2.
destruct c1; try solve[congruence].
case_eq stack.
intros Hstack; rewrite Hstack in *; congruence.
intros f stack' Hstack.
rewrite Hstack in *.
destruct f.
case_eq stack'.
intros Hstack'; rewrite Hstack' in H2.
2: solve[intros ? ? Hstack'; rewrite Hstack' in H2; congruence].
destruct (core_simulations i).
unfold CompilabilityInvariant.match_states in H1.
destruct H1 as [RR [H1 H3]].
simpl in *. 
specialize (H3 (linker_active c2)).
rewrite Hstack in H1, H3.
subst i.
destruct (eq_nat_dec (linker_active c2) (linker_active c2)); try solve[elimtype False; omega].
specialize (H3 fc).
rewrite dependent_types_nonsense in H3.
spec H3; auto.
destruct H3 as [c3 [H3 H4]].
generalize core_halted0; intro core_halted1.
specialize (core_halted1 (cd (linker_active c2)) j fc m1 c3 m2 v1 H4).
spec core_halted1; auto.
generalize H2.
unfold csem_map_S, csem_map.
destruct (lt_dec (linker_active c2) num_modules); try solve[elimtype False; omega].
solve[assert (PF = l) as -> by apply proof_irr; auto].
destruct core_halted1 as [v2 [H5 [H6 H7]]].
exists v2.
split; auto.
split; auto.
unfold linker_safely_halted.
destruct c2.
destruct stack0.
simpl in stack_nonempty0; elimtype False; omega.
destruct f.
simpl in H6.
unfold csem_map_T, csem_map in H6.
destruct (lt_dec i num_modules); try solve[elimtype False; omega].
assert (PF0 = l) as -> by apply proof_irr; auto.
simpl in H3.
destruct (eq_nat_dec i i); try solve[elimtype False; omega].
rewrite dependent_types_nonsense in H3.
inversion H3.
subst c3.
destruct stack0; auto.
generalize RR.
rewrite Hstack.
simpl.
rewrite Hstack'.
simpl.
solve[intros [? [? FALSE]]; elimtype False; auto].

(*7: safely_halted_diagram*)
intros until c2; intros H1 H2 H3 H4 H5.
destruct (core_simulations (linker_active s1)).
generalize core_halted0.
intro core_halted1.
specialize (core_halted1 (cd (linker_active s1)) j c1 m1 c2 m2 rv1).
spec core_halted1; auto.
destruct H1 as [RR [H6 H7]].
simpl in *.
destruct (H7 (linker_active s1) c1 H2) as [c1' [H8 H9]].
rewrite H3 in H8.
solve[inv H8; auto].
spec core_halted1; auto.
destruct core_halted1 as [v2 [INJ [HALT INJ']]].
exists v2.
split; auto.
split; auto.
clear INJ'.
inv H5.
elimtype False; clear - H2 H4 H6.
apply corestep_not_halted in H6.
generalize H4; unfold csem_map_S, csem_map; simpl.
simpl in *.
destruct (lt_dec i num_modules); try solve[elimtype False; omega].
assert (l = pf_i) as -> by apply proof_irr; auto.
simpl in H2.
destruct (eq_nat_dec i i); try solve[elimtype False; omega].
rewrite dependent_types_nonsense in H2; inversion H2; subst c1.
unfold genv_map, init_data in *.
solve[rewrite H6; intros; congruence].
simpl in H2.
destruct (eq_nat_dec i i); try solve[elimtype False; omega].
rewrite dependent_types_nonsense in H2; inversion H2; subst c1.
simpl in H4.
unfold csem_map_S, csem_map in H4.
destruct (lt_dec i num_modules); try solve[elimtype False; omega].
generalize @at_external_halted_excl; intros H5.
specialize (H5 _ _ _ _ (get_module_rgsem (modules_S l)) c).
unfold genv_map, init_data in *.
rewrite H4 in H5.
assert (Heq: l = pf_i) by apply proof_irr; auto.
rewrite Heq in *.
rewrite AT_EXT in H5.
solve[destruct H5; congruence].
simpl in H2.
destruct (eq_nat_dec j0 j0); try solve[elimtype False; omega].
rewrite dependent_types_nonsense in H2; inversion H2; subst c1.
destruct s2.
simpl in *.
destruct stack0; try solve[congruence].
destruct f.
destruct (eq_nat_dec j0 i0); try solve[congruence]; subst.
rewrite dependent_types_nonsense in H3; inversion H3; subst fc.
destruct H1 as [RR [H1 H7]].
simpl in *.
unfold R, R_inv in *.
destruct RR as [RR1 [RR2 RR3]].
destruct stack0; try solve[elimtype False; auto].
destruct f.
specialize (H7 i0 c').
destruct (eq_nat_dec i0 i0); try solve[elimtype False; omega].
spec H7.
solve[rewrite dependent_types_nonsense; auto].
destruct H7 as [c3 [H7 H7']].
rewrite dependent_types_nonsense in H7.
inv H7.
destruct RR2 as [cd' MATCH].
clear e H2 H1 e0 H3.
destruct RR3 as [RR [[cd'' RR2] RR3]].
subst i1.
generalize ext_pf.
unfold all_at_external.
inversion 1; subst.
destruct H3 as [ef [sig [args AT_EXT]]].
clear core_after_external0.
destruct (core_simulations i).
clear core_ord_wf0 core_diagram0 core_initial0 core_halted0 core_at_external0.
specialize (core_after_external0 
 cd'' j j c fc m1' ef args rv1 m1' m2 m2 v2 sig).
specialize (RGsim i); destruct RGsim.
spec core_after_external0.
solve[eapply match_state_inj; eauto].
spec core_after_external0; auto.
spec core_after_external0; auto.
unfold csem_map_S, csem_map.
destruct (lt_dec i num_modules); try solve[elimtype False; omega].
solve[assert (l = pf_i) as -> by apply proof_irr; auto].
spec core_after_external0; auto.
solve[eapply match_state_preserves_globals; eauto].
spec core_after_external0; auto.
spec core_after_external0; auto.
solve[apply inject_separated_same_meminj].
spec core_after_external0; eauto.
spec core_after_external0; auto.
spec core_after_external0; auto.
solve[unfold mem_forward; intros; split; auto].
spec core_after_external0.
solve[unfold Events.mem_unchanged_on; split; auto].
spec core_after_external0.
solve[unfold mem_forward; intros; split; auto].
spec core_after_external0.
solve[unfold Events.mem_unchanged_on; split; auto].
spec core_after_external0.
admit. (*safely_halted_diagram: add typing precondition: Val.has_type retv (proj_sig_res sig) *)
destruct core_after_external0 as 
 [cd2 [_c [_c0 [AFTER1 [AFTER2 MATCH12]]]]].
assert (CALLERS: all_at_external fT vT modules_T stack0).
 solve[eapply all_at_external_cons; eauto].
exists 
 (mkLinkerCoreState (mkFrame i pf_i _c0 :: stack0) (length_cons _ _) CALLERS).
exists m2.
exists (ExtendedSimulations.core_datas_upd _ i cd2 cd).
exists j.
split; auto.
split.
solve[apply inject_separated_same_meminj].
split.
assert (pf_i = PF0) as -> by apply proof_irr.
assert (PF = plt_ok LOOKUP) as -> by apply proof_irr.

destruct (core_simulations i0).
clear core_ord_wf0 core_diagram0 core_initial0 core_at_external0 core_after_external0.
specialize (core_halted0 (cd i0) j c' m1' c3 m2 rv1).
spec core_halted0; auto.
spec core_halted0; auto.
destruct core_halted0 as [v2' [? [? ?]]].
apply link_return with (retv := v2'); auto.
unfold csem_map_T, csem_map in H7.
destruct (lt_dec i0 num_modules); try solve[elimtype False; omega].
solve[assert (plt_ok LOOKUP = l) as -> by apply proof_irr; auto].
intros k pf_k.
unfold genv_mapT, genvs in domain_eq_T.
specialize (domain_eq_T k).
destruct (lt_dec k num_modules); try solve[elimtype False; omega].
solve[assert (pf_k = l) as -> by apply proof_irr; auto].
unfold csem_map_T, csem_map in AFTER2.
cut (v2' = v2).
intros ->.
destruct (lt_dec i num_modules); try solve[elimtype False; omega].
solve[assert (PF0 = l) as -> by apply proof_irr; auto].
clear - H7 HALT.
rewrite H7 in HALT.
solve[inv HALT; auto].
split.
split.
simpl.
exists (@refl_equal _ i).
split; auto.
cut (c'' = _c).
intros ->.
solve[exists cd2; auto].
cut (retv = rv1).
intros ->.
clear - AFTER1 H6 PF0.
unfold csem_map_S, csem_map in AFTER1.
destruct (lt_dec i num_modules); try solve[elimtype False; omega].
assert (Heq: l = pf_i) by apply proof_irr.
subst l.
unfold genv_map, init_data in *.
rewrite AFTER1 in H6.
solve[inv H6; auto].
clear - HALTED H4 PF.
unfold csem_map_S, csem_map in H4.
destruct (lt_dec i0 num_modules); try solve[elimtype False; omega].
assert (l = plt_ok LOOKUP) by apply proof_irr; subst.
unfold genv_map, init_data in *.
solve[rewrite H4 in HALTED; inv HALTED; auto].
split; auto.
simpl.
intros i1 c1 H1.
destruct (eq_nat_dec i1 i); try solve[congruence].
subst.
rewrite dependent_types_nonsense in H1.
inv H1.
exists _c0.
split; auto.
rewrite ExtendedSimulations.core_datas_upd_same.
cut (c1 = _c).
solve[intros ->; auto].
cut (rv1 = retv).
intros ->.
clear - AFTER1 H6 PF0.
unfold csem_map_S, csem_map in AFTER1.
destruct (lt_dec i num_modules); try solve[elimtype False; omega].
assert (Heq: l = pf_i) by apply proof_irr.
subst l.
unfold genv_map, init_data in *.
rewrite AFTER1 in H6.
solve[inv H6; auto].
clear - HALTED H4 PF.
unfold csem_map_S, csem_map in H4.
destruct (lt_dec i0 num_modules); try solve[elimtype False; omega].
assert (l = plt_ok LOOKUP) by apply proof_irr; subst.
unfold genv_map, init_data in *.
solve[rewrite H4 in HALTED; inv HALTED; auto].

solve[split; split; auto].
Qed.

End LinkerCompilable.


  
