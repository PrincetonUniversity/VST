Require Import msl.base. (*for spec tac*)

Require Import sepcomp.core_semantics.
Require Import sepcomp.forward_simulations.
Require Import sepcomp.rg_forward_simulations.
Require Import sepcomp.step_lemmas.
Require Import sepcomp.extspec.
Require Import sepcomp.extension.
Require Import sepcomp.extension_safety.
Require Import sepcomp.extension_simulations.
Require Import sepcomp.extension_proof.
Require Import sepcomp.Address.
Require Import sepcomp.mem_lemmas.
Require Import sepcomp.Coqlib2. 
Require Import sepcomp.wf_lemmas.

Require Import Axioms.
Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import compcert.common.Values.
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
 (csem: RelyGuaranteeSemantics (Genv.t F V) C (*(list (ident * globdef F V))*)),
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
 (modules: forall i: nat, i < num_modules -> CompCertModule.Sig (fT i) (vT i) (cT i))
 (entry_points: list (val*val*signature)).

Implicit Arguments plt_ok [].

Definition all_at_external (l: call_stack cT num_modules) :=
 List.Forall (fun (f:frame cT num_modules) => match f with mkFrame i pf_i c => 
  exists ef, exists sig, exists args,
   at_external (get_module_csem (modules pf_i)) c = Some (ef, sig, args)
  end) l.

Fixpoint private_blocks (stack: call_stack cT num_modules) b :=
 match stack with 
 | nil => False
 | mkFrame i pf_i c_i :: stack' => 
   private_block (get_module_csem (modules pf_i)) c_i b \/ private_blocks stack' b
 end.

Inductive linker_corestate: Type := mkLinkerCoreState: forall
 (stack: call_stack cT num_modules)
 (stack_nonempty: length stack >= 1)
 (callers_at_external: all_at_external (List.tail stack)),
 linker_corestate.

Implicit Arguments mkLinkerCoreState [].

Definition genvs_agree (F1 F2 V1 V2: Type) (ge1: Genv.t F1 V1) (ge2: Genv.t F2 V2) :=
  (forall id: ident, Genv.find_symbol ge1 id=Genv.find_symbol ge2 id) /\
  (forall b v1 v2,
    PTree.get b (Genv.genv_vars ge1) = Some v1 -> PTree.get b (Genv.genv_vars ge2) = Some v2 ->  
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
  corestep (get_module_csem (modules pf_i)) (get_module_genv (modules pf_i)) c m c' m' ->
  linker_corestep ge
   (mkLinkerCoreState (mkFrame i pf_i c :: stack) pf ext_pf) m
   (mkLinkerCoreState (mkFrame i pf_i c' :: stack) pf ext_pf) m'

(** 'link' steps *)
| link_call: forall ge stack i j args id sig b (c: cT i) m (pf_i: i < num_modules) c' 
   (LOOKUP: procedure_linkage_table id = Some j) 
   (NEQ_IJ: i<>j) (** 'external' functions cannot be defined within this module *)
   (AT_EXT: at_external (get_module_csem (modules pf_i)) c = 
     Some (EF_external id sig, sig, args)) pf ext_pf ext_pf',
  (forall (k: nat) (pf_k: k<num_modules), genvs_agree ge (get_module_genv (modules pf_k))) ->
  (forall (k: nat) (pf_k: k<num_modules), genvs_domain_eq ge (get_module_genv (modules pf_k))) ->
  Genv.find_symbol ge id = Some b -> 
  In (Vptr b (Int.repr 0), Vptr b (Int.repr 0), sig) entry_points -> 
  initial_core 
   (get_module_csem (modules (plt_ok id j LOOKUP)))
   (get_module_genv (modules (plt_ok id j LOOKUP))) (Vptr b (Int.repr 0)) args = Some c' -> 

  linker_corestep ge
   (mkLinkerCoreState (mkFrame i pf_i c :: stack) pf ext_pf) m
   (mkLinkerCoreState 
     (mkFrame j (plt_ok id j LOOKUP) c' :: mkFrame i pf_i c :: stack) (length_cons _ _) ext_pf') m

(** 'return' steps *)
| link_return: forall ge stack i j c m (pf_i: i < num_modules) c' c'' retv ef sig args pfj
   (AT_EXT: at_external (get_module_csem (modules pf_i)) c = Some (ef, sig, args)) 
   (HALTED: halted (get_module_csem (modules pfj)) c' = Some retv) 
   (TYCHECKS: val_has_type_opt (Some retv) (ef_sig ef)) (*FIXME: allow retv = None*) 
   pf ext_pf ext_pf',
  (forall (k: nat) (pf_k: k<num_modules), genvs_agree ge (get_module_genv (modules pf_k))) ->
  (forall (k: nat) (pf_k: k<num_modules), genvs_domain_eq ge (get_module_genv (modules pf_k))) ->
  after_external (get_module_csem (modules pf_i)) (Some retv) c = Some c'' -> 
  linker_corestep ge
   (mkLinkerCoreState 
     (mkFrame j pfj c' :: mkFrame i pf_i c :: stack) pf ext_pf) m
   (mkLinkerCoreState (mkFrame i pf_i c'' :: stack) (length_cons _ _) ext_pf') m.

Definition linker_at_external (s: linker_corestate) := 
  match s with
  | mkLinkerCoreState nil _ _ => None
  | mkLinkerCoreState (mkFrame i pf_i c :: call_stack) _ _ =>
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
Implicit Arguments linker_at_external [].

Definition linker_after_external (retv: option val) (s: linker_corestate) :=
  match s with
  | mkLinkerCoreState nil _ _ => None
  | mkLinkerCoreState (mkFrame i pf_i c :: call_stack) _ ext_pf =>
    match after_external (get_module_csem (modules pf_i)) retv c with
    | None => None
    | Some c' => Some (mkLinkerCoreState (mkFrame i pf_i c' :: call_stack) 
       (length_cons _ _) ext_pf)
    end
  end.

Definition linker_halted (s: linker_corestate) :=
  match s with
  | mkLinkerCoreState nil _ _ => None
  | mkLinkerCoreState (mkFrame i pf_i c :: nil) _ _ =>
     halted (get_module_csem (modules pf_i)) c
  | mkLinkerCoreState (mkFrame i pf_i c :: call_stack) _ _ => None
  end.

Definition main_id := 1%positive. (*hardcoded*)

Definition linker_initial_mem (ge: Genv.t F V) (m: mem) (init_data: list (ident * globdef F V)) := 
  mem_wd m /\
  Genv.alloc_globals ge Mem.empty init_data = Some m.

Definition linker_initial_core (ge: Genv.t F V) (f: val) (args: list val) :=
  match f, Genv.find_symbol ge main_id with
  | Vptr b ofs, Some b' => 
    if eq_block b b' then 
       (match procedure_linkage_table main_id as x 
          return (x = procedure_linkage_table main_id -> option linker_corestate) with
       | None => fun _ => None (** no module defines 'main' *)
       | Some i => fun pf => 
         match initial_core (get_module_csem (modules (@plt_ok main_id i (eq_sym pf)))) 
                 (get_module_genv (modules (@plt_ok main_id i (eq_sym pf)))) f args with
         | None => None
         | Some c => Some (mkLinkerCoreState (mkFrame i (plt_ok main_id i (eq_sym pf)) c :: nil) 
                             (length_cons _ _) (all_at_external_consnil _))
         end 
       end) (refl_equal _)
     else None
   | _, _ => None (** either no 'main' was defined or [f] is not a [Vptr] *)
   end.

Program Definition linker_core_semantics: 
  CoreSemantics (Genv.t F V) linker_corestate mem (*(list (ident * globdef F V)) *):=
 Build_CoreSemantics (*_*) _ _ _ 
  (*deprecated: linker_initial_mem*) 
  linker_initial_core
  linker_at_external
  linker_after_external
  linker_halted
  linker_corestep _ _ _ _.
Next Obligation.
inv H.
apply corestep_not_at_external in H2.
solve[simpl; rewrite H2; auto].
simpl; rewrite AT_EXT, LOOKUP; auto.
simpl.
destruct (at_external_halted_excl (get_module_csem (modules pfj)) c')
 as [H3|H3].
solve[rewrite H3; auto].
solve[rewrite H3 in HALTED; congruence].
Qed.
Next Obligation.
inv H.
apply corestep_not_halted in H2.
simpl; destruct stack; auto.
destruct (at_external_halted_excl (get_module_csem (modules pf_i)) c) 
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
case_eq (after_external (get_module_csem (modules PF)) retv c).
intros c' H2; rewrite H2 in H.
inv H; apply after_at_external_excl in H2.
simpl; rewrite H2; auto.
case_eq (after_external (get_module_csem (modules PF)) retv c).
solve[intros c' H2; rewrite H2 in H; intro; congruence].
intros H2 H3.
solve[rewrite H2 in H; congruence].
Qed.

Program Definition linker_coop_core_semantics: 
  CoopCoreSem (Genv.t F V) linker_corestate (*(list (ident * globdef F V)) *):=
 Build_CoopCoreSem (*_*) _ _
  linker_core_semantics _ _ (*_*).
Next Obligation.
inv CS.
apply corestep_fwd in H1; auto.
apply mem_forward_refl.
apply mem_forward_refl.
Qed.
Next Obligation.
inv CS; auto.
apply corestep_wdmem in H2; auto.
Qed.
(*initial_mem deprecated Next Obligation. 
unfold linker_initial_mem in H.
destruct H; auto.
Qed.*)

Program Definition rg_linker_core_semantics: 
  RelyGuaranteeSemantics (Genv.t F V) linker_corestate (*(list (ident * globdef F V)) *) :=
 Build_RelyGuaranteeSemantics (*_*) _ _ 
 linker_coop_core_semantics
 (fun c b => match c with mkLinkerCoreState stack _ _ => private_blocks stack b end)
 _ _ _ _.
Next Obligation.
destruct c.
clear stack_nonempty callers_at_external.
induction stack.
solve[right; auto].
destruct a.
simpl.
destruct (private_dec (get_module_csem (modules PF)) c b).
solve[left; auto].
destruct IHstack.
solve[left; auto].
right.
intros CONTRA.
solve[destruct CONTRA; auto].
Qed.
Next Obligation.
destruct c.
intros CONTRA.
rename H into H2.
unfold linker_initial_core in H2.
case_eq v.
rename V into V'.
solve[intros V; rewrite V in *; try solve[congruence]].
intros i V2.
rewrite V2 in H2.
congruence.
intros i V2.
rewrite V2 in H2.
congruence.
intros f V2.
rewrite V2 in H2.
congruence.
intros b' i V2.
rewrite V2 in H2.
case_eq (Genv.find_symbol ge0 main_id).
2: solve[intros H6; rewrite H6 in H2; destruct v; congruence].
intros b1 H6.
rewrite H6 in H2.
if_tac in H2; try solve[congruence].
case_eq (procedure_linkage_table main_id); try solve[congruence].
intros n PLT.
revert H2.
generalize (refl_equal (procedure_linkage_table main_id)).
generalize PLT.
pattern (procedure_linkage_table main_id) at 0 2 4.
rewrite PLT.
intros ? ?.
subst.
case_eq
 (initial_core 
   (get_module_csem (modules (plt_ok main_id n (eq_sym e))))
   (get_module_genv (modules (plt_ok main_id n (eq_sym e))))
   (Vptr b1 i) vs); try solve[congruence].
intros c Heq; inv Heq.
intros H1; inv H1.
simpl in CONTRA.
eapply private_initial in H0.
elimtype False; apply H0.
destruct CONTRA; try solve[elimtype False; auto].
solve[eauto].
intros PLT.
revert H2.
generalize (refl_equal (procedure_linkage_table main_id)).
generalize PLT.
pattern (procedure_linkage_table main_id) at 0 2 4.
rewrite PLT.
intros ? ? ?; congruence.
Qed.
Next Obligation.
destruct c'.
destruct c.
inv H.
simpl in H0.
simpl.
destruct H0; auto.
apply (private_step _ b) in H7; auto.
solve[destruct H7; auto].
apply (private_initial _ b) in H9.
simpl in H0.
destruct H0; auto.
solve[elimtype False; apply H9; auto].
unfold all_at_external in callers_at_external0.
simpl in callers_at_external0.
inv callers_at_external0.
clear H4.
(*destruct H2 as [ef [ef_sig [args AT_EXT]]].*)
simpl in H0.
destruct H0.
simpl.
solve[eapply (private_external _ b) in AT_EXT; eauto].
solve[left; right; right; auto].
Qed.
Next Obligation.
unfold linker_at_external in H.
unfold linker_after_external in H0.
destruct c.
destruct stack.
congruence.
destruct f.
case_eq (at_external (get_module_csem (modules PF)) c).
intros [[ef' sig'] args'] AT_EXT.
2: solve[intros AT_EXT; rewrite AT_EXT in H; congruence].
case_eq (after_external (get_module_csem (modules PF)) retv c).
intros c'' Heq.
rewrite Heq in H0.
inv H0.
simpl in H1|-*.
destruct H1.
eapply (private_external _ b) in Heq; eauto.
right; auto.
intros H2.
rewrite H2 in H0.
congruence.
Qed.

(** Preservation of privacy invariants *)

Fixpoint private_valid_inv m (stack: call_stack cT num_modules) :=
 match stack with
 | nil => True
 | mkFrame i pf_i c_i :: stack' => 
   (forall b, private_block (get_module_csem (modules pf_i)) c_i b -> 
     (b < Mem.nextblock m)%positive) /\
   private_valid_inv m stack'
 end.

Lemma private_valid_inv_fwd: 
  forall m m' stack,
  private_valid_inv m stack -> 
  (Mem.nextblock m <= Mem.nextblock m')%positive -> 
  private_valid_inv m' stack.
Proof.
induction stack; auto.
simpl.
destruct a.
intros [H1 H2] H3.
split; auto.
intros b H4.
assert (b < Mem.nextblock m)%positive.
auto.
xomega.
Qed.

Fixpoint private_disjoint_inv' (i: nat) (pf_i: i < num_modules) 
  c_i (stack: call_stack cT num_modules) := 
 match stack with 
 | nil => True
 | mkFrame k pf_k c_k :: stack' => 
   (forall b, private_block (get_module_csem (modules pf_i)) c_i b -> 
     ~private_block (get_module_csem (modules pf_k)) c_k b) /\
   private_disjoint_inv' pf_i c_i stack'
 end.

Fixpoint private_disjoint_inv (stack: call_stack cT num_modules) :=
  match stack with
  | nil => True
  | mkFrame i pf_i c_i :: stack' => 
    private_disjoint_inv' pf_i c_i stack' /\ private_disjoint_inv stack'
  end.

Lemma private_valid_invariant: 
  forall stack m stack' m' n pf1 pf2 pf1' pf2',
  corestepN rg_linker_core_semantics ge n 
   (mkLinkerCoreState stack pf1 pf2) m (mkLinkerCoreState stack' pf1' pf2') m' -> 
  private_valid_inv m stack -> 
  private_valid_inv m' stack'.
Proof.
intros.
revert stack pf1 pf2 m H H0.
induction n.
simpl.
solve[intros until m; intros H1; inv H1; auto].
intros until m; simpl.
intros [c2 [m2 [STEP STEPN]]].
inv STEP.
simpl.
intros H4.
apply IHn 
 with (stack := mkFrame i pf_i c' :: stack0) (pf1 := pf) (pf2 := ext_pf) (m := m2); auto.
simpl.
destruct H4 as [H4 H5].
split; auto.
intros b H6.
destruct (private_dec (get_module_csem (modules pf_i)) c b).
cut (Mem.nextblock m <= Mem.nextblock m2)%positive. intro H7.
cut (b < Mem.nextblock m)%positive. intro H8.
xomega.
apply H4; auto.
apply corestep_fwd in H3.
solve[apply forward_nextblock in H3; auto].
eapply private_step in H3; eauto.
destruct H3.
elimtype False; auto.
solve[destruct H; auto].
assert (Mem.nextblock m <= Mem.nextblock m2)%positive. 
 apply corestep_fwd in H3.
 solve[apply forward_nextblock in H3; auto].
solve[eapply private_valid_inv_fwd; eauto].
intros H6.
apply IHn 
 with (stack := mkFrame j (plt_ok id j LOOKUP) c' :: mkFrame i pf_i c :: stack0)
      (pf1 := length_cons (mkFrame j (plt_ok id j LOOKUP) c')
                  (mkFrame i pf_i c :: stack0))
      (pf2 := ext_pf')
      (m := m2); auto.
simpl.
split.
intros b' H7.
elimtype False.
solve[eapply private_initial in H5; eauto].
split.
intros b' H7.
simpl in H6.
destruct H6 as [H6 H8].
solve[apply H6; auto].
solve[destruct H6 as [H6 H8]; auto].
intros H6.
apply IHn 
 with (stack := mkFrame i pf_i c'' :: stack0)
      (pf1 := length_cons (mkFrame i pf_i c'') stack0)
      (pf2 := ext_pf')
      (m := m2); auto.
simpl.
split.
intros b H7.
simpl in pf2.
unfold all_at_external in pf2.
inv pf2.
(*destruct H4 as [ef [sig [args ATEXT]]].*)
eapply private_external in H3; eauto.
simpl in H6.
destruct H6 as [_ [H6 H8]].
apply H6; auto.
solve[destruct H6 as [? [? ?]]; auto].
Qed.

Lemma private_disjoint_inv'_eq: 
  forall i (pf: i < num_modules) c c' stack, 
  (forall b, private_block (get_module_csem (modules pf)) c' b ->
             private_block (get_module_csem (modules pf)) c b) -> 
  private_disjoint_inv' pf c stack -> 
  private_disjoint_inv' pf c' stack.
Proof.
intros until stack.
intros H1 H2.
simpl.
induction stack; auto.
simpl.
destruct a.
split; auto.
intros b H3.
intros CONTRA.
apply H1 in H3.
simpl in H2.
destruct H2 as [H2 H4].
solve[apply (H2 b); auto].
apply IHstack.
solve[simpl in H2; destruct H2; auto].
Qed.

Lemma private_disjoint_inv_eq: 
  forall i (pf: i < num_modules) c c' stack, 
  (forall b, private_block (get_module_csem (modules pf)) c' b ->
             private_block (get_module_csem (modules pf)) c b) -> 
  private_disjoint_inv (mkFrame i pf c :: stack) -> 
  private_disjoint_inv (mkFrame i pf c' :: stack).
Proof.
intros until stack.
intros H1 H2.
simpl.
simpl in H2; destruct H2.
split; auto.
induction stack; auto.
simpl.
destruct a.
simpl in H; destruct H.
split; auto.
eapply IHstack; eauto.
destruct H0; auto.
Qed.

Lemma private_disjoint_step: forall i (pf_i: i < num_modules) c m c' m' stack,
  corestep (get_module_csem (modules pf_i)) (get_module_genv (modules pf_i)) c m c' m' ->
  private_valid_inv m (mkFrame i pf_i c :: stack) -> 
  private_disjoint_inv' pf_i c stack -> 
  private_disjoint_inv' pf_i c' stack.
Proof.
intros.
induction stack; auto.
destruct a.
simpl.
split; auto.
intros b H2.
simpl in H1.
destruct H1 as [H1 H3].
destruct (private_dec (get_module_csem (modules pf_i)) c b).
apply H1; auto.
intros CONTRA.
eapply private_step in H; eauto.
destruct H; eauto.
destruct H as [H2' H4].
assert (b < Mem.nextblock m)%positive.
 clear - H0 CONTRA.
 solve[destruct H0 as [H0 [H1 H2]]; auto].
clear - H2' H4 H.
xomega.
simpl in *.
destruct H0 as [? [? ?]].
destruct H1 as [? ?].
solve[apply IHstack; auto].
Qed.

Lemma private_disjoint_invariant: 
  forall stack stack' m m' n pf1 pf2 pf1' pf2',
  corestepN rg_linker_core_semantics ge n 
   (mkLinkerCoreState stack pf1 pf2) m (mkLinkerCoreState stack' pf1' pf2') m' -> 
  private_valid_inv m stack -> 
  private_disjoint_inv stack -> 
  private_disjoint_inv stack'.
Proof.
intros.
revert stack pf1 pf2 m H H0 H1.
induction n; intros.
simpl in H.
solve[inv H; auto].
simpl in H.
destruct H as [c2 [m2 [STEP STEPN]]].
inv STEP.
apply IHn 
 with (stack := mkFrame i pf_i c' :: stack0) (pf1 := pf) (pf2 := ext_pf) (m := m2); auto.
eapply private_valid_invariant with (n := S O); eauto.
simpl.
exists (mkLinkerCoreState (mkFrame i pf_i c' :: stack0) pf ext_pf).
exists m2.
split; eauto.
solve[constructor; eauto].
simpl.
simpl in H1.
destruct H1 as [H1 H6].
split; auto.
solve[eapply private_disjoint_step; eauto].
apply IHn 
 with (stack := mkFrame j (plt_ok id j LOOKUP) c' :: mkFrame i pf_i c :: stack0)
      (pf1 := length_cons (mkFrame j (plt_ok id j LOOKUP) c')
                  (mkFrame i pf_i c :: stack0))
      (pf2 := ext_pf')
      (m := m2); auto.
simpl.
split; auto.
intros b' H8.
destruct (private_dec (get_module_csem (modules pf_i)) c b').
simpl in H0.
destruct H0 as [H0 H9].
solve[apply H0; auto].
elimtype False.
solve[eapply private_initial in H7; eauto].
simpl.
split; auto.
split; auto.
intros b' H8 CONTRA.
solve[eapply private_initial in H7; eauto].
clear - H7.
induction stack0; simpl; auto.
destruct a.
split; auto.
intros b' H1 CONTRA.
solve[eapply private_initial in H7; eauto].
apply IHn 
 with (stack := mkFrame i pf_i c'' :: stack0)
      (pf1 := length_cons (mkFrame i pf_i c'') stack0)
      (pf2 := ext_pf')
      (m := m2); auto.
simpl.
split.
intros b H7.
simpl in pf2.
unfold all_at_external in pf2.
inv pf2.
(*destruct H6 as [ef [sig [args ATEXT]]].*)
clear H6.
clear H8.
eapply private_external in H5; eauto.
simpl in H0.
destruct H0 as [_ [H6 H8]].
solve[apply H6; auto].
solve[destruct H0 as [? [? ?]]; auto].
simpl.
simpl in H1.
destruct H1 as [? [? ?]].
split; auto.
clear - H5 H1 pf2.
unfold all_at_external in pf2.
simpl in pf2.
inv pf2.
destruct H2 as [ef [sig [args ATEXT]]].
clear H3.
induction stack0; auto.
simpl.
destruct a.
simpl in H1.
destruct H1 as [H1 H2].
split; auto.
intros b H3 CONTRA.
eapply private_external in H5; eauto.
apply (H1 b); auto.
Qed.

End LinkerCoreSemantics.

Section LinkingExtension.
Variables
 (F V Z Zint Zext: Type) 
 (proj_zext: Z -> Zext) 
 (zmult: unit -> Zext -> Z)
 (proj_zmult: forall t z, proj_zext (zmult t z) = z)
 (cT fT vT: nat -> Type)
 (num_modules: nat) 
 (procedure_linkage_table: ident -> option nat)
 (plt_ok: 
   forall (id: ident) (i: nat), 
   procedure_linkage_table id = Some i -> i < num_modules)
 (modules: forall i: nat, i < num_modules -> 
   CompCertModule.Sig (fT i) (vT i) (cT i))
 (csig: ext_spec Z) (esig: ext_spec Zext)
 (entry_points: list (val*val*signature)).

Definition genv_map: nat -> Type := fun i: nat => Genv.t (fT i) (vT i).

Program Definition trivial_core_semantics: forall i: nat, 
 CoreSemantics (genv_map i) (cT i) mem (*(list (ident * globdef (fT i) (vT i)))*) :=
 fun i: nat => Build_CoreSemantics (*_*) _ _ _ 
  (*initial_mem: (fun _ _ _ => False)*)
  (fun _ _ _ => None) (fun _ => None) 
  (fun _ _ => None) (fun _ => None) (fun _ _ _ _ _ => False) _ _ _ _.

Program Definition trivial_coop_core_semantics: forall i: nat,
 CoopCoreSem (genv_map i) (cT i) (*(list (ident * globdef (fT i) (vT i)))*) :=
 fun i: nat => Build_CoopCoreSem (*_*) _ _ (trivial_core_semantics i) _ _ (*_*).
Next Obligation.
elimtype False; auto.
Qed.
Next Obligation.
elimtype False; auto.
Qed.
(*initial_mem:
Next Obligation.
elimtype False; auto.
Qed.*)

Program Definition trivial_rg_semantics: forall i: nat,
 RelyGuaranteeSemantics (genv_map i) (cT i) (*(list (ident * globdef (fT i) (vT i)))*) :=
 fun i: nat => Build_RelyGuaranteeSemantics (*_*) _ _ (trivial_coop_core_semantics i)
   (fun c b => False) _ _ _ _.
Next Obligation. right; auto. Qed.

Definition csem_map: forall i: nat, 
 RelyGuaranteeSemantics (genv_map i) (cT i) (*(list (ident * globdef (fT i) (vT i)))*) :=
 fun i: nat => match lt_dec i num_modules with
               | left pf => get_module_csem (modules pf)
               | right _ => trivial_rg_semantics i
               end.

Definition linker_proj_core (i: nat) (s: linker_corestate cT _ _ modules): option (cT i) :=
  match s with
  | mkLinkerCoreState nil _ _ => None
  | mkLinkerCoreState (mkFrame j pf_j c :: call_stack) _ _ =>
     match eq_nat_dec i j with 
     | left pf => Some (eq_rect j (fun x => cT x) c i (sym_eq pf))
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
 @Genv.mkgenv _ _ (PTree.empty block) (PTree.empty _) (PTree.empty _) 1%positive
 _ _ _ _ _.
Next Obligation. solve[rewrite PTree.gempty in H; congruence]. Qed.
Next Obligation. solve[rewrite PTree.gempty in H; congruence]. Qed.
Next Obligation. solve[rewrite PTree.gempty in H; congruence]. Qed.
Next Obligation. solve[rewrite PTree.gempty in H; congruence]. Qed.
Next Obligation. solve[rewrite PTree.gempty in H; congruence]. Qed.

Definition genvs: forall i: nat, Genv.t (fT i) (vT i) :=
 fun i: nat => match lt_dec i num_modules with
               | left pf => get_module_genv (modules pf)
               | right _ => trivial_genv i
               end.

Definition init_data := fun i: nat => list (ident * globdef (fT i) (vT i)).

Implicit Arguments linker_corestate [fT vT].

Lemma dependent_types_nonsense: forall i (c: cT i) (e: i=i), 
 eq_rect i (fun x => cT x) c i (eq_sym e) = c.
Proof.
intros; rewrite <-Eqdep_dec.eq_rect_eq_dec; auto.
apply eq_nat_dec.
Qed.

Variable linkable_csig_esig: linkable proj_zext
  (fun (ef: AST.external_function) => forall s c sig args,
    linker_proj_core (linker_active s) s = Some c ->
    at_external (csem_map (linker_active s)) c = Some (ef, sig, args) ->
    linker_at_external _ _ procedure_linkage_table _ s = None)
  csig esig.

Lemma handled_lem: 
 forall s c ef sig args,
 linker_proj_core (linker_active s) s = Some c ->
 at_external (csem_map (linker_active s)) c = Some (ef, sig, args) ->
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
inversion H; subst c; clear H.
unfold genv_map in *; rewrite H0 in H1.
destruct ef; try solve[congruence].
exists name.
destruct (procedure_linkage_table name); try solve[congruence].
solve[eexists; split; eauto].
Qed.

Lemma handled_invar: 
 forall s c s' c' ef sig args sig' args',
 linker_proj_core (linker_active s) s = Some c ->
 at_external (csem_map (linker_active s)) c = Some (ef, sig, args) ->
 linker_at_external _ _ procedure_linkage_table _ s = None -> 
 linker_proj_core (linker_active s') s' = Some c' ->
 at_external (csem_map (linker_active s')) c' = Some (ef, sig', args') ->
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
inversion H2; subst c'; clear H2.
unfold genv_map in *; rewrite H3.
assert (exists id, exists sig, 
 ef = EF_external id sig /\
 exists b, procedure_linkage_table id = Some b) as [id [sig'' [-> [b ->]]]].
 solve[eapply handled_lem; eauto].
auto.
Qed. 

Program Definition linking_extension: 
 @Extension.Sig _ _ _ _ (Genv.t F V) (*(list (ident * globdef F V)) *)
     (linker_corestate num_modules cT modules) 
     (rg_linker_core_semantics F V cT fT vT procedure_linkage_table 
              plt_ok modules entry_points)
     esig _ (*_*) cT csem_map csig :=
 Extension.Make 
  (linker_core_semantics F V cT fT vT procedure_linkage_table plt_ok modules entry_points)
  esig _ (*_*) csem_map csig 
  (const num_modules)
  linker_proj_core _  
  linker_active _ 
  (fun _ => tt) proj_zext zmult
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
exists c; f_equal.
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
 (mkLinkerCoreState (mkFrame i PF c2 :: stack) stack_nonempty callers_at_external)
 c2 m2 c' m'
).
simpl in IHn; spec IHn.
destruct (eq_nat_dec i i); try solve[elimtype False; omega].
solve[rewrite dependent_types_nonsense; auto].
destruct IHn as [s' [STEP23' [_ PROJ]]]; auto.
destruct (eq_nat_dec i i); try solve[elimtype False; omega].
rewrite dependent_types_nonsense in H1.
inversion H1; rewrite H0 in *; clear H0 H1.
exists s'; split; auto.
exists (mkLinkerCoreState (mkFrame i PF c2 :: stack) stack_nonempty callers_at_external).
exists m2.
split; auto.
constructor; auto.
unfold csem_map, genvs in STEP12.
destruct (lt_dec i num_modules); try solve[elimtype False; omega].
solve[assert (PF=l) as -> by apply proof_irr; auto].
Qed.

Lemma linker_private_conserving: 
 private_conserving 
  (rg_linker_core_semantics F V cT fT vT procedure_linkage_table plt_ok modules entry_points) 
   csem_map linking_extension.
Proof.
unfold private_conserving.
intros s i c PROJ b PRIVB.
destruct s.
simpl in PROJ.
destruct stack.
congruence.
destruct f.
destruct (eq_nat_dec i i0); try solve[elimtype False; omega].
subst.
rewrite <-Eqdep_dec.eq_rect_eq_dec in PROJ.
inv PROJ.
simpl.
left.
unfold csem_map in PRIVB.
destruct (lt_dec i0 num_modules); try solve[elimtype False; omega].
assert (PF = l) as -> by apply proof_irr.
auto.
solve[apply eq_nat_dec].
congruence.
Qed.

Lemma linker_step_lem: 
 forall i ge c2 m2 c2' m2' s2' pf_i stack pf1 pf2
 (csem_fun: forall i: nat, corestep_fun (csem_map i)),
 corestep (csem_map i) (genvs i) c2 m2 c2' m2' -> 
 corestep (linker_core_semantics F V cT fT vT procedure_linkage_table
             plt_ok modules entry_points) ge  
           (mkLinkerCoreState (mkFrame i pf_i c2::stack) pf1 pf2) m2 s2' m2' ->
  s2' = mkLinkerCoreState (mkFrame i pf_i c2'::stack) pf1 pf2.
Proof.
intros until pf2; intros csem_fun; intros STEP12 STEP12'; simpl in *.
inv STEP12'.
assert (pf_i1 = pf_i) as -> by apply proof_irr.
assert (c' = c2').
 generalize (@csem_fun i).
 unfold corestep_fun, csem_map, genvs in *.
 destruct (lt_dec i num_modules); try solve[elimtype False; omega].
 apply Eqdep_dec.inj_pair2_eq_dec in H0; [|solve[apply eq_nat_dec]]; subst c2.
 assert (l = pf_i1) by apply proof_irr.
 subst.
 intros H10. 
 specialize (H10 _ _ _ _ _ _ _ H8 STEP12).
 solve[inv H10; auto].
assert (pf0 = pf1) as -> by apply proof_irr; auto.
assert (ext_pf0 = pf2) as -> by apply proof_irr; auto.
solve[subst; auto].
apply corestep_not_at_external in STEP12.
unfold csem_map in STEP12.
destruct (lt_dec i num_modules); try solve[elimtype False; omega].
assert (l = pf_i1) by apply proof_irr.
subst.
apply Eqdep_dec.inj_pair2_eq_dec in H0.
subst.
clear - AT_EXT STEP12.
solve[unfold genv_map in *; congruence].
solve[apply eq_nat_dec].
apply corestep_not_halted in STEP12.
unfold csem_map in STEP12.
destruct (lt_dec i num_modules); try solve[elimtype False; omega].
assert (l = pfj0) by apply proof_irr.
subst.
apply Eqdep_dec.inj_pair2_eq_dec in H0.
subst.
clear - HALTED STEP12.
solve[unfold genv_map in *; congruence].
solve[apply eq_nat_dec].
Qed.

Lemma linker_core_compatible: forall (ge: Genv.t F V) 
   (agree: forall (k : nat) (pf_k : k < num_modules),
   genvs_agree ge (get_module_genv (modules pf_k)))
   (domain_eq: forall (k : nat) (pf_k : k < num_modules),
     genvs_domain_eq ge (get_module_genv (modules pf_k)))
   (csem_fun: forall i: nat, corestep_fun (csem_map i)),
 @core_compatible _ _ _ _ (Genv.t F V) (*(list (ident*globdef F V)) *)
        (linker_corestate num_modules cT modules) 
        (linker_core_semantics F V cT fT vT procedure_linkage_table plt_ok modules entry_points) 
        esig (fun i => Genv.t (fT i) (vT i)) (*init_data*) cT
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
solve[rewrite dependent_types_nonsense; auto].
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
destruct (@at_external (Genv.t (fT j) (vT j)) (cT j) Mem.mem
             (*(list (prod ident (globdef (fT j) (vT j)))) *)
             (csem_map j) c).
congruence.
unfold csem_map in H1.
(*generalize LOOKUP as LOOKUP'; intro.
apply plt_ok in LOOKUP'.*)
destruct (lt_dec j num_modules); try solve[elimtype False; omega].
assert (H2: l = pfj) by apply proof_irr.
rewrite H2 in H1.
unfold genv_map in *.
rewrite HALTED in H1.
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
(*generalize LOOKUP as LOOKUP'; intro.
apply plt_ok in LOOKUP'.*)
destruct (lt_dec j num_modules); try solve[elimtype False; omega].
apply corestep_not_halted in H2.
assert (H3: l = pfj) by apply proof_irr.
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
exists (mkLinkerCoreState (mkFrame i PF c' :: stack) stack_nonempty callers_at_external).
constructor; auto.
unfold csem_map, genvs in H2.
destruct (lt_dec i num_modules); try solve[elimtype False; omega].
assert (H3: l = PF) by apply proof_irr.
rewrite H3 in H2.
solve[apply H2].

intros until m'; intros H1 H2 H3 H4 j H5.
inv H4; simpl in *.
destruct (eq_nat_dec i i); try solve[elimtype False; omega|auto].
destruct (eq_nat_dec j i); try solve[elimtype False; omega|auto].
subst; destruct (eq_nat_dec j j0); try solve[elimtype False; omega].
subst; destruct (eq_nat_dec j i); try solve[elimtype False; omega].
solve[auto].

intros until n; intros H1 H2 H3 j H4.
simpl in *.
clear - H1 H2 H3 H4 csem_fun.
revert s m c c' H1 H2 H3 H4.
induction n.
solve[intros; simpl in H3; inv H3; auto].
simpl; intros s m c c' H1 H2 H3 H4.
destruct H2 as [c2 [m2 [STEP STEPN]]].
destruct H3 as [s2 [m2' [STEP' STEPN']]].
cut (linker_proj_core j s = linker_proj_core j s2).
intro H5.
rewrite H5.
assert (Heq: linker_active s = linker_active s2).
 inv STEP'.
 simpl; auto.
 simpl in *.
 destruct (eq_nat_dec i i); try solve[elimtype False; omega].
 rewrite <-Eqdep_dec.eq_rect_eq_dec in H1.
 inv H1.
 apply corestep_not_at_external in STEP.
 unfold csem_map in STEP.
 destruct (lt_dec i num_modules); try solve[elimtype False; omega].
 assert (l = pf_i) by apply proof_irr.
 subst l.
 unfold genv_map, init_data in STEP, AT_EXT.
 rewrite STEP in AT_EXT.
 congruence.
 solve[apply eq_nat_dec].
 simpl in *.
 destruct (eq_nat_dec j0 j0); try solve[elimtype False; omega].
 rewrite <-Eqdep_dec.eq_rect_eq_dec in H1.
 inv H1.
 apply corestep_not_halted in STEP.
 unfold csem_map in STEP.
(* generalize (plt_ok LOOKUP); intro.*)
 destruct (lt_dec j0 num_modules); try solve[elimtype False; omega].
 assert (l = pfj) by apply proof_irr.
 subst l.
 unfold genv_map, init_data in *.
 rewrite HALTED in STEP.
 congruence.
 solve[apply eq_nat_dec].
specialize (IHn s2 m2').
rewrite <-Heq in IHn.
apply (IHn c2 c'); auto.
clear - H1 STEP STEP' csem_fun.
inv STEP'; simpl in *.
destruct (eq_nat_dec i i); try solve[elimtype False; omega].
rewrite <-Eqdep_dec.eq_rect_eq_dec in H1|-*.
inv H1.
generalize (csem_fun i); intros H3.
unfold corestep_fun in H3.
unfold csem_map, genvs in *.
destruct (lt_dec i num_modules); try solve[elimtype False; omega].
assert (l = pf_i) by apply proof_irr.
subst l.
eapply H3 with (q1 := c') in STEP; eauto.
solve[inv STEP; eauto].
solve[apply eq_nat_dec].
solve[apply eq_nat_dec].
destruct (eq_nat_dec i i); try solve[elimtype False; omega].
rewrite <-Eqdep_dec.eq_rect_eq_dec in H1.
inv H1.
apply corestep_not_at_external in STEP.
unfold csem_map in STEP.
destruct (lt_dec i num_modules); try solve[elimtype False; omega].
assert (l = pf_i) by apply proof_irr.
subst l.
unfold genv_map, init_data in *.
rewrite STEP in AT_EXT.
congruence.
solve[apply eq_nat_dec].
destruct (eq_nat_dec j j); try solve[elimtype False; omega].
rewrite <-Eqdep_dec.eq_rect_eq_dec in H1.
inv H1.
apply corestep_not_halted in STEP.
unfold csem_map in STEP.
(*generalize (plt_ok LOOKUP); intro.*)
destruct (lt_dec j num_modules); try solve[elimtype False; omega].
unfold genv_map, init_data in *.
assert (l = pfj) by apply proof_irr.
subst l.
rewrite STEP in HALTED.
congruence.
solve[apply eq_nat_dec].
assert (m2 = m2').
 generalize (csem_fun (linker_active s)).
 intro Hfun.
 unfold corestep_fun in Hfun.
 clear - H1 STEP STEP' H5 Hfun.
 inv STEP'; simpl in *.
 eapply Hfun with (q1 := c') (m1 := m2') in STEP; eauto.
 solve[inv STEP; auto].
 unfold csem_map, genvs in *.
 destruct (lt_dec i num_modules); try solve[elimtype False; omega].
 assert (l = pf_i) as -> by apply proof_irr.
 destruct (eq_nat_dec i i); try solve[elimtype False; omega].
 rewrite <-Eqdep_dec.eq_rect_eq_dec in H1. 
 inv H1.
 solve[auto].
 solve[apply eq_nat_dec].
 destruct (eq_nat_dec i i); try solve[elimtype False; omega].
 rewrite <-Eqdep_dec.eq_rect_eq_dec in H1. 
 inv H1.
 apply corestep_not_at_external in STEP.
 unfold csem_map in STEP.
 destruct (lt_dec i num_modules); try solve[elimtype False; omega].
 assert (l = pf_i) as -> by apply proof_irr.
 subst l.
 unfold genv_map, init_data in *.
 rewrite AT_EXT in STEP.
 congruence.
 solve[apply eq_nat_dec].
 destruct (eq_nat_dec j0 j0); try solve[elimtype False; omega].
 rewrite <-Eqdep_dec.eq_rect_eq_dec in H1. 
 inv H1.
 apply corestep_not_halted in STEP.
 unfold csem_map in STEP.
 destruct (lt_dec j0 num_modules); try solve[elimtype False; omega].
 unfold genv_map, init_data in *.
 assert (l = pfj) as -> by apply proof_irr.
 subst l.
 rewrite HALTED in STEP.
 congruence.
 solve[apply eq_nat_dec]. 
subst m2.
unfold genv_map, init_data in *.
solve[apply STEPN].
clear - H1 H4 STEP STEP'.
inv STEP'; simpl in *.
destruct (eq_nat_dec j i).
solve[elimtype False; auto].
solve[auto].
apply corestep_not_at_external in STEP.
unfold csem_map in STEP.
destruct (lt_dec i num_modules); try solve[elimtype False; omega].
assert (l = pf_i) by apply proof_irr.
subst l.
unfold genv_map, init_data in *.
destruct (eq_nat_dec i i); try solve[elimtype False; omega].
rewrite <-Eqdep_dec.eq_rect_eq_dec in H1.
inv H1.
rewrite STEP in AT_EXT.
congruence.
solve[apply eq_nat_dec].
destruct (eq_nat_dec j0 j0); try solve[elimtype False; omega].
rewrite <-Eqdep_dec.eq_rect_eq_dec in H1.
inv H1.
apply corestep_not_halted in STEP.
unfold csem_map in STEP.
destruct (lt_dec j0 num_modules); try solve[elimtype False; omega].
assert (l = pfj) by apply proof_irr.
subst l.
unfold genv_map, init_data in *.
rewrite HALTED in STEP.
congruence.
solve[apply eq_nat_dec].

intros until retv; intros H1 H2 H3.
destruct s; destruct s'; simpl in H3.
destruct stack; try solve[inv H3].
destruct f.
unfold csem_map in H2; simpl in H2.
destruct (lt_dec i num_modules); try solve[elimtype False; congruence].
assert (H4: l = PF) by apply proof_irr; auto.
rewrite H4 in H2.
unfold init_data in *.
assert (H: c0 = c).
 simpl in H1.
 destruct (eq_nat_dec i i); try solve[elimtype False; omega].
 rewrite dependent_types_nonsense in H1.
 solve[inversion H1; auto].
rewrite H in *.
unfold genv_map in *.
rewrite H2 in H3.
inversion H3.
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
destruct (after_external (get_module_csem (modules PF)) retv c).
inv H1.
destruct (eq_nat_dec j i); try solve[elimtype False; omega].
auto.
congruence.

intros until args; intros H1.
destruct s; simpl in *|-.
destruct stack; try solve[congruence].
destruct f.
exists c; simpl.
destruct (eq_nat_dec i i); try solve[elimtype False; omega].
split.
rewrite dependent_types_nonsense; auto.
unfold csem_map.
destruct (lt_dec i num_modules); try solve[elimtype False; omega].
assert (l = PF) as -> by apply proof_irr; auto.
unfold init_data, genv_map.
destruct (at_external (get_module_csem (modules PF)) c).
destruct p as [[ef' sig'] args'].
destruct ef'; auto.
destruct (procedure_linkage_table name); try solve[congruence].
congruence.
Qed.

End LinkingExtension.

Section LinkerCompilable.
Variables 
 (Z Zext F_S F_T V_S V_T: Type) 
 (proj_zext: Z -> Zext)
 (zmult: unit -> Zext -> Z)
 (proj_zmult: forall t z, proj_zext (zmult t z) = z)
 (geS: Genv.t F_S V_S) (geT: Genv.t F_T V_T) 
 (num_modules: nat)
 (cS cT fS fT vS vT: nat -> Type)
 (procedure_linkage_table: ident -> option nat)
 (plt_ok: 
   forall (id: ident) (i: nat), 
   procedure_linkage_table id = Some i -> i < num_modules)
 (modules_S: forall i: nat, i < num_modules -> CompCertModule.Sig (fS i) (vS i) (cS i))
 (modules_T: forall i: nat, i < num_modules -> CompCertModule.Sig (fT i) (vT i) (cT i))
 (Hspec: ext_spec Z) (Hexternal_spec: ext_spec Zext).

(** Conditions required to construct a linking extension *)

Definition handled_S := handled cS fS vS procedure_linkage_table modules_S. 
Definition handled_T := handled cT fT vT procedure_linkage_table modules_T. 

Variable linkableS_csig_esig: linkable proj_zext handled_S Hspec Hexternal_spec.
Variable linkableT_csig_esig: linkable proj_zext handled_T Hspec Hexternal_spec.

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
 core_data i ->  meminj -> cS i -> mem -> cT i -> mem -> Prop.
Variable core_ord: forall i: nat, core_data i -> core_data i -> Prop.
Variable num_modules_nonzero: (O < num_modules)%nat. (*Required by defn. of core_ords*)

Variable RGsim: forall i: nat,
 StableRelyGuaranteeSimulation.Sig (csem_map_S i) (csem_map_T i) (genv_mapS i) (@match_state i).

Variable entry_points: list (val*val*signature).

Variable core_simulations: forall i: nat,
 Forward_simulation_inject
  (*(list (ident * globdef (fS i) (vS i)))
  (list (ident * globdef (fT i) (vT i)))*)
  (csem_map_S i) 
  (csem_map_T i) (genv_mapS i) (genv_mapT i) entry_points 
  (core_data i) (@match_state i) (@core_ord i).

Implicit Arguments linker_corestate [fT vT].

Fixpoint tl_inv j m1 m2 
    (stack1: call_stack cS num_modules) (stack2: call_stack cT num_modules) := 
 match stack1, stack2 with
 | nil, nil => True
 | mkFrame i pf_i c_i :: stack1', mkFrame k pf_k c_k :: stack2' => 
   (exists pf: k=i, exists cd0, exists j0, exists m10, exists m20,
     @match_state i cd0 j0 c_i m10 (eq_rect k (fun x => cT x) c_k i pf) m20 /\
     Mem.inject j0 m10 m20 /\
     inject_incr j0 j /\
     inject_separated j0 j m10 m20 /\
     mem_forward m10 m1 /\
     Mem.unchanged_on (fun b ofs => 
       loc_unmapped j0 b ofs /\ 
       private_block (get_module_csem (modules_S pf_i)) c_i b) m10 m1 /\
     mem_forward m20 m2 /\
     Mem.unchanged_on (fun b ofs => 
       loc_out_of_reach j0 m10 b ofs /\ 
       private_block (get_module_csem (modules_T pf_k)) c_k b) m20 m2) /\
   tl_inv j m1 m2 stack1' stack2'
 | _, _ => False
 end.

Definition stack_inv j m1 m2 
    (stack1: call_stack cS num_modules) (stack2: call_stack cT num_modules) := 
 match stack1, stack2 with
 | nil, nil => True
 | mkFrame i pf_i c_i :: stack1', mkFrame k pf_k c_k :: stack2' => 
   exists pf: k=i,
   (exists cd, @match_state i cd j c_i m1 (eq_rect k (fun x => cT x) c_k i pf) m2) /\
   tl_inv j m1 m2 stack1' stack2'
 | _, _ => False
 end.

Lemma tl_inv_length_eq: 
 forall j m1 m2 stack1 stack2,
 tl_inv j m1 m2 stack1 stack2 -> length stack1=length stack2.
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
destruct H as [H H2].
solve[destruct H as [? [? [? H]]]; auto].
Qed.

Lemma stack_inv_length_eq: 
 forall j m1 m2 stack1 stack2,
 stack_inv j m1 m2 stack1 stack2 -> length stack1=length stack2.
Proof.
intros until stack2.
destruct stack1; destruct stack2; simpl; auto.
solve[intros; elimtype False; auto].
intros stack2.
destruct f.
solve[intros; elimtype False; auto].
destruct f.
intros.
destruct f0.
destruct H as [? [? H]].
solve[f_equal; eapply tl_inv_length_eq; eauto].
Qed.

Definition R_inv (j:meminj) (x:linker_corestate num_modules cS modules_S) (m1:mem) 
                            (y:linker_corestate num_modules cT modules_T) (m2:mem) := 
 match x, y with
 | mkLinkerCoreState stack1 _ _, mkLinkerCoreState stack2 _ _ => 
    private_valid_inv fS vS modules_S m1 stack1 /\
    private_disjoint_inv fS vS modules_S stack1 /\
    private_valid_inv fT vT modules_T m2 stack2 /\
    private_disjoint_inv fT vT modules_T stack2 /\
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
 corestep (csem_map_S i) (genv_mapS i)  c2 m2 c2' m2' -> 
 corestep (linker_core_semantics F_S V_S cS fS vS procedure_linkage_table
             plt_ok modules_S entry_points) geS  
           (mkLinkerCoreState (mkFrame i pf_i c2::stack) pf1 pf2) m2 s2' m2' ->
  s2' = mkLinkerCoreState (mkFrame i pf_i c2'::stack) pf1 pf2.
Proof.
intros until pf2; intros STEP12 STEP12'; simpl in *.
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
assert (l = pfj0) by apply proof_irr.
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
simpl in *.
destruct H1 as [c3 [m3 [STEP12 STEP23]]].
destruct H2 as [s3 [m3' [STEP12' STEP23']]].
specialize (IHn c3 m3 pf1 pf2 STEP23).
inv STEP12'.
assert (c' = c3).
 generalize (@csem_fun_T i).
 unfold corestep_fun, csem_map_T, csem_map, genv_mapT, genvs in *.
 destruct (lt_dec i num_modules); try solve[elimtype False; omega].
 apply Eqdep_dec.inj_pair2_eq_dec in H0; [|solve[apply eq_nat_dec]]; subst c2.
 assert (l = pf_i1) by apply proof_irr.
 subst.
 intros H10; specialize (H10 _ _ _ _ _ _ _ H8 STEP12).
 solve[inv H10; auto].
assert (m3' = m3). 
 generalize (@csem_fun_T i).
 unfold corestep_fun, csem_map_T, csem_map, genv_mapT, genvs in *.
 destruct (lt_dec i num_modules); try solve[elimtype False; omega].
 apply Eqdep_dec.inj_pair2_eq_dec in H0; [|solve[apply eq_nat_dec]]; subst c2.
 assert (l = pf_i1) by apply proof_irr.
 subst.
 intros H10; specialize (H10 _ _ _ _ _ _ _ H8 STEP12).
 solve[inv H10; auto].
subst.
spec IHn; eauto.
assert (pf1 = pf0) as -> by apply proof_irr.
assert (pf2 = ext_pf0) as -> by apply proof_irr.
assert (pf_i = pf_i1) as -> by apply proof_irr.
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
assert (l = pfj0) by apply proof_irr.
subst.
apply Eqdep_dec.inj_pair2_eq_dec in H0.
subst.
clear - HALTED STEP12.
solve[unfold genv_map in *; congruence].
solve[apply eq_nat_dec].
Qed.

(*TODO: move to more general setting*)
Lemma loc_unmapped_sub: 
  forall j j' b ofs,
  inject_incr j j' -> 
  loc_unmapped j' b ofs -> 
  loc_unmapped j b ofs.
Proof.
intros.
unfold inject_incr in H.
unfold loc_unmapped in *.
case_eq (j b).
intros [b0 ofs0] Heq.
solve[erewrite H in H0; eauto].
solve[auto].
Qed.

Lemma loc_outofreach_sub: 
  forall j j' b ofs m,
  inject_incr j j' -> 
  loc_out_of_reach j' m b ofs -> 
  loc_out_of_reach j m b ofs.
Proof.
intros.
unfold inject_incr in H.
unfold loc_out_of_reach in *.
intros.
specialize (H b0 b delta H1).
solve[specialize (H0 _ _ H); auto].
Qed.

Lemma private_disjoint_inv'_initialS: 
  forall stack k c pf,
  (forall b, ~private_block (csem_map_S k) c b) -> 
  private_disjoint_inv' fS vS modules_S pf c stack.
Proof.
intros.
induction stack.
simpl; auto.
simpl.
destruct a.
split; auto.
intros b H1 CONTRA.
apply (H b).
unfold csem_map_S, csem_map.
destruct (lt_dec k num_modules).
assert (l = pf) as -> by apply proof_irr.
auto.
elimtype False; auto.
Qed.

Lemma private_disjoint_inv'_initialT: 
  forall stack k c pf,
  (forall b, ~private_block (csem_map_T k) c b) -> 
  private_disjoint_inv' fT vT modules_T pf c stack.
Proof.
intros.
induction stack.
simpl; auto.
simpl.
destruct a.
split; auto.
intros b H1 CONTRA.
apply (H b).
unfold csem_map_T, csem_map.
destruct (lt_dec k num_modules).
assert (l = pf) as -> by apply proof_irr.
auto.
elimtype False; auto.
Qed.
(*END move*)

Lemma linking_extension_compilable 
  (cd_init: CompilabilityInvariant.core_datas core_data):
 CompilableExtension.Sig 
 (@rg_linker_core_semantics F_S V_S num_modules cS fS vS 
   procedure_linkage_table plt_ok modules_S entry_points)
 (@rg_linker_core_semantics F_T V_T num_modules cT fT vT 
   procedure_linkage_table plt_ok modules_T entry_points)
 geS geT entry_points.
Proof.
set (R := R_inv).
destruct (@ExtensionCompilability 
 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
 (@rg_linker_core_semantics F_S V_S num_modules cS fS vS 
   procedure_linkage_table plt_ok modules_S entry_points)
 (@rg_linker_core_semantics F_T V_T num_modules cT fT vT 
   procedure_linkage_table plt_ok modules_T entry_points)
 csem_map_S csem_map_T Hspec Hexternal_spec
 geS geT genv_mapS genv_mapT 
 (@linking_extension F_S V_S Z Zext proj_zext zmult proj_zmult cS fS vS 
   num_modules procedure_linkage_table plt_ok modules_S Hspec Hexternal_spec 
   entry_points linkableS_csig_esig)
 (@linking_extension F_T V_T Z Zext proj_zext zmult proj_zmult cT fT vT 
   num_modules procedure_linkage_table plt_ok modules_T Hspec Hexternal_spec 
   entry_points linkableT_csig_esig)
 entry_points core_data match_state core_ord num_modules R)
 as [LEM].
apply LEM; auto.
unfold genv_mapS.
apply (@linker_core_compatible F_S V_S Z Zext proj_zext zmult proj_zmult cS fS vS
  num_modules procedure_linkage_table plt_ok 
  modules_S Hspec Hexternal_spec entry_points linkableS_csig_esig); auto.
 clear - domain_eq_S.
 unfold genv_mapS, genvs in domain_eq_S.
 intros k pf_k.
 specialize (domain_eq_S k).
 destruct (lt_dec k num_modules); try solve[elimtype False; omega].
 solve[assert (pf_k = l) as -> by apply proof_irr; auto]. 
apply (@linker_core_compatible F_T V_T Z Zext proj_zext zmult proj_zmult cT fT vT
  num_modules procedure_linkage_table plt_ok 
  modules_T Hspec Hexternal_spec entry_points linkableT_csig_esig); auto.
 clear - domain_eq_T.
 unfold genv_mapT, genvs in domain_eq_T.
 intros k pf_k.
 specialize (domain_eq_T k).
 destruct (lt_dec k num_modules); try solve[elimtype False; omega].
 solve[assert (pf_k = l) as -> by apply proof_irr; auto].
solve[apply linker_private_conserving].
solve[apply linker_private_conserving].
intros; simpl.
destruct x; simpl.
destruct stack.
simpl in stack_nonempty; omega.
solve[destruct f; auto].
intros; simpl.
destruct x; simpl.
destruct stack.
simpl in stack_nonempty; omega.
solve[destruct f; auto].
clear LEM; constructor; simpl.

(*1*)
intros until cd'; intros H1 H2. 
intros [_ [_ [_ [_ [RR [H3 H4]]]]]].
intros H5 H6 H7 H8 STEP1 STEP2 ESTEP1 ESTEP2 MATCH'.
simpl in *.
unfold R, R_inv in RR|-*.
destruct s1; destruct s2; simpl in *.
destruct RR as [PRIV1 [DISJ1 [PRIV2 [DISJ2 RR]]]].
destruct stack.
solve[congruence].
intros; destruct f.
destruct stack0; simpl in RR.
solve[elimtype False; auto].
destruct f.
subst.
destruct (eq_nat_dec i0 i0); try solve[elimtype False; omega].
rewrite <-Eqdep_dec.eq_rect_eq_dec in H1, H2;
 try solve[apply eq_nat_dec].
inv H1; inv H2.
destruct RR as [? [[cd'' MATCH] STACK]]. 
rewrite <-Eqdep_dec.eq_rect_eq_dec in MATCH;
 try solve[apply eq_nat_dec].
generalize STEP2 as STEP2'; intro.
apply linker_step_lem2 
 with (s2' := s2') (stack := stack0) (pf_i := PF0) (pf1 := stack_nonempty0)
  (pf2 := callers_at_external0) in STEP2; auto.
subst.
generalize STEP1 as STEP1'; intro.
eapply linker_step_lem1 
 with (stack := stack) (pf_i := PF) (pf1 := stack_nonempty)
  (pf2 := callers_at_external) in STEP1; eauto.
subst.
split; auto.

simpl; split; auto.
intros b H10.
eapply private_valid_invariant 
 with (stack' := mkFrame i0 PF c1' :: stack)
      (m' := m1') 
      (pf1' := stack_nonempty) 
      (pf2' := callers_at_external) 
      (procedure_linkage_table := procedure_linkage_table) 
      (plt_ok := plt_ok) 
      (n := S O)
      in PRIV1; auto.
simpl in PRIV1.
destruct PRIV1 as [X Y].
apply (X b); auto.
exists (mkLinkerCoreState (mkFrame i0 PF c1' :: stack) 
           stack_nonempty callers_at_external).
exists m1'.
solve[simpl; split; eauto].
simpl in PRIV1.
destruct PRIV1 as [X Y].
apply private_valid_inv_fwd with (m := m1); auto.
apply corestep_fwd in STEP1'.
solve[apply forward_nextblock; auto].
split.
eapply private_disjoint_invariant
 with (n := S O).
simpl.
exists (mkLinkerCoreState (mkFrame i0 PF c1' :: stack) 
           stack_nonempty callers_at_external).
exists m1'.
solve[split; eauto].
solve[auto].
solve[auto].

split.
simpl; split. 
intros b H10.
eapply private_valid_invariant 
 with (stack' := mkFrame i0 PF0 c2' :: stack0)
      (m' := m2') 
      (pf1' := stack_nonempty0) 
      (pf2' := callers_at_external0) 
      (procedure_linkage_table := procedure_linkage_table) 
      (plt_ok := plt_ok) 
      (n := n)
      in PRIV2; auto.
simpl in PRIV2.
destruct PRIV2 as [X Y].
apply (X b); auto.
simpl.
solve[eauto].
simpl in PRIV2.
destruct PRIV2 as [X Y].
apply private_valid_inv_fwd with (m := m2); auto.
apply corestepN_fwd in STEP2'.
solve[apply forward_nextblock in STEP2'; auto].
split.
eapply private_disjoint_invariant
 with (n := n).
simpl.
solve[eauto].
solve[auto].
solve[auto].

exists (@refl_equal _ i0).
split.
solve[exists cd'; auto].

(*tl_inv PROOF*)
apply corestep_fwd in STEP1'.
apply corestepN_fwd in STEP2'.
clear - H5 H6 H7 H8 PF MATCH' MATCH STACK RGsim H H0 DISJ1 DISJ2 STEP1' STEP2'.
revert stack0 STACK DISJ2; induction stack.
intros stack0; destruct stack0; simpl; auto.
intros stack0; destruct stack0; simpl; auto.
destruct a; destruct f.
intros [[PF' [cd0 [j0 [m10 [m20 [QQ1 [QQINJ [QQ2 [QQ3 [QQ4 [QQ5 [QQ6 MATCH'']]]]]]]]]]]] STACK'].
subst.
rewrite <-Eqdep_dec.eq_rect_eq_dec in QQ1; try solve[apply eq_nat_dec].
split; auto.
exists (@refl_equal _ i); exists cd0; exists j0; exists m10; exists m20.
split; auto.
split; auto.
split; auto.
solve[eapply inject_incr_trans; eauto].
split; auto.
solve[eapply inject_separated_incr_fwd2; eauto].
split; auto.
eapply mem_forward_trans; eauto.
split; auto.

eapply mem_unchanged_unmapped_trans; eauto.
apply mem_unchanged_on_sub with (Q := fun b ofs => 
  loc_unmapped j b ofs /\
  ~private_block (csem_map_S i0) c1 b); auto.
intros b ofs [? ?]; split; auto.
intros CONTRA.
clear - DISJ1 CONTRA H2.
simpl in DISJ1.
destruct DISJ1 as [[X _] _].
apply (X b); auto.
revert CONTRA.
unfold csem_map_S, csem_map.
destruct (lt_dec i0 num_modules); try solve[congruence].
solve[assert (l = PF) as -> by apply proof_irr; auto].

split; auto.
solve[eapply mem_forward_trans; eauto].

apply (@unchanged_outofreach_trans _ _ _ _ m10 m1 m20 m2 m2' j0 j); auto.
intros b ofs p H1 H2.
solve[destruct (QQ4 b H1); auto].
apply mem_unchanged_on_sub with (Q := fun b ofs => 
  loc_out_of_reach j m1 b ofs /\
  ~private_block (csem_map_T i0) c2 b); auto.
intros b ofs [? ?]; split; auto.
intros CONTRA.
clear - DISJ2 CONTRA H2.
destruct DISJ2 as [[X _] _].
apply (X b); auto.
revert CONTRA.
unfold csem_map_T, csem_map.
destruct (lt_dec i0 num_modules); try solve[congruence].
solve[assert (l = PF0) as -> by apply proof_irr; auto].

clear - DISJ1 DISJ2 IHstack STACK'.
apply IHstack; auto.
destruct DISJ1 as [[X Y] [Z W]].
solve[split; auto].
destruct DISJ2 as [[X Y] [Z W]].
solve[split; auto].
(*END tl_inv PROOF*)

(*2*)
intros until args1; intros [_ [_ [_ [_ [RR [H1 H2]]]]]]; simpl in *.
intros H3 H4 H5 H6 H7 H8 H9 AT_EXT H10 H11.
unfold R, R_inv in *.
intros HAS_TY1 HAS_TY2 INJ.
destruct s1; destruct s2; simpl in *.
destruct stack.
simpl in stack_nonempty; elimtype False; omega.
destruct f; simpl in *.
destruct stack0.
simpl in stack_nonempty0; elimtype False; omega.
destruct f; simpl in *.
subst.
case_eq (after_external (get_module_csem (modules_S PF)) ret1 c).
2: solve[intros Heq; rewrite Heq in H10; congruence].
intros c1 Heq1.
rewrite Heq1 in H10.
inv H10.
case_eq (after_external (get_module_csem (modules_T PF0)) ret2 c0).
2: solve[intros Heq; rewrite Heq in H11; congruence].
intros c2 Heq2.
rewrite Heq2 in H11.
inv H11.
destruct RR as [PRIV1 [DISJ1 [PRIV2 [DISJ2 [RR1 [[cd' MATCH] RR2]]]]]].

split3; auto.

assert (Hlt: (Mem.nextblock m1 <= Mem.nextblock m1')%positive).
 solve[apply forward_nextblock in H6; auto].

split; auto.
intros b H10.
assert (b < Mem.nextblock m1)%positive.
 case_eq (at_external (get_module_csem (modules_S PF)) c).
 intros [[ef' sig'] args'] ATEXT.
 eapply private_external in Heq1; eauto.
 destruct PRIV1 as [X Y].
 solve[apply (X b); eauto].
 intros ATEXT.
 rewrite ATEXT in AT_EXT.
 congruence.
xomega.
eapply private_valid_inv_fwd; eauto.
solve[destruct PRIV1; auto].
destruct DISJ1 as [X Y].
simpl; split; auto.
case_eq (at_external (get_module_csem (modules_S PF)) c).
2: intros ATEXT; rewrite ATEXT in AT_EXT; congruence.
intros [[ef' sig'] args'] ATEXT.
apply private_disjoint_inv'_eq with (c := c).
solve[intros; eapply private_external; eauto].
solve[apply X].

split; auto.
simpl; split; auto.
intros b H10.
assert (b < Mem.nextblock m2)%positive.
 case_eq (at_external (get_module_csem (modules_S PF)) c).
 2: intros ATEXT; rewrite ATEXT in AT_EXT; congruence.
 intros [[ef' sig'] args'] ATEXT.
 destruct (core_simulations i0).
 rewrite <-Eqdep_dec.eq_rect_eq_dec in MATCH.
 eapply core_at_external0 in MATCH; eauto.
 destruct MATCH as [_ [_ [vals2 [_ [_ ATEXT2]]]]].
 unfold csem_map_T, csem_map in ATEXT2.
 destruct (lt_dec i0 num_modules); try solve[elimtype False; omega].
 assert (l = PF0) by apply proof_irr.
 subst.
 eapply private_external in Heq2; eauto.
 destruct PRIV2 as [X Y].
 solve[apply (X b); eauto].
 unfold csem_map_S, csem_map.
 destruct (lt_dec i0 num_modules); try solve[elimtype False; omega].
 assert (l = PF) as -> by apply proof_irr.
 solve[eauto].
 solve[apply eq_nat_dec].
apply H8 in H.
solve[destruct H; auto].
destruct PRIV2 as [X Y].
eapply private_valid_inv_fwd; eauto.
solve[apply forward_nextblock in H8; auto].
split.

simpl.
destruct DISJ2.
split; auto.
apply private_disjoint_inv'_eq with (c := c0).
case_eq (at_external (get_module_csem (modules_S PF)) c).
2: intros ATEXT; rewrite ATEXT in AT_EXT; congruence.
intros [[ef' sig'] args'] ATEXT.
destruct (core_simulations i0).
rewrite <-Eqdep_dec.eq_rect_eq_dec in MATCH.
eapply core_at_external0 in MATCH; eauto.
destruct MATCH as [_ [_ [vals2 [_ [_ ATEXT2]]]]].
unfold csem_map_T, csem_map in ATEXT2.
destruct (lt_dec i0 num_modules); try solve[elimtype False; omega].
assert (l = PF0) by apply proof_irr.
subst.
intros; eapply private_external; eauto.
unfold csem_map_S, csem_map.
destruct (lt_dec i0 num_modules); try solve[elimtype False; omega].
assert (l = PF) as -> by apply proof_irr.
solve[eauto].
solve[apply eq_nat_dec].
solve[apply H].

simpl.
exists RR1.
split; auto.
destruct (core_simulations i0).
clear core_ord_wf0 core_diagram0 core_initial0 core_halted0 core_at_external0.
(*cut (match_state cd' j' c m1' c0 m2').
intros MATCH'.*)
case_eq (at_external (get_module_csem (modules_S PF)) c).
2: solve[intros AT_EXT'; rewrite AT_EXT' in AT_EXT; congruence].
intros [[ef' sig'] args'] AT_EXT'.
rewrite AT_EXT' in AT_EXT.
specialize (core_after_external0 cd' j j' c c0 m1 ef' args' ret1 m1' m2 m2' ret2 sig').
specialize (RGsim i0); destruct RGsim.
spec core_after_external0; auto.
solve[eapply match_state_inj; eauto].
spec core_after_external0; auto.
rewrite <-Eqdep_dec.eq_rect_eq_dec in MATCH.
solve[auto].
solve[apply eq_nat_dec].
spec core_after_external0; auto.
unfold csem_map_S, csem_map.
destruct (lt_dec i0 num_modules); try solve[elimtype False; omega].
solve[assert (l = PF) as -> by apply proof_irr; auto].
spec core_after_external0; auto.
solve[eapply match_state_preserves_globals; eauto].
spec core_after_external0; auto.
spec core_after_external0; auto.
spec core_after_external0; eauto.
spec core_after_external0; auto.
spec core_after_external0; auto.
spec core_after_external0; auto.
apply mem_unchanged_on_sub with (Q := fun b ofs => 
  loc_unmapped j b ofs /\
  (private_block (get_module_csem (modules_S PF)) c b \/
    private_blocks fS vS modules_S stack b)); auto.
intros b ofs [? ?]; split; auto.
generalize H0.
unfold csem_map_S, csem_map.
destruct (lt_dec i0 num_modules); try solve[elimtype False; omega].
solve[assert (l = PF) as -> by apply proof_irr; auto].
spec core_after_external0; auto.
spec core_after_external0; auto.
apply mem_unchanged_on_sub with (Q := fun b ofs => 
  loc_out_of_reach j m1 b ofs /\
  (private_block (get_module_csem (modules_T PF0)) c0 b \/
    private_blocks fT vT modules_T stack0 b)); auto.
intros b ofs [? ?]; split; auto.
generalize H0.
unfold csem_map_T, csem_map.
destruct (lt_dec i0 num_modules); try solve[elimtype False; omega].
solve[assert (l = PF0) as -> by apply proof_irr; auto].
spec core_after_external0.
unfold val_has_type_opt' in HAS_TY1.
assert (Heq: ef = ef').
 clear - AT_EXT.
 destruct ef'; try solve[congruence].
 destruct (procedure_linkage_table name); try solve[congruence].
solve[rewrite Heq in *; auto].
spec core_after_external0; auto.
unfold val_has_type_opt' in HAS_TY2.
assert (Heq: ef = ef').
 clear - AT_EXT.
 destruct ef'; try solve[congruence].
 destruct (procedure_linkage_table name); try solve[congruence].
solve[rewrite Heq in *; auto].
destruct core_after_external0 as [cd'' [st1' [st2' [EQ1 [EQ2 MATCH2]]]]].
clear - Heq1 Heq2 EQ1 EQ2 PF MATCH2.
unfold csem_map_S, csem_map_T, csem_map in *|-.
destruct (lt_dec i0 num_modules); try solve[elimtype False; omega].
assert (l = PF) as -> by apply proof_irr.
assert (PF0 = PF) as -> by apply proof_irr.
unfold genv_map in *.
rewrite Heq1 in EQ1; inv EQ1.
unfold genv_map in EQ2.
rewrite Heq2 in EQ2; inv EQ2.
rewrite <-Eqdep_dec.eq_rect_eq_dec; auto.
solve[exists cd''; auto].
solve[apply eq_nat_dec].
(*
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

(*mem_unch_on*)
apply mem_unchanged_on_sub with (Q := fun b ofs => 
  loc_unmapped j b ofs /\
  (private_block (get_module_csem (modules_S PF)) c b \/
    private_blocks fS vS modules_S stack b)); auto.
intros b ofs [? X]; split; auto.
unfold csem_map_S, csem_map in X.
destruct (lt_dec i0 num_modules); try solve[elimtype False; omega].
solve[assert (PF = l) as -> by apply proof_irr; auto].
apply mem_unchanged_on_sub with (Q := fun b ofs => 
  loc_out_of_reach j m1 b ofs /\
  (private_block (get_module_csem (modules_T PF0)) c0 b \/
    private_blocks fT vT modules_T stack0 b)); auto.
intros b ofs [? X]; split; auto.
unfold csem_map_T, csem_map in X.
destruct (lt_dec i0 num_modules); try solve[elimtype False; omega].
solve[assert (PF0 = l) as -> by apply proof_irr; auto].

rewrite <-Eqdep_dec.eq_rect_eq_dec in MATCH; auto.
solve[apply eq_nat_dec].
*)

(*BEGIN tl_inv PROOF*)
clear H2 AT_EXT.
assert (INJJ: Mem.inject j m1 m2).
 destruct (RGsim i0).
 solve[eapply match_state_inj; eauto].
clear - RR2 H3 H4 H5 H6 H7 H8 H9 PF RGsim INJJ.
revert stack0 RR2 H9; induction stack; auto.
intros stack0 RR2 H9; destruct stack0; simpl in RR2. 
solve[destruct a; elimtype False; auto].
destruct a; destruct f.
destruct RR2 
 as [[PF' [cd0 [j0 [m10 [m20 [QQ1 [QQINJ [QQ2 [QQ3 [QQ4 [QQ5 [QQ6 MATCH'']]]]]]]]]]]] STACK'].
subst.
rewrite <-Eqdep_dec.eq_rect_eq_dec in QQ1; try solve[apply eq_nat_dec].
simpl.
split; auto.
exists (@refl_equal _ i); exists cd0; exists j0; exists m10; exists m20.
split; auto.
split; auto.
split; auto.
solve[eapply inject_incr_trans; eauto].
split; auto.
solve[eapply inject_separated_incr_fwd2; eauto].
split; auto.
eapply mem_forward_trans; eauto.
split; auto.

eapply mem_unchanged_unmapped_trans; eauto.
simpl in H7.
apply mem_unchanged_on_sub with (Q := fun b ofs => 
  loc_unmapped j b ofs /\
  (private_block (get_module_csem (modules_S PF)) c b \/
    private_block (get_module_csem (modules_S PF1)) c1 b \/
    private_blocks fS vS modules_S stack b)); auto.
solve[intros b ofs [? ?]; split; auto].

split; auto.
solve[eapply mem_forward_trans; eauto].

apply (@unchanged_outofreach_trans _ _ _ _ m10 m1 m20 m2 m2' j0 j); auto.
intros b ofs p H1 H2.
solve[destruct (QQ4 b H1); auto].
simpl in H9.
apply mem_unchanged_on_sub with (Q := fun b ofs => 
  loc_out_of_reach j m1 b ofs /\
  (private_block (get_module_csem (modules_T PF0)) c0 b \/
    private_block (get_module_csem (modules_T PF2)) c2 b \/
    private_blocks fT vT modules_T stack0 b)); auto.
solve[intros b ofs [? ?]; split; auto].

apply IHstack; auto.
apply mem_unchanged_on_sub with (Q := fun b ofs => 
  loc_unmapped j b ofs /\
  (private_block (get_module_csem (modules_S PF)) c b \/
    private_block (get_module_csem (modules_S PF1)) c1 b \/
    private_blocks fS vS modules_S stack b)); auto.
intros b ofs [? ?]; split; auto.
solve[destruct H0; auto].
apply mem_unchanged_on_sub with (Q := fun b ofs => 
  loc_out_of_reach j m1 b ofs /\
  (private_block (get_module_csem (modules_T PF0)) c0 b \/
    private_block (get_module_csem (modules_T PF2)) c2 b \/
    private_blocks fT vT modules_T stack0 b)); auto.
intros b ofs [? ?]; split; auto.
solve[destruct H0; auto].
(*END tl_inv PROOF*)

(*3: extension_diagram*)
unfold CompilabilityInvariant.match_states; simpl. 
intros until j; intros H1 H2 H3 H4 H5 H6; 
 intros [_ [_ [_ [_ [RR [H7 H8]]]]]] H9 H10 H11 H12 STEP.
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
assert (Hef: ef = EF_external id sig0).
 clear - AT_EXT H5 H1 pf_i.
 destruct (eq_nat_dec (linker_active s2) (linker_active s2)); 
  try solve[elimtype False; omega].
 rewrite<-Eqdep_dec.eq_rect_eq_dec in H1.
 inv H1.
 unfold csem_map_S, csem_map in H5.
 destruct (lt_dec (linker_active s2) num_modules); try solve[elimtype False; omega].
 assert (l = pf_i) by apply proof_irr.
 subst l.
 rewrite AT_EXT in H5.
 solve[inv H5; auto].
 solve[apply eq_nat_dec].
rewrite Hef in *.
destruct (eq_nat_dec (linker_active s2) (linker_active s2)); try solve[omega].
rewrite dependent_types_nonsense in H1; inv H1.
rename j0 into k.
destruct (core_simulations k).
specialize (core_initial0 (Vptr b (Int.repr 0)) (Vptr b (Int.repr 0)) 
  (ef_sig (EF_external id sig0))).
spec core_initial0; auto.
assert (sig = sig0) as Heq.
 clear - H5 AT_EXT.
 unfold csem_map_S, csem_map in H5.
 destruct (lt_dec (linker_active s2) num_modules); try solve[elimtype False; omega].
 assert (Heq: l = pf_i) by apply proof_irr; auto; subst.
 solve[rewrite H5 in AT_EXT; inv AT_EXT; auto].
rewrite Heq in *; clear Heq.
specialize (core_initial0 args1 c' m1' j args2 m2).
spec core_initial0; auto.
clear - H5 AT_EXT H15.
unfold csem_map_S, csem_map in H5.
destruct (lt_dec (linker_active s2) num_modules); try solve[elimtype False; omega].
assert (Heq: l = pf_i) by apply proof_irr; auto.
subst; rewrite H5 in AT_EXT; inv AT_EXT.
unfold csem_map_S, csem_map, genv_mapS, genvs.
generalize (plt_ok LOOKUP) as plt_ok'; intro.
destruct (lt_dec k num_modules); try solve[elimtype False; omega].
assert (Heq: l = plt_ok LOOKUP) by apply proof_irr; auto.
solve[subst; auto].
spec core_initial0; auto.
spec core_initial0; auto.
spec core_initial0; auto.
simpl.
destruct core_initial0 as [cd' [c'' [INIT MATCH]]].
destruct s2; simpl in H2; induction stack0.
solve[simpl in stack_nonempty; elimtype False; omega].
destruct a.
destruct (eq_nat_dec i i); try solve[elimtype False; omega].
rewrite dependent_types_nonsense in H2.
inversion H2; rewrite H7 in *; clear H7.
simpl in *.
destruct RR as [PRIV1 [DISJ1 [PRIV2 [DISJ2 [RR1 [RR2 STACK_INV]]]]]].
generalize STACK_INV as STACK_INV'; intro.
apply tl_inv_length_eq in STACK_INV. 
assert (CALLERS: 
 all_at_external fT vT modules_T (List.tail (mkFrame k (plt_ok LOOKUP) c'' :: 
  mkFrame i pf_i c2 :: stack0))).
 simpl.
 apply List.Forall_cons.
 exists (EF_external id sig0); exists sig0; exists args2.
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

(*BEGIN private lemmas*)
unfold private_valid.
simpl.
intros.
destruct (eq_nat_dec i0 k); try solve[congruence].
subst.
elimtype False.
eapply private_initial in H15.
apply H15.
erewrite <-Eqdep_dec.eq_rect_eq_dec in H1.
inv H1.
unfold csem_map_S, csem_map in H16.
destruct (lt_dec k num_modules); try solve[congruence].
assert (plt_ok LOOKUP = l) as -> by apply proof_irr.
solve[eauto].
generalize (plt_ok LOOKUP); intro CONTRA.
elimtype False.
solve[apply n; auto].
solve[apply eq_nat_dec].
split.
unfold private_disjoint.
intros until d; intros NEQ; simpl; intros.
destruct (eq_nat_dec i0 k); try solve[congruence].
solve[destruct (eq_nat_dec j0 k); try solve[congruence]].
split.
unfold private_valid.
simpl.
intros.
destruct (eq_nat_dec i0 k); try solve[congruence].
subst.
erewrite <-Eqdep_dec.eq_rect_eq_dec in H1.
inv H1.
eapply private_initial in INIT.
elimtype False.
solve[eauto].
solve[apply eq_nat_dec].
split.
unfold private_disjoint.
simpl.
intros.
destruct (eq_nat_dec i0 k); try solve[congruence].
solve[destruct (eq_nat_dec j0 k); try solve[congruence]].
split.
split.
split.
intros b0 PRIV.
eapply private_initial in H15.
solve[elimtype False; apply H15; eauto].
destruct PRIV1.
solve[split; auto].
split; auto.
split; auto.
destruct PRIV1.
split; auto.
intros b0 PRIV.
eapply private_initial in H15.
solve[elimtype False; apply H15; eauto].
apply private_disjoint_inv'_initialS.
intros b0 CONTRA.
eapply private_initial in H15.
apply H15.
unfold csem_map_S, csem_map in CONTRA.
destruct (lt_dec k num_modules).
assert (plt_ok LOOKUP = l) as -> by apply proof_irr.
solve[eauto].
generalize (plt_ok LOOKUP).
intros.
solve[elimtype False; auto].
split.
simpl.
split.
intros b0 PRIV.
eapply private_initial in INIT.
elimtype False; apply INIT.
unfold csem_map_T, csem_map.
destruct (lt_dec k num_modules); try solve[congruence].
assert (l = plt_ok LOOKUP) as -> by apply proof_irr.
solve[eauto].
generalize (plt_ok LOOKUP).
solve[intros; elimtype False; auto].
destruct PRIV2 as [X Y].
split; auto.
intros.
apply X.
assert (PF = pf_i) as -> by apply proof_irr.
solve[auto].
split.
destruct PRIV2 as [X Y].
simpl.
split; auto.
split; auto.
intros.
eapply private_initial in INIT.
intros CONTRA.
eapply INIT.
unfold csem_map_T, csem_map.
destruct (lt_dec k num_modules).
assert (l = plt_ok LOOKUP) as -> by apply proof_irr.
solve[eauto].
generalize (plt_ok LOOKUP).
solve[intros; elimtype False; auto].
apply private_disjoint_inv'_initialT.
intros b0 CONTRA.
eapply private_initial in INIT.
solve[apply INIT; eauto].
split.
destruct DISJ2 as [Z0 W].
assert (pf_i = PF) as -> by apply proof_irr.
solve[auto].
destruct DISJ2 as [Z0 W].
assert (pf_i = PF) as -> by apply proof_irr.
solve[auto].
(*END private lemmas*)

exists (@refl_equal _ k).
destruct RR2 as [cd'' RR2].
split.
solve[eexists; eauto].
split; auto.
exists RR1.
exists cd''; exists j; exists m1'; exists m2.
split; auto.
split; auto.
split; auto.
split; auto.
solve[apply inject_separated_same_meminj].
split; auto.
solve[apply mem_forward_refl].
split; auto.
solve [constructor; split; auto; split; trivial].
split; auto.
solve[apply mem_forward_refl].
solve [constructor; split; auto; split; trivial].
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
unfold ExtendedSimulations.core_datas_upd.
solve[rewrite data_upd_same; auto].
congruence.

split. 
solve [constructor; split; auto; split; trivial].
split.
solve [constructor; split; auto; split; trivial].
left.
exists O; simpl.
exists (mkLinkerCoreState 
 (mkFrame k (plt_ok LOOKUP) c'' :: mkFrame i pf_i c2 :: stack0) (length_cons _ _) CALLERS).
exists m2.
split; auto.
assert (Heq: pf_i = PF) by apply proof_irr; auto.
subst pf_i.
apply link_call 
 with (args := args2) (sig := sig0) (b := b); auto.
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
solve[assert (l = PF) as -> by apply proof_irr; auto].
(*clear - H5 AT_EXT H6. 
unfold csem_map_S, csem_map in H5.
destruct (lt_dec i num_modules); try solve[elimtype False; omega].
assert (l = PF) by apply proof_irr; auto; subst.
solve[rewrite H5 in AT_EXT; inv AT_EXT; auto].*)
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
unfold csem_map_T, csem_map, genv_mapT, genvs in INIT.
generalize (plt_ok LOOKUP) as plt_ok'; intro.
destruct (lt_dec k num_modules); try solve[elimtype False; omega].
solve[assert (plt_ok' = l) as -> by apply proof_irr; auto].
try congruence.   (* Coq 8.3/8.4 compatibility *)

(*'return' case*)
destruct (eq_nat_dec (linker_active s2) (linker_active s2)); try solve[omega].
inv H1.
rewrite dependent_types_nonsense in H3, H5.
edestruct (@at_external_halted_excl 
 (Genv.t (fS (linker_active s2)) (vS (linker_active s2)))
 (cS (linker_active s2)) mem 
 (list (ident * globdef (fS (linker_active s2)) (vS (linker_active s2)))) 
 (csem_map_S (linker_active s2)) c').
unfold genv_map in *.
congruence.
elimtype False; clear - HALTED H1 plt_ok.
unfold csem_map_S, csem_map in H1.
destruct (lt_dec (linker_active s2) num_modules); try solve[omega].
assert (Heq: l = pfj) by apply proof_irr; auto.
unfold genv_map in *.
solve[subst; congruence].
try congruence.   (* Coq 8.3/8.4 compatibility *)

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
rewrite H6 in H5.
assert (PF = PF0) as -> by apply proof_irr; auto.
rewrite H12.
destruct ef; auto.
solve[destruct (procedure_linkage_table name); try solve[congruence]].

(*5: initial_core_diagram*)
intros until sig; intros H1 H2 H3 H4 H5.
destruct s1; simpl in *.
unfold linker_initial_core in H2.
case_eq v1.
solve[intros V; rewrite V in *; try solve[congruence]].
intros i V.
rewrite V in H2.
destruct v1; try solve[congruence].
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
 (initial_core (get_module_csem (modules_S (plt_ok PLT)))
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
unfold linker_initial_core.
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
assert (plt_ok (Logic.eq_sym e) = l) as -> by apply proof_irr; auto.
unfold genv_map in INIT.
rewrite INIT.
solve[assert (l = plt_ok PLT0) as -> by apply proof_irr; auto].
exfalso. apply H0; trivial. 

revert H2.
generalize (refl_equal (procedure_linkage_table main_id)).
generalize PLT.
pattern (procedure_linkage_table main_id) at 0 2 4.
rewrite PLT in *.
intros ? e.
assert (plt_ok (Logic.eq_sym e) = plt_ok PLT) as -> by apply proof_irr.
rewrite H7.
inversion 1; subst.
split.

(*BEGIN private lemmas*)
unfold private_valid.
simpl.
intros.
destruct (eq_nat_dec i0 n); try solve[congruence].
subst.
elimtype False.
eapply private_initial in H7.
apply H7.
erewrite <-Eqdep_dec.eq_rect_eq_dec in H0.
inv H0.
unfold csem_map_S, csem_map in H8.
destruct (lt_dec n num_modules); try solve[congruence].
assert (plt_ok PLT = l) as -> by apply proof_irr.
solve[eauto].
generalize (plt_ok PLT); intro CONTRA.
solve[elimtype False; eauto].
solve[apply eq_nat_dec].
split.
unfold private_disjoint.
intros until d; intros NEQ; simpl; intros.
destruct (eq_nat_dec i0 n); try solve[congruence].
solve[destruct (eq_nat_dec j0 n); try solve[congruence]].
split.
unfold private_valid.
simpl.
intros.
destruct (eq_nat_dec i0 n); try solve[congruence].
subst.
erewrite <-Eqdep_dec.eq_rect_eq_dec in H0.
inv H0.
eapply private_initial in INIT.
elimtype False.
solve[eauto].
solve[apply eq_nat_dec].
split.
unfold private_disjoint.
simpl.
intros.
destruct (eq_nat_dec i0 n); try solve[congruence].
solve[destruct (eq_nat_dec j0 n); try solve[congruence]].
split.
split.
split.
intros b0 PRIV.
eapply private_initial in H7.
solve[elimtype False; apply H7; eauto].
simpl; auto.
split; simpl; auto.
split; auto.
split; auto.
intros b0 PRIV.
eapply private_initial in INIT.
elimtype False; apply INIT.
unfold csem_map_T, csem_map.
destruct (lt_dec n num_modules); try solve[congruence].
assert (l = plt_ok PLT0) as -> by apply proof_irr.
solve[eauto].
generalize (plt_ok PLT).
solve[intros; elimtype False; auto].
split; auto.
(*END private lemmas*)

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
unfold ExtendedSimulations.core_datas_upd.
solve[rewrite data_upd_same; auto].

intros H7.
revert H2.
generalize (refl_equal (procedure_linkage_table main_id)).
generalize PLT.
pattern (procedure_linkage_table main_id) at 0 2 4.
rewrite PLT in *.
intros ? e.
assert (plt_ok (Logic.eq_sym e) = plt_ok PLT) as -> by apply proof_irr.
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

(*6: halted_step*)
intros until rty.
intros H1 H2.
unfold linker_halted in H2.
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
destruct H1 as [_ [_ [_ [_ [RR [H1 H3]]]]]].
simpl in *. 
specialize (H3 (linker_active c2)).
rewrite Hstack in H1, H3.
subst i.
destruct (eq_nat_dec (linker_active c2) (linker_active c2)); try solve[elimtype False; omega].
specialize (H3 c).
rewrite dependent_types_nonsense in H3.
spec H3; auto.
destruct H3 as [c3 [H3 H4]].
generalize core_halted0; intro core_halted1.
specialize (core_halted1 (cd (linker_active c2)) j c m1 c3 m2 v1 rty H4).
spec core_halted1; auto.
generalize H2.
unfold csem_map_S, csem_map.
destruct (lt_dec (linker_active c2) num_modules); try solve[elimtype False; omega].
solve[assert (PF = l) as -> by apply proof_irr; auto].
intros HAS_TY.
destruct core_halted1 as [v2 [H5 [H6 H7]]]; auto.
exists v2.
split; auto.
split; auto.
unfold linker_halted.
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
solve[intros [? [? [? [? [? [? FALSE]]]]]]; elimtype False; auto].

(*7: halted_diagram*)
intros until c2; intros H1 H2 H3 H4 H5.
destruct (core_simulations (linker_active s1)).

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
solve[rewrite H6; intros; congruence].
simpl in H2.
destruct (eq_nat_dec i i); try solve[elimtype False; omega].
rewrite dependent_types_nonsense in H2; inversion H2; subst c1.
simpl in H4.
unfold csem_map_S, csem_map in H4.
destruct (lt_dec i num_modules); try solve[elimtype False; omega].
generalize @at_external_halted_excl; intros H5.
specialize (H5 _ _ _ _ (get_module_csem (modules_S l)) c).
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
rewrite dependent_types_nonsense in H3; inversion H3; subst c0.
destruct H1 as [_ [_ [_ [_ [RR [H1 H7]]]]]].
simpl in *.
unfold R, R_inv in *.
destruct RR as [PRIV1 [DISJ1 [PRIV2 [DISJ2 [RR1 [RR2 RR3]]]]]].
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
destruct RR3 as [[PF' [cd0 [j0 [m10 [m20 [QQmatch [QQ1 [QQ2 [QQ3 [QQ4 [QQ5 [QQ6 QQ7]]]]]]]]]]]] TL].
subst i1.
generalize ext_pf.
unfold all_at_external.
inversion 1; subst.
(*destruct H3 as [ef [sig [args AT_EXT]]].*)
clear core_after_external0.
destruct (core_simulations i).
clear core_ord_wf0 core_diagram0 core_initial0 core_halted0 core_at_external0.
simpl in ext_pf0.
inv ext_pf0.
destruct H3 as [ef0 [sig0 [args0 AT_EXT0]]].

destruct (core_simulations i0).
specialize (core_halted0 (cd i0) j c' m1' c3 m2 rv1 (proj_sig_res (ef_sig ef))).
spec core_halted0; auto.
spec core_halted0; auto.
spec core_halted0; auto.
assert (Heq: rv1 = retv).
 clear - HALTED H4 PF.
 unfold csem_map_S, csem_map in H4.
 destruct (lt_dec i0 num_modules); try solve[elimtype False; omega].
 assert (l = pfj) by apply proof_irr; auto.
 subst l.
 rewrite HALTED in H4.
 solve[inv H4; auto].
solve[subst rv1; auto].
destruct core_halted0 as [rv2 [X1 [X2 [X3 X4]]]].

exists rv2; split; auto.
split; auto.

specialize (core_after_external0 
 cd0 j0 j c c0 m10 ef0 args0 (Some rv1) m1' m20 m2 (Some rv2) sig0).
spec core_after_external0; auto.
spec core_after_external0; auto.
spec core_after_external0; auto.
unfold csem_map_S, csem_map.
destruct (lt_dec i num_modules); try solve[elimtype False; omega].
solve[assert (l = pf_i) as -> by apply proof_irr; auto].
spec core_after_external0; auto.
solve[destruct (RGsim i); eapply match_state_preserves_globals; eauto].
spec core_after_external0; auto.
spec core_after_external0; auto.
spec core_after_external0; auto.
destruct (RGsim i0).
rewrite <-Eqdep_dec.eq_rect_eq_dec in MATCH.
(*eapply match_state_inj; eauto.*)
(*solve[apply eq_nat_dec].*)
spec core_after_external0; auto.
spec core_after_external0; auto.
spec core_after_external0; auto.
unfold csem_map_S, csem_map.
destruct (lt_dec i num_modules); try solve[elimtype False; omega].
solve[assert (l = pf_i) as -> by apply proof_irr; auto].
spec core_after_external0; auto.
spec core_after_external0; auto.
unfold csem_map_T, csem_map.
destruct (lt_dec i num_modules); try solve[elimtype False; omega].
solve[assert (l = PF0) as -> by apply proof_irr; auto].
spec core_after_external0.
assert (Heq: rv1 = retv).
 clear - HALTED H4 PF.
 unfold csem_map_S, csem_map in H4.
 destruct (lt_dec i0 num_modules); try solve[elimtype False; omega].
 assert (l = pfj) by apply proof_irr; auto.
 subst l.
 rewrite HALTED in H4.
 solve[inv H4; auto].
rewrite Heq in *.
assert (Heq': sig = sig0).
 clear - AT_EXT AT_EXT0.
 rewrite AT_EXT in AT_EXT0.
 solve[inv AT_EXT0; auto].
subst sig.
clear - AT_EXT AT_EXT0 TYCHECKS.
simpl.
cut (ef0 = ef).
intros ->; auto.
rewrite AT_EXT in AT_EXT0.
solve[inv AT_EXT0; auto].
destruct core_after_external0 as 
 [cd2 [_c [_c0 [AFTER1 [AFTER2 MATCH12]]]]].
simpl.
cut (ef0 = ef).
intros ->; auto.
rewrite AT_EXT in AT_EXT0.
solve[inv AT_EXT0; auto].

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
assert (PF = pfj) as -> by apply proof_irr.

destruct (core_simulations i0).
clear core_ord_wf0 core_diagram0 core_initial0 core_at_external0 core_after_external0.
specialize (core_halted0 (cd i0) j c' m1' c3 m2 rv1 (proj_sig_res (ef_sig ef))).
spec core_halted0; auto.
spec core_halted0; auto.
destruct core_halted0 as [v2' [? [? ?]]]; auto.
assert (Heq: rv1 = retv).
 clear - HALTED H4 PF.
 unfold csem_map_S, csem_map in H4.
 destruct (lt_dec i0 num_modules); try solve[elimtype False; omega].
 assert (l = pfj) by apply proof_irr; auto.
 subst l.
 rewrite HALTED in H4.
 solve[inv H4; auto].
solve[subst rv1; auto].
 
unfold all_at_external in callers_at_external.
simpl in callers_at_external.
inversion callers_at_external.
subst x.
destruct H13 as [ef00 [sig00 [args00 AT_EXT00]]].
apply link_return with (retv := v2') (ef := ef00) (sig := sig00) (args := args00); auto.
unfold csem_map_T, csem_map in H9.
destruct (lt_dec i0 num_modules); try solve[elimtype False; omega].
solve[assert (pfj = l0) as -> by apply proof_irr; auto].

simpl.
destruct H10 as [HASTY2 H10].
assert (Heq: rv1 = retv).
 clear - HALTED H4 PF.
 unfold csem_map_S, csem_map in H4.
 destruct (lt_dec i0 num_modules); try solve[elimtype False; omega].
 assert (l = pfj) by apply proof_irr; auto.
 subst l.
 solve[rewrite H4 in HALTED; inv HALTED; auto].
subst rv1.

assert (Heq2: ef = ef00).
 specialize (core_at_external1 cd0 j0 c m10 c0 m20 ef args sig).
 spec core_at_external1; auto.
 spec core_at_external1; auto.
 clear - AT_EXT PF.
 unfold csem_map_S, csem_map. 
 destruct (lt_dec i num_modules); try solve[elimtype False; omega].
 solve[assert (l = PF0) as -> by apply proof_irr; auto].
 destruct core_at_external1 as [? [? [? [? [? AT_EXT00']]]]].
 clear - PF0 AT_EXT00 AT_EXT00'.
 unfold csem_map_T, csem_map in AT_EXT00'.
 destruct (lt_dec i num_modules); try solve[elimtype False; omega].
 assert (l = PF0) by apply proof_irr.
 subst l.
 unfold genv_map in *. 
 rewrite AT_EXT00' in AT_EXT00.
 solve[inv AT_EXT00; auto].
solve[subst ef; auto].

intros k pf_k.
unfold genv_mapT, genvs in domain_eq_T.
specialize (domain_eq_T k).
destruct (lt_dec k num_modules); try solve[elimtype False; omega].
solve[assert (pf_k = l0) as -> by apply proof_irr; auto].
unfold csem_map_T, csem_map in AFTER2.
cut (v2' = rv2).
intros ->.
destruct (lt_dec i num_modules); try solve[elimtype False; omega].
solve[assert (PF0 = l0) as -> by apply proof_irr; auto].
clear - H9 X2.
rewrite H9 in X2.
solve[inv X2; auto].
split.
split.
simpl.

(*BEGIN private lemmas*)
unfold private_valid.
simpl.
intros.
destruct (eq_nat_dec i1 i); try solve[congruence].
subst.
eapply private_external in H6; eauto.
erewrite <-Eqdep_dec.eq_rect_eq_dec in H1.
inv H1.
unfold csem_map_S, csem_map in H2.
destruct (lt_dec i num_modules); try solve[congruence].
assert (pf_i = l) by apply proof_irr.
subst.
destruct PRIV1 as [X [Y Z0]].
solve[apply Y; eauto].
solve[apply eq_nat_dec].
erewrite <-Eqdep_dec.eq_rect_eq_dec in H1.
inv H1.
unfold csem_map_S, csem_map in H2.
destruct (lt_dec i num_modules); try solve[elimtype False; omega].
assert (pf_i = l) as -> by apply proof_irr.
solve[auto].
solve[apply eq_nat_dec].

split.
unfold private_disjoint.
intros until d; intros NEQ; simpl; intros.
destruct (eq_nat_dec i1 i); try solve[congruence].
solve[destruct (eq_nat_dec j1 i); try solve[congruence]].
split.
unfold private_valid.
simpl.
intros.
destruct (eq_nat_dec i1 i); try solve[congruence].
subst.
eapply core_at_external1 in QQmatch; eauto.
2: unfold csem_map_S, csem_map.
2: destruct (lt_dec i num_modules); try solve[elimtype False; omega].
2: solve[assert (l = pf_i) as -> by apply proof_irr; eauto].
destruct QQmatch as [_ [_ [vals2 [_ [_ ATEXT2]]]]].
rewrite <-Eqdep_dec.eq_rect_eq_dec in ATEXT2.
eapply private_external in AFTER2; eauto.
destruct PRIV2 as [X [Y Z0]].
unfold csem_map_T, csem_map in AFTER2.
destruct (lt_dec i num_modules); try solve[elimtype False; omega].
assert (PF0 = l) by apply proof_irr.
subst.
solve[apply Y in AFTER2; eauto].
rewrite <-Eqdep_dec.eq_rect_eq_dec in H1.
solve[inv H1; auto].
solve[apply eq_nat_dec].
solve[apply eq_nat_dec].
(*unfold csem_map_S, csem_map.
destruct (lt_dec i num_modules); try solve[elimtype False; omega].
assert (l = pf_i) as -> by apply proof_irr.
subst.
solve[eauto].*)
split.
unfold private_disjoint.
simpl.
intros.
destruct (eq_nat_dec i1 i); try solve[congruence].
solve[destruct (eq_nat_dec j1 i); try solve[congruence]].
split.
split.
split.
intros b0 PRIV.
eapply private_external in H6; eauto.
destruct PRIV1 as [X [Y Z0]].
solve[apply Y; auto].
destruct PRIV1 as [X [Y Z0]].
solve[auto].
split.
destruct DISJ1 as [X [Y Z0]].
eapply private_disjoint_inv_eq.
intros.
eapply private_external; eauto.
simpl.
split; auto.
split.
simpl.
split.
intros.
eapply core_at_external1 in QQmatch; eauto.
destruct QQmatch as [_ [_ [vals2 [_ [_ ATEXT2]]]]].
rewrite <-Eqdep_dec.eq_rect_eq_dec in ATEXT2.
eapply private_external in AFTER2; eauto.
destruct PRIV2 as [X [Y Z0]].
apply Y.
unfold csem_map_T, csem_map in AFTER2.
destruct (lt_dec i num_modules).
assert (pf_i = l) by apply proof_irr.
subst.
assert (PF0 = l) as -> by apply proof_irr.
solve[eauto].
solve[elimtype False; auto].
unfold csem_map_T, csem_map.
destruct (lt_dec i num_modules); try solve[elimtype False; omega].
assert (l = pf_i) as -> by apply proof_irr.
solve[eauto].
solve[apply eq_nat_dec].
unfold csem_map_S, csem_map.
destruct (lt_dec i num_modules); try solve[elimtype False; omega].
assert (l = pf_i) as -> by apply proof_irr.
solve[eauto].
solve[destruct PRIV2 as [? [? ?]]; auto].
split.
destruct DISJ2 as [X [Y Z0]].
eapply private_disjoint_inv_eq.
eapply core_at_external1 in QQmatch; eauto.
unfold csem_map_S, csem_map.
destruct (lt_dec i num_modules); try solve[elimtype False; omega].
assert (l = pf_i) as -> by apply proof_irr.
solve[eauto].
simpl.
split; auto.
assert (AT_EXT': at_external (csem_map_S i) c = Some (ef, sig, args)).
 unfold csem_map_S, csem_map.
 destruct (lt_dec i num_modules); try solve[elimtype False; omega].
 rewrite <-AT_EXT.
 solve[assert (l = pf_i) as -> by apply proof_irr; auto].
eapply core_at_external1 in QQmatch; eauto.
destruct QQmatch as [_ [_ [vals2 [_ [_ ATEXT2]]]]].
rewrite <-Eqdep_dec.eq_rect_eq_dec in ATEXT2.
2: solve[apply eq_nat_dec].
apply private_disjoint_inv'_eq with (c := c0); auto.
intros.
eapply private_external; eauto.
unfold csem_map_T, csem_map in ATEXT2.
destruct (lt_dec i num_modules); try solve[elimtype False; omega].
assert (pf_i = l) as -> by apply proof_irr.
solve[eauto].
unfold csem_map_T, csem_map in AFTER2.
destruct (lt_dec i num_modules); try solve[elimtype False; omega].
assert (pf_i = l) as -> by apply proof_irr.
solve[eauto].
assert (pf_i = PF0) as -> by apply proof_irr.
solve[eauto].
(*END private lemmas*)

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
unfold genv_map in *.
rewrite AFTER1 in H6.
solve[inv H6; auto].
clear - HALTED H4 PF.
unfold csem_map_S, csem_map in H4.
destruct (lt_dec i0 num_modules); try solve[elimtype False; omega].
assert (l = pfj) by apply proof_irr; subst.
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
unfold ExtendedSimulations.core_datas_upd.
rewrite data_upd_same.
cut (c1 = _c).
solve[intros ->; auto].
cut (rv1 = retv).
intros ->.
clear - AFTER1 H6 PF0.
unfold csem_map_S, csem_map in AFTER1.
destruct (lt_dec i num_modules); try solve[elimtype False; omega].
assert (Heq: l = pf_i) by apply proof_irr.
subst l.
unfold genv_map in *. 
rewrite AFTER1 in H6.
solve[inv H6; auto].
clear - HALTED H4 PF.
unfold csem_map_S, csem_map in H4.
destruct (lt_dec i0 num_modules); try solve[elimtype False; omega].
assert (l = pfj) by apply proof_irr; subst.
solve[rewrite H4 in HALTED; inv HALTED; auto].

solve[split; split; auto; intros; split; trivial].
solve[apply eq_nat_dec].
Qed.

End LinkerCompilable.
  
