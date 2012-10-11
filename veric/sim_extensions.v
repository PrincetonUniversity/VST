Add LoadPath "..".
Require Import veric.sim.

Set Implicit Arguments.

Notation mem := Memory.mem.

Section extension.
Variables (G C1 C2 M D: Type) (CS: CoreSemantics G C1 M D).

Let corestate := (C1*C2)%type.

Variable init_extended_core: forall (genv: G) (f: Values.val) (args: list Values.val),
  option C2.

Definition make_initial_core genv f args := 
  match make_initial_core CS genv f args, init_extended_core genv f args with 
  | Some c1, Some c2 => Some (c1, c2) 
  | _, _ => None 
  end.

Variable handled: AST.external_function -> bool.

Definition at_external' (c: corestate) :=
  match c with (c1, c2) => 
    match at_external CS c1 with 
    | None => None
    | Some (f, args) => if handled f then None else Some (f, args)
    end end.

Definition after_external (ret: Values.val) (c: corestate): option corestate :=
  match c with (c1, c2) => 
    match after_external CS ret c1 with 
    | None => None
    | Some c1' => Some (c1', c2)
    end end.

Definition safely_halted (genv: G) (c: corestate): option Integers.Int.int := None. (*??*)

Variable handled_step: G -> AST.external_function -> list Values.val -> C2 -> M -> 
                            Values.val -> C2 -> M -> Prop.

Variable handled_step_handled: 
  forall genv f args c2 m ret c2' m',
  handled_step genv f args c2 m ret c2' m' -> 
  handled f = true.

Inductive corestep': G -> corestate -> M -> corestate -> M -> Prop :=
| step_core: forall g c1 c2 m c1' m',
  corestep CS g c1 m c1' m' -> 
  corestep' g (c1, c2) m (c1', c2) m'
| step_extend: forall g c1 c2 m c2' m' f args ret c',
  at_external CS c1 = Some (f, args) -> 
  handled_step g f args c2 m ret c2' m' -> 
  after_external ret (c1, c2') = Some c' -> 
  corestep' g (c1, c2) m c' m'.

Program Definition extendCS := Build_CoreSemantics G corestate M D
  (@initial_mem _ _ _ _ CS)
  make_initial_core
  at_external'
  after_external
  safely_halted
  corestep' 
  _ _ _.
Next Obligation.
inversion H; subst; simpl.
erewrite (corestep_not_at_external CS); eauto.
rewrite H0; erewrite handled_step_handled; eauto.
Qed.

End extension.

Section compcert_extension.
Variables (G C1 C2 D: Type) (CS: CompcertCoreSem G C1 D).
Let corestate := (C1 * C2)%type.
Variables 
  (init_extended_core : G -> Values.val -> list Values.val -> option C2)
  (handled : AST.external_function -> bool)
  (handled_step : G ->
                  AST.external_function ->
                  list Values.val -> C2 -> mem -> Values.val -> C2 -> mem -> Prop)
  (handled_step_handled : forall (genv : G) (f : AST.external_function)
                            (args : list Values.val) 
                            (c2 : C2) (m : mem) (ret : Values.val) 
                            (c2' : C2) (m' : mem),
                          handled_step genv f args c2 m ret c2' m' ->
                          handled f = true)
  (handled_step_det : forall genv f args c2 m ret ret' c2' m' c2'' m'',
    handled_step genv f args c2 m ret c2' m' ->
    handled_step genv f args c2 m ret' c2'' m'' ->
    c2'=c2'' /\ m'=m'' /\ ret=ret')
  (handled_step_allowed_core_modifications : forall genv f args c2 m ret c2' m',
    handled_step genv f args c2 m ret c2' m' ->
    allowed_core_modification m m').

Definition extended_coresem :=
  extendCS CS init_extended_core handled handled_step handled_step_handled.

Program Definition extendCCS := Build_CompcertCoreSem G corestate D
  extended_coresem _ _.
Next Obligation.
inversion H; subst; inversion H0; subst.
cut ((c1', m1) = (c1'0, m2)).
inversion 1; subst; auto.
eapply csem_corestep_fun; eauto.
apply corestep_not_at_external in H1; rewrite H1 in H4; congruence.
apply corestep_not_at_external in H10; rewrite H10 in H1; congruence.
rewrite H1 in H6; inversion H6; subst.
destruct (handled_step_det H2 H8) as [H20 [H21 H22]]; subst.
rewrite H12 in H3; inversion H3; subst; auto.
Qed.
Next Obligation.
inversion H; subst.
apply csem_allowed_modifications in H0; auto.
eapply handled_step_allowed_core_modifications; eauto.
Qed.

End compcert_extension.

(* NOTES: 
-1) extensions preserve safety; needs axioms about safety of handled_step at external calls
-2) preservation of simulation diagrams (probably 3 cases)
-3) define a simple extension with one external function call; show that it satisfies 
properties (1) and (2)
-4) do same for concurrency extension
*)