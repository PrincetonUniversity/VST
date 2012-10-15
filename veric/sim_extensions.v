Add LoadPath "..".
Require Import veric.sim veric.sim_step_lemmas.

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

Variable upd_globstate: C1 -> C2 -> option C2.

Definition after_external' (ret: Values.val) (c: corestate): option corestate :=
  match c with (c1, c2) => 
    match after_external CS ret c1 with 
    | None => None
    | Some c1' => match upd_globstate c1' c2 with 
                  | None => None
                  | Some c2' => Some (c1', c2')
                  end
    end end.

Definition safely_halted (genv: G) (c: corestate): option Integers.Int.int := None. (*??*)

Variable handled_step: G -> AST.external_function -> list Values.val -> C2 -> M -> 
                            Values.val -> C2 -> M -> Prop.

Variable handled_step_handled: 
  forall genv f args c2 m ret c2' m',
  handled_step genv f args c2 m ret c2' m' -> 
  handled f = true.

Inductive corestep': G -> corestate -> M -> corestate -> M -> Prop :=
| step_core: forall g c1 c2 m c1' c2' m',
  corestep CS g c1 m c1' m' -> 
  upd_globstate c1' c2 = Some c2' -> 
  corestep' g (c1, c2) m (c1', c2') m'
| step_extend: forall g c1 c2 m c2' m' f args ret c',
  at_external CS c1 = Some (f, args) -> 
  handled_step g f args c2 m ret c2' m' -> 
  after_external' ret (c1, c2') = Some c' -> 
  corestep' g (c1, c2) m c' m'.

Program Definition extendCS := Build_CoreSemantics G corestate M D
  (@initial_mem _ _ _ _ CS)
  make_initial_core
  at_external'
  after_external'
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
  (cores_related : C1 -> C2 -> Prop)
  (handled : AST.external_function -> bool)
  (handled_step : G -> AST.external_function ->
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

Variable upd_globstate: C1 -> C2 -> option C2.
Variable upd_globstate_fun: 
  forall c1 c2 c2' c2'',
  upd_globstate c1 c2 = Some c2' -> 
  upd_globstate c1 c2 = Some c2'' -> 
  c2'=c2''.

Definition extended_coresem :=
  extendCS CS init_extended_core handled upd_globstate handled_step handled_step_handled.

Program Definition extendCCS := Build_CompcertCoreSem G corestate D
  extended_coresem _ _.
Next Obligation.
inversion H; subst; inversion H0; subst.
cut ((c1', m1) = (c1'0, m2)).
inversion 1; subst; auto.
specialize (upd_globstate_fun H2 H10); subst; auto.
eapply csem_corestep_fun; eauto.
apply corestep_not_at_external in H1; rewrite H1 in *; congruence.
apply corestep_not_at_external in H7; rewrite H7 in *; congruence.
rewrite H1 in H6; inversion H6; subst.
destruct (handled_step_det H2 H8) as [H20 [H21 H22]]; subst.
rewrite H12 in H3; inversion H3; subst; auto.
Qed.
Next Obligation.
inversion H; subst.
apply csem_allowed_modifications in H0; auto.
eapply handled_step_allowed_core_modifications; eauto.
Qed.

(* extensions preserve safety *)

Variable ora: Type.
Variable ExtSpec: external_specification mem AST.external_function ora.

Variable INV_PRE: forall ge ef args c2 m (x : ext_spec_type ExtSpec ef) z, 
  ext_spec_pre ExtSpec ef x args c2 m ->
  exists ret, exists c2', exists m', handled_step ge ef args z m ret c2' m'.

Variable INV_POST: forall ge ef args c2 m ret c2' m' x z, 
  ext_spec_pre ExtSpec ef x args z m -> 
  handled_step ge ef args c2 m ret c2' m' ->
  ext_spec_post ExtSpec ef x ret z m'. 

Variable CORE_DIAGRAM_HANDLED: forall ge f args ret c1 c2 m c2' c2'' m' c1',
  cores_related c1 c2 -> 
  at_external CS c1 = Some (f, args) -> 
  handled_step ge f args c2 m ret c2' m' -> 
  after_external' CS upd_globstate ret (c1, c2') = Some (c1', c2'') -> 
  cores_related c1' c2''.

Variable CORE_DIAGRAM_UNHANDLED: forall f args ret c1 c2 c1' c2',
  cores_related c1 c2 -> 
  at_external CS c1 = Some (f, args) -> 
  handled f = false -> 
  after_external' CS upd_globstate ret (c1, c2) = Some (c1', c2') -> 
  cores_related c1' c2'.

Variable upd_after_external1: 
  forall ef l ret c1 c2 c1',
  cores_related c1 c2 -> 
  at_external CS c1 = Some (ef, l) -> 
  after_external CS ret c1 = Some c1' -> 
  exists c2', upd_globstate c1' c2 = Some c2'.

Variable upd_after_external2: 
  forall ge ef l ret c1 c2 c1' c2' m m', 
  cores_related c1 c2 -> 
  at_external CS c1 = Some (ef, l) -> 
  handled_step ge ef l c2 m ret c2' m' -> 
  after_external CS ret c1 = Some c1' -> 
  exists c2'', upd_globstate c1' c2' = Some c2''.

Variable upd_after_corestep: 
  forall ge c1 c2 c1' m m',
  cores_related c1 c2 -> 
  corestep CS ge c1 m c1' m' -> 
  exists c2', 
    upd_globstate c1' c2 = Some c2' /\ 
    cores_related c1' c2'.

Lemma extendCCS_safeN ge (z: ora) (c1: C1) (c2: C2) (m: mem) (n: nat) :
  cores_related c1 c2 -> 
  safeN CS ExtSpec ge n z c1 m -> 
  safeN extendCCS ExtSpec ge n z (c1, c2) m.
Proof.
revert ge c1 c2 z m; induction n; simpl; auto.
intros ge c1 c2 z m H1.
case_eq (at_external CS c1).
destruct p as [ef l].
case_eq (handled ef).
destruct (sim.safely_halted CS ge c1).
intros; elimtype False; auto.
intros H2 H3 [x H4].
assert (H5: ext_spec_evolve ExtSpec z z) by admit. (*evolve must evolve...*)
specialize (H4 z H5).
destruct H4 as [H4 H7].
destruct (INV_PRE ge ef l z m x c2 H4) as [ret [c2' [m' H8]]].
generalize H8 as H8'.
apply INV_POST with (z := z) (x := x) in H8.
destruct (H7 ret m' z H8) as [c1' [H9 H10]]; intros H11.
destruct (upd_after_external2 H1 H3 H11 H9) as [c2'' H12].
exists (c1', c2''). 
exists m'.
assert (H13: after_external' CS upd_globstate ret (c1, c2') = Some (c1', c2'')).
 unfold after_external'. 
 rewrite H9; auto.
 rewrite H12; auto.
split.
eapply step_extend; eauto.
eapply IHn; auto.
eapply CORE_DIAGRAM_HANDLED; eauto.
auto.

intros H2 H3.
destruct (sim.safely_halted CS ge c1).
inversion 1.
intros [x H4].
exists x.
intros z' H5; split.
destruct (H4 z' H5).
auto.
intros ret m' z'' H6.
destruct (H4 z' H5) as [H0 H7].
destruct (H7 _ _ _ H6) as [c1' [H9 H10]].
destruct (upd_after_external1 _ H1 H3 H9) as [c2' H11]. 
exists (c1', c2').
rewrite H9.
rewrite H11.
split; auto.
eapply IHn; eauto.
eapply CORE_DIAGRAM_UNHANDLED with (ret := ret); eauto.
unfold after_external'.
rewrite H9.
rewrite H11.
split; auto.

destruct (sim.safely_halted CS ge c1).
admit. (*let's assume we're never safely halted; HALT is an external 
         function call that never returns*)
intros H2 [c' [m' [H3 H4]]].
destruct (upd_after_corestep _ _ _ _ H1 H3) as [c2' [H5 H6]].
exists (c', c2').
exists m'.
split.
eapply step_core; eauto.
eapply IHn; eauto.
Qed.

(* NOTES: 
-2) preservation of simulation diagrams (probably 3 cases)
-3) define a simple extension with one external function call; show that it satisfies 
properties (1) and (2)
-4) do same for concurrency extension
*)

End compcert_extension.