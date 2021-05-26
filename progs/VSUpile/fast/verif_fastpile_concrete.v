Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import fastpile.
Require Import spec_stdlib.
Require Import spec_fastpile_concrete.

Instance FPileConcCompSpecs : compspecs. make_compspecs prog. Defined.

Section FastpileConcrete_VSU.
Variable M: MallocFreeAPD.

Definition crep (s: Z) (p: val) : mpred :=
  EX s':Z, !! (0 <= s /\ 0 <= s' <= Int.max_signed /\
                 (s <= Int.max_signed -> s'=s)) &&
  data_at Ews tpile (Vint (Int.repr s')) p.

Definition cfreeable (p: val) :=
   malloc_token M Ews tpile p.

Lemma crep_local_facts:
  forall s p, crep s p |-- !! isptr p.
Proof.
intros.
unfold crep.
Intros s'.
entailer!.
Qed.

#[export] Hint Resolve crep_local_facts : saturate_local.

Lemma crep_valid_pointer:
  forall s p, crep s p |-- valid_pointer p.
Proof. 
 intros.
 unfold crep. Intros s'.
 auto with valid_pointer.
Qed.
#[export] Hint Resolve crep_valid_pointer : valid_pointer.

Definition FASTPILECONC: FastpileConcreteAPD :=
  Build_FastpileConcreteAPD crep crep_local_facts crep_valid_pointer cfreeable.

Definition surely_malloc_spec :=
  DECLARE _surely_malloc
   WITH t:type, gv: globals
   PRE [ size_t ]
       PROP (0 <= sizeof t <= Ptrofs.max_unsigned;
                complete_legal_cosu_type t = true;
                natural_aligned natural_alignment t = true)
       PARAMS (Vptrofs (Ptrofs.repr (sizeof t))) GLOBALS (gv)
       SEP (mem_mgr M gv)
    POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP (mem_mgr M gv; malloc_token M Ews t p * data_at_ Ews t p).

  Definition FastpileConc_ASI: funspecs := FastpileConcreteASI M FASTPILECONC.

  Definition fastpileconc_imported_specs:funspecs := MallocFreeASI M.

  Definition fastpileconc_internal_specs: funspecs := surely_malloc_spec::FastpileConc_ASI.

  Definition FastpileConcVprog: varspecs. mk_varspecs prog. Defined.
  Definition FastpileConcGprog: funspecs := fastpileconc_imported_specs ++ fastpileconc_internal_specs.

Lemma body_Pile_new: semax_body FastpileConcVprog FastpileConcGprog f_Pile_new (Pile_new_spec M FASTPILECONC).
Proof.
start_function.
forward_call (tpile, gv).
split3; simpl; auto; computable.
Intros p.
forward.
forward.
simpl countrep. unfold crep.
simpl count_freeable. unfold cfreeable.
Exists p 0.
entailer!.
Qed.

Lemma body_Pile_add: semax_body FastpileConcVprog FastpileConcGprog f_Pile_add (Pile_add_spec M FASTPILECONC).
Proof.
start_function.
simpl countrep. unfold crep.
Intros s'.
forward.
forward_if (temp _t'1 (if zle 0 n then if zle n (Int.max_signed-s') then Vtrue else Vfalse else Vfalse)).
-
forward.
entailer!.
destruct (zle 0 n); [ | lia].
destruct (zle _ _).
unfold Int.lt. rewrite zlt_false.
reflexivity.
normalize. rep_lia.
unfold Int.lt. rewrite zlt_true.
reflexivity.
normalize.
rep_lia.
-
forward.
entailer!.
-
destruct (zle 0 n); try lia.
forward_if (PROP()LOCAL (temp _pp p)
   SEP(crep (n+s) p; mem_mgr M gv)).
+
if_tac in H3; inv H3.
forward.
unfold crep. Exists (s'+n).
entailer!.
+
forward.
unfold crep.
if_tac in H3; inv H3.
Exists s'. entailer!.
+
forward.
Qed.

Lemma body_Pile_count: semax_body FastpileConcVprog FastpileConcGprog f_Pile_count (Pile_count_spec FASTPILECONC).
Proof.
start_function.
simpl countrep. unfold crep.
Intros s'.
forward.
forward.
simpl countrep. unfold crep.
Exists s' s'.
entailer!.
Qed.

Lemma body_Pile_free: semax_body FastpileConcVprog FastpileConcGprog f_Pile_free (Pile_free_spec M FASTPILECONC).
Proof.
start_function.
simpl countrep. unfold crep.
simpl count_freeable. unfold cfreeable. Intros s'.
assert_PROP (p<>nullval) by entailer!. 
forward_call (free_spec_sub M (Tstruct _pile noattr))  (p, gv).
rewrite if_false by auto.
cancel.
forward.
Qed.

(*Same statement and proof as verif_pile. Indeed, the C files have the same code duplication...*)
(*Statement and proof also shared with verif_fastpile.v*)
Lemma body_surely_malloc: semax_body FastpileConcVprog FastpileConcGprog f_surely_malloc surely_malloc_spec.
Proof.
start_function.
forward_call (malloc_spec_sub M t) gv.
Intros p.
if_tac.
{ subst.
  forward_if False.
  - forward_call 1. contradiction.
  - congruence. }
forward_if True.
+ contradiction.
+ forward. entailer!.
+ forward. Exists p. entailer!.
Qed.

  Definition FastpileVSU: @VSU NullExtension.Espec
      nil fastpileconc_imported_specs ltac:(QPprog prog) FastpileConc_ASI emp.
  Proof. 
    mkVSU prog fastpileconc_internal_specs.
    + solve_SF_internal body_surely_malloc.
    + solve_SF_internal body_Pile_count.
    + solve_SF_internal body_Pile_add.
    + solve_SF_internal body_Pile_new.
    + solve_SF_internal body_Pile_free.
  Qed.

End FastpileConcrete_VSU.

