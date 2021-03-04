Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import fastpile.
Require Import spec_stdlib.
Require Import spec_fastpile.
Require Import spec_fastpile_private.
Require Import PileModel.

Section Pile_VSU.
Variable M: MallocFreeAPD.

Lemma fastprep_local_facts:
  forall sigma p,
   fastprep sigma p |-- !! (isptr p /\ Forall (Z.le 0) sigma).
Proof.
intros.
unfold fastprep.
Intros q.
entailer!.
Qed.

Local Hint Resolve fastprep_local_facts : saturate_local.

Lemma fastprep_valid_pointer:
  forall sigma p,
   fastprep sigma p |-- valid_pointer p.
Proof. 
 intros.
 unfold fastprep. Intros x.
 entailer!; auto with valid_pointer.
Qed.
Local Hint Resolve fastprep_valid_pointer : valid_pointer.

Definition pfreeable (p: val) : mpred :=
            malloc_token M Ews tpile p.

Definition PILE: PileAPD := Build_PileAPD fastprep
              fastprep_local_facts fastprep_valid_pointer pfreeable.

Definition PILEPRIV: FastpilePrivateAPD := Build_FastpilePrivateAPD PILE (eq_refl _).

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

Definition Pile_ASI: funspecs := PileASI M PILE.

Definition pile_imported_specs:funspecs := MallocFreeASI M.

Definition pile_internal_specs: funspecs := surely_malloc_spec::Pile_ASI.

Definition PileVprog: varspecs. mk_varspecs prog. Defined.
Definition PileGprog: funspecs := pile_imported_specs ++ pile_internal_specs.

Lemma body_Pile_new: semax_body PileVprog PileGprog f_Pile_new (Pile_new_spec M PILE).
Proof.
start_function.
forward_call (tpile, gv).
Intros p.
forward.
forward.
simpl pilerep; unfold fastprep. 
simpl pile_freeable. unfold pfreeable.
Exists p 0.
entailer!.
Qed.

Lemma body_Pile_add: semax_body PileVprog PileGprog f_Pile_add (Pile_add_spec M PILE).
Proof.
start_function.
simpl pilerep. unfold fastprep.
Intros s.
forward.
forward_if (temp _t'1 (if zle 0 n then if zle n (Int.max_signed-s) then Vtrue else Vfalse else Vfalse)).
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
forward.
entailer!.
destruct (zle 0 n); try lia. clear l.
destruct (zle n (Int.max_signed - s)).
-
forward_if (PROP()LOCAL (temp _pp p)
   SEP(data_at Ews tpile (Vint (Int.repr (s+n))) p;
         mem_mgr M gv)).
forward.
entailer!.
inversion H3.
forward.
simpl pilerep. unfold fastprep.
Exists (s+n).
entailer!.
split.
constructor; auto. lia.
simpl. intros.
rewrite H2.
lia.
apply sumlist_nonneg in H1; lia.
-
forward_if (PROP()LOCAL (temp _pp p)
   SEP(data_at Ews tpile (Vint (Int.repr s)) p;
         mem_mgr M gv)).
contradiction H3'; auto.
forward.
entailer!.
forward.
simpl pilerep. unfold fastprep.
Exists s.
entailer!.
split.
constructor; auto.
lia.
simpl.
apply sumlist_nonneg in H1; lia.
Qed.

Lemma body_Pile_count: semax_body PileVprog PileGprog f_Pile_count (Pile_count_spec PILE).
Proof.
start_function.
simpl pilerep; unfold fastprep. Intros s.
forward.
forward.
entailer!.
rewrite H2; auto.
simpl pilerep; unfold fastprep.
Exists s.
entailer!.
Qed.

Lemma body_Pile_free: semax_body PileVprog PileGprog f_Pile_free (Pile_free_spec M PILE).
Proof.
start_function.
simpl pilerep; unfold fastprep. 
simpl pile_freeable; unfold pfreeable. Intros s.
assert_PROP (p<>nullval) by entailer!.
forward_call (free_spec_sub M (Tstruct _pile noattr))  (p, gv).
rewrite if_false by auto.
cancel.
forward.
Qed.

Lemma body_surely_malloc: semax_body PileVprog PileGprog f_surely_malloc surely_malloc_spec.
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

  Definition PileVSU: @VSU NullExtension.Espec
      nil pile_imported_specs ltac:(QPprog prog) Pile_ASI emp.
  Proof. 
    mkVSU prog pile_internal_specs.
    + solve_SF_internal body_surely_malloc.
    + solve_SF_internal body_Pile_new.
    + solve_SF_internal body_Pile_add.
    + solve_SF_internal body_Pile_count.
    + solve_SF_internal body_Pile_free.
  Qed.

  Definition PilePrivateVSU: @VSU NullExtension.Espec
      nil pile_imported_specs ltac:(QPprog prog) (FastpilePrivateASI M PILEPRIV) emp.
  Proof. 
    mkVSU prog pile_internal_specs.
    + solve_SF_internal body_surely_malloc.
    + solve_SF_internal body_Pile_new.
    + solve_SF_internal body_Pile_add.
    + solve_SF_internal body_Pile_count.
    + solve_SF_internal body_Pile_free.
  Qed.

End Pile_VSU.

