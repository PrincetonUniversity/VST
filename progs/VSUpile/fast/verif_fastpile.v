Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import fastpile.
Require Import spec_stdlib.
Require Import spec_fastpile.
Require Import spec_fastpile_private.

Section Fastpile_VSU.
Variable M: MemMGRPredicates.

Lemma fastprep_local_facts:
  forall sigma p,
   fastprep sigma p |-- !! (isptr p /\ Forall (Z.le 0) sigma).
Proof.
intros.
unfold fastprep.
Intros q.
entailer!.
Qed.

Hint Resolve fastprep_local_facts : saturate_local.

Lemma fastprep_valid_pointer:
  forall sigma p,
   fastprep sigma p |-- valid_pointer p.
Proof. 
 intros.
 unfold fastprep. Intros x.
 entailer!; auto with valid_pointer.
Qed.
Hint Resolve fastprep_valid_pointer : valid_pointer.

Definition pfreeable (p: val) : mpred :=
            malloc_token M Ews tpile p.

Definition FASTPILE: PilePredicates := Build_PilePredicates fastprep
              fastprep_local_facts fastprep_valid_pointer pfreeable.

Definition FASTPILEPRIV: FastpilePrivatePredicates := Build_FastpilePrivatePredicates FASTPILE (eq_refl _).

Definition surely_malloc_spec :=
  DECLARE _surely_malloc
   WITH t:type, gv: globals
   PRE [ tuint ]
       PROP (0 <= sizeof t <= Int.max_unsigned;
                complete_legal_cosu_type t = true;
                natural_aligned natural_alignment t = true)
       (LAMBDAx [gv] [Vint (Int.repr (sizeof t))]
       (SEP (mem_mgr M gv)))
    POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP (mem_mgr M gv; malloc_token M Ews t p * data_at_ Ews t p).

  Definition Fastpile_ASI: funspecs := PileASI M FASTPILE.

  Definition fastpile_imported_specs:funspecs := (*spec_stdlib.specs.*)MMASI M.

  Definition fastpile_internal_specs: funspecs := surely_malloc_spec::Fastpile_ASI.

  Definition FastpileVprog: varspecs. mk_varspecs prog. Defined.
  Definition FastpileGprog: funspecs := fastpile_imported_specs ++ fastpile_internal_specs.

Lemma body_Pile_new: semax_body FastpileVprog FastpileGprog f_Pile_new (Pile_new_spec M FASTPILE).
Proof.
start_function.
forward_call (tpile, gv).
split3; simpl; auto; computable.
Intros p.
forward.
forward.
simpl pilerep; unfold fastprep. 
simpl pile_freeable. unfold pfreeable.
Exists p 0.
entailer!.
Qed.

Lemma sumlist_nonneg: forall sigma, 
  Forall (Z.le 0) sigma -> 0 <= sumlist sigma.
Proof.
intros.
induction sigma; simpl. omega. inv H.
apply IHsigma in H3; omega.
Qed.

Lemma body_Pile_add: semax_body FastpileVprog FastpileGprog f_Pile_add (Pile_add_spec M FASTPILE).
Proof.
start_function.
simpl pilerep. unfold fastprep.
Intros s.
forward.
forward_if (temp _t'1 (if zle 0 n then if zle n (Int.max_signed-s) then Vtrue else Vfalse else Vfalse)).
forward.
entailer!.
destruct (zle 0 n); [ | omega].
destruct (zle _ _).
unfold Int.lt. rewrite zlt_false.
reflexivity.
normalize. rep_omega.
unfold Int.lt. rewrite zlt_true.
reflexivity.
normalize.
rep_omega.
forward.
entailer!.
destruct (zle 0 n); try omega. clear l.
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
constructor; auto. omega.
simpl. intros.
rewrite H2.
omega.
apply sumlist_nonneg in H1; omega.
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
omega.
simpl.
apply sumlist_nonneg in H1; omega.
Qed.

Lemma body_Pile_count: semax_body FastpileVprog FastpileGprog f_Pile_count (Pile_count_spec FASTPILE).
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

Lemma body_Pile_free: semax_body FastpileVprog FastpileGprog f_Pile_free (Pile_free_spec M FASTPILE).
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

(*Same pstatement and proof as verif_pile. Indeed, the C files have the same code duplication...*)
Lemma body_surely_malloc: semax_body FastpileVprog FastpileGprog f_surely_malloc surely_malloc_spec.
Proof.
start_function.
forward_call (malloc_spec_sub M t) gv.
Intros p.
if_tac.
{ subst.
  forward_if False.
  - forward_call 1. contradiction.
  - inv H2. }
forward_if True.
+ contradiction.
+ forward. entailer!.
+ forward. Exists p. entailer!.
Qed.

  Definition FastpileComponent: @Component NullExtension.Espec FastpileVprog _ 
      nil fastpile_imported_specs prog Fastpile_ASI fastpile_internal_specs.
  Proof. 
    mkComponent.
    + solve_SF_internal body_surely_malloc.
    + solve_SF_internal body_Pile_new.
    + solve_SF_internal body_Pile_add.
    + solve_SF_internal body_Pile_count.
    + solve_SF_internal body_Pile_free.
  Qed.

  Definition FastpileVSU: @VSU NullExtension.Espec FastpileVprog _ 
      nil fastpile_imported_specs prog Fastpile_ASI.
  Proof. eexists; apply FastpileComponent. Qed.

  Definition FastpilePrivateComponent: @Component NullExtension.Espec FastpileVprog _ 
      nil fastpile_imported_specs prog (FastpilePrivateASI M FASTPILEPRIV) fastpile_internal_specs.
  Proof. 
    mkComponent.
    + solve_SF_internal body_surely_malloc.
    + solve_SF_internal body_Pile_new.
    + solve_SF_internal body_Pile_add.
    + solve_SF_internal body_Pile_count.
    + solve_SF_internal body_Pile_free.
  Qed.

Definition FastpilePrivateVSU: @VSU NullExtension.Espec FastpileVprog _ 
      nil fastpile_imported_specs prog (FastpilePrivateASI M FASTPILEPRIV).
  Proof. eexists; apply FastpileComponent. Qed.
End Fastpile_VSU.
