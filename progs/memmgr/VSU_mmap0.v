Require Import VST.floyd.proofauto.
Require Import mmap0.
Require Import ASI_mmap0.
Require Import VST.floyd.VSU.

Local Instance CompSpecs : compspecs. make_compspecs prog. Defined. 

Definition MM0_Vprog : varspecs. mk_varspecs prog. Defined.

Definition placeholder_spec :=
 DECLARE _mmap0_placeholder
 WITH u: unit
 PRE [ ]
   PROP (False) PARAMS() GLOBALS() SEP()
 POST [ tint ]
   PROP() LOCAL() SEP().

Definition MM0_internal_specs: funspecs := [mmap0_spec _mmap0; placeholder_spec].

Definition MM0_Imports:funspecs := nil.

Definition SYS: funspecs := [munmap_spec _munmap(*once mmap0 can be veried, we should should add  mmap_spec here*)] .

Definition MM0_Gprog:funspecs := MM0_Imports ++ SYS++MM0_internal_specs.

Lemma body_placeholder: semax_body MM0_Vprog MM0_Gprog f_mmap0_placeholder placeholder_spec.
Proof.
start_function.
contradiction.
Qed.

(*See explanantion in AppelNaumann's paper, and in mmap0.c*)
Parameter body_mmap0: semax_body MM0_Vprog MM0_Gprog f_mmap0 (mmap0_spec _mmap0).

Require Import VST.floyd.library. (*for body_lemma_of_funspec *)
Parameter body_munmap:
 forall (*{Espec: OracleKind}*) {cs: compspecs},
 @body_lemma_of_funspec NullExtension.Espec 
    (EF_external "munmap"
      (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default))
    (snd (munmap_spec _munmap)).

Definition MM0_VSU: @VSU NullExtension.Espec
           SYS nil ltac:(QPprog prog) (Mmap0_ASI _mmap0 _munmap) emp.
 Proof. 
    mkVSU prog (SYS++MM0_internal_specs).
  + (*external: munmap*)
      clear; solve_SF_external body_munmap. simpl. Intros res.
(*      destruct x. clear z v.
      simpl; Intros res.*)
      destruct ret; simpl in H; [ simpl | try contradiction].
      - red in H.
        destruct v; try contradiction; simpl. 
        2: apply prop_right; trivial.
        all: unfold PROPx, LOCALx, SEPx; simpl; unfold local, liftx; simpl; unfold lift1, lift, eval_id; simpl; Intros; try congruence.
      - unfold PROPx, LOCALx, SEPx; simpl; unfold local, liftx; simpl; unfold lift1, lift, eval_id; simpl; Intros; try congruence.
  + solve_SF_internal body_mmap0.
  + solve_SF_internal body_placeholder.
  Qed.