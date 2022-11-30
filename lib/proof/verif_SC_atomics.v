Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require VST.floyd.library. (*for body_lemma_of_funspec *)
Require Import VSTlib.SC_atomics_extern.
Require Import VSTlib.spec_SC_atomics.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

#[export] Declare Instance M: AtomicsAPD.

Parameter body_make_atomic: 
 forall {Espec: OracleKind} ,
   VST.floyd.library.body_lemma_of_funspec 
        (EF_external "make_atomic" (mksignature (AST.Tint :: nil) AST.Tlong cc_default))
       make_atomic_spec. 

Parameter body_make_atomic_ptr:
 forall {Espec: OracleKind}  ,
   VST.floyd.library.body_lemma_of_funspec 
       (EF_external "make_atomic_ptr"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
       make_atomic_ptr_spec.

Parameter body_free_atomic: 
 forall {Espec: OracleKind}  ,
   VST.floyd.library.body_lemma_of_funspec 
        (EF_external "free_atomic"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
       free_atomic_int_spec.

Parameter body_free_atomic_ptr: 
 forall {Espec: OracleKind}  ,
   VST.floyd.library.body_lemma_of_funspec 
        (EF_external "free_atomic_ptr"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
       free_atomic_ptr_spec.

Parameter body_atom_load: 
 forall {Espec: OracleKind}  ,
   VST.floyd.library.body_lemma_of_funspec 
        (EF_external "atom_load"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
       atomic_load_spec.

Parameter body_atom_store: 
 forall {Espec: OracleKind}  ,
   VST.floyd.library.body_lemma_of_funspec 
        (EF_external "atom_store"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid cc_default))
       atomic_store_spec.

Parameter body_atom_CAS: 
 forall {Espec: OracleKind}  ,
   VST.floyd.library.body_lemma_of_funspec 
        (EF_external "atom_CAS"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tint :: nil)
                     AST.Tint cc_default))
       atomic_CAS_spec.


Parameter body_atom_exchange: 
 forall {Espec: OracleKind}  ,
   VST.floyd.library.body_lemma_of_funspec 
        (EF_external "atom_exchange"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tint
                     cc_default))
       atomic_exchange_spec.

Definition SC_atomics_placeholder_spec :=
 DECLARE _SC_atomics_placeholder
 WITH u: unit
 PRE [ ]
   PROP (False) PARAMS () GLOBALS () SEP()
 POST [ tint ]
   PROP() LOCAL() SEP().

  Definition SCA_ASI: funspecs := AtomicsASI.

  Definition SCA_imported_specs:funspecs :=  nil.

  Definition SCA_internal_specs: funspecs := SC_atomics_placeholder_spec::SCA_ASI.

  Definition SCAVprog : varspecs. mk_varspecs prog. Defined.
  Definition SCAGprog: funspecs := SCA_imported_specs ++ SCA_internal_specs.
(*
  Lemma SCA_Init: VSU_initializer prog (mem_mgr M).
  Proof. InitGPred_tac. apply mem_mgr_rep. Qed.
*)

Lemma body_SC_atomics_placeholder: semax_body SCAVprog SCAGprog f_SC_atomics_placeholder SC_atomics_placeholder_spec.
Proof.
start_function.
contradiction.
Qed.

Definition SCA_E : funspecs := SCA_ASI.

Ltac check_mpreds2 R ::= (* Patch for https://github.com/PrincetonUniversity/VST/issues/638 *)
 lazymatch R with
 | @sepcon mpred _ _ ?a ?b => check_mpreds2 a; check_mpreds2 b
 | _ => match type of R with ?t =>
                          first [constr_eq t mpred
                                 | fail 4 "The conjunct" R "has type" t "but should have type mpred; these two types may be convertible but they are not identical"]
                     end
 | nil => idtac
 end.

#[local] Existing Instance NullExtension.Espec.  (* FIXME *)

Definition SCAVSU: VSU SCA_E SCA_imported_specs ltac:(QPprog prog) SCA_ASI emp.
  Proof. 
    mkVSU prog SCA_internal_specs.
    - solve_SF_internal body_SC_atomics_placeholder.
    - solve_SF_external body_make_atomic.
       admit.
    - solve_SF_external body_make_atomic_ptr.
       admit.
    - solve_SF_external body_free_atomic_ptr.
    - solve_SF_external body_free_atomic.
    - solve_SF_external body_atom_load.
        simpl. admit.
    - solve_SF_external body_atom_store.
        simpl. admit.
    - solve_SF_external body_atom_CAS.
        simpl. admit.
    - solve_SF_external body_atom_exchange.
        simpl. admit.
Admitted.  (* all these admits are undoubtedly provable; see for example 
                            Lemma RETURN_tc_option_val_float  in verif_math.v *)

