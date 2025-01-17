Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require VST.floyd.library. (*for body_lemma_of_funspec *)
Require Import VSTlib.SC_atomics_extern.
Require Import VSTlib.spec_SC_atomics.
(*
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
*)

Section AtomicsASI.
Context `{VOK: !VSTGS OK_ty Σ}.

#[export] Declare Instance M: AtomicsAPD.

Local Fixpoint get_def [T] (al: list (ident * T)) (i: ident) : option T :=
 match al with 
 | nil => None
 | (j,x)::r => if ident_eq i j then Some x else get_def r i
 end.

Local Definition get_extfun (i: ident) : external_function :=
  match get_def SC_atomics_extern.global_definitions i with
  | Some (Gfun (External x _ _ _)) => x
  | _ => EF_annot 1%positive "error: extfun not found" nil
  end.


Parameter body_make_atomic: 
 forall {Espec: ext_spec OK_ty} ,
   VST.floyd.library.body_lemma_of_funspec (get_extfun _make_atomic)
(*        (EF_external "make_atomic" (mksignature (Xint :: nil) Xptr cc_default))*)
       make_atomic_spec. 

Parameter body_make_atomic_ptr:
 forall {Espec: ext_spec OK_ty}  ,
   VST.floyd.library.body_lemma_of_funspec (get_extfun _make_atomic_ptr)
(*       (EF_external "make_atomic_ptr"
                   (mksignature (Xptr :: nil) Xptr cc_default))*)
       make_atomic_ptr_spec.

Parameter body_free_atomic: 
 forall {Espec: ext_spec OK_ty}  ,
   VST.floyd.library.body_lemma_of_funspec (get_extfun _free_atomic)
(*        (EF_external "free_atomic"
                   (mksignature (Xptr :: nil) Xvoid cc_default))*)
       free_atomic_int_spec.

Parameter body_free_atomic_ptr: 
 forall {Espec: ext_spec OK_ty}  ,
   VST.floyd.library.body_lemma_of_funspec (get_extfun _free_atomic_ptr)
(*        (EF_external "free_atomic_ptr"
                   (mksignature (Xptr :: nil) Xvoid cc_default))*)
       free_atomic_ptr_spec.

Parameter body_atom_load: 
 forall {Espec: ext_spec OK_ty}  ,
   VST.floyd.library.body_lemma_of_funspec (get_extfun _atom_load)
(*        (EF_external "atom_load"
                   (mksignature (Xptr :: nil) Xint cc_default))*)
       atomic_load_spec.

Parameter body_atom_store: 
 forall {Espec: ext_spec OK_ty}  ,
   VST.floyd.library.body_lemma_of_funspec (get_extfun _atom_store)
(*        (EF_external "atom_store"
                   (mksignature (Xptr :: Xint :: nil) Xvoid cc_default))
*)
       atomic_store_spec.

Parameter body_atom_CAS: 
 forall {Espec: ext_spec OK_ty}  ,
   VST.floyd.library.body_lemma_of_funspec (get_extfun _atom_CAS)
(*        (EF_external "atom_CAS"
                   (mksignature (Xptr :: Xptr :: Xint :: nil)
                     Xint cc_default))
*)
       atomic_CAS_spec.


Parameter body_atom_exchange: 
 forall {Espec: ext_spec OK_ty}  ,
   VST.floyd.library.body_lemma_of_funspec (get_extfun _atom_exchange)
(*        (EF_external "atom_exchange"
                   (mksignature (Xptr :: Xint :: nil) Xint
                     cc_default))
*)
       atomic_exchange_spec.

Definition SC_atomics_placeholder_spec : ident * @funspec Σ :=
 DECLARE _SC_atomics_placeholder
 WITH u: unit
 PRE [ ]
   PROP (False) PARAMS () GLOBALS () SEP()
 POST [ tint ]
   PROP() LOCAL() SEP().

  Definition SCA_ASI: funspecs := AtomicsASI.

  Definition SCA_imported_specs: @funspecs Σ :=  nil.

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
(*
Ltac check_mpreds2 R ::= (* Patch for https://github.com/PrincetonUniversity/VST/issues/638 *)
 lazymatch R with
 | @sepcon mpred _ _ ?a ?b => check_mpreds2 a; check_mpreds2 b
 | _ => match type of R with ?t =>
                          first [constr_eq t mpred
                                 | fail 4 "The conjunct" R "has type" t "but should have type mpred; these two types may be convertible but they are not identical"]
                     end
 | nil => idtac
 end.
*)
(*#[local] Existing Instance NullExtension.Espec.  (* FIXME *)
*)

Ltac solve_SF_external B ::=
  first [ split3;
            [ reflexivity 
            | reflexivity 
            | split3;
                [ reflexivity
                | reflexivity
                | split3;
                   [ left; trivial
                   | clear; intros ? ? ?; cbv [ofe_mor_car]; 
                     try solve [entailer!]; try apply TT_right;
                     repeat match goal with |- (let (y, z) := ?x in _) _ ∧ _ ⊢ _ =>
                                     destruct x as [y z]
                     end
                    | split; [ try apply B | eexists; split; cbv; reflexivity ]
            ] ] ]
        | idtac ].

Definition SCAVSU `{Espec: ext_spec OK_ty}: VSU SCA_E SCA_imported_specs ltac:(QPprog prog) SCA_ASI (fun _ => emp).
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
    - solve_SF_external body_atom_CAS.
        simpl. admit.
    - solve_SF_external body_atom_exchange.
        simpl. admit.
Admitted.  (* all these admits are undoubtedly provable; see for example 
                            Lemma RETURN_tc_option_val_float  in verif_math.v *)

End AtomicsASI.
