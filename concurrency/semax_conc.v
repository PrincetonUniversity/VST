Require Import VST.veric.juicy_extspec.
Require Import VST.veric.SeparationLogic.
Require Import compcert.cfrontend.Ctypes.
Require Import VST.veric.expr.
Require Import VST.concurrency.semax_conc_pred.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.field_at.
Import Clightdefs.
Import String.
Open Scope funspec_scope.

Definition spawned_funtype := Tfunction (Tcons (tptr tvoid) Tnil) tint cc_default.

Section mpred.

Context `{!heapGS Σ}.

(*+ Specification of each concurrent primitive *)

(* To enable joinable threads, the postcondition would be [tptr tthread]
with a type [tthread] related to the postcondition through a [thread]
predicate in the logic.  The [join] would then also be implemented
using the oracle, as [acquire] is.  The postcondition would be [match
PrePost with existT ty (w, pre, post) => thread th (post w b)
end] *)

Definition spawn_arg_type := ProdType (ConstType (val * val)) (SigType Type (fun A => ProdType (ProdType
  (ArrowType (ConstType A) (ConstType globals)) (ConstType A))
  (ArrowType (ConstType A) (ArrowType (ConstType val) Mpred)))).

Program Definition spawn_spec :=
  TYPE spawn_arg_type WITH f : _, b : _, fs : _
  PRE [ tptr spawned_funtype, tptr tvoid ]
    PROP (tc_val (tptr Tvoid) b)
    PARAMS (f; b)
    GLOBALS (let 'existT _ ((gv, w), _) := fs in gv w)
    SEP (let 'existT _ ((gv, w), pre) := fs in
         (func_ptr
           (WITH y : val, x : _
             PRE [ tptr tvoid ]
               PROP ()
               PARAMS (y)
               GLOBALS (gv w)
               SEP (pre x y)
             POST [ tptr tvoid ]
               PROP  ()
               LOCAL ()
               SEP   ())
           f);
         let 'existT _ ((gv, w), pre) := fs in valid_pointer b ∧ pre w b) (* Do we need the valid_pointer here? *)
  POST [ tvoid ]
    PROP ()
    RETURN (Vint Int.zero) (* spawned functions must return 0 for now *)
    SEP (). (* here's where we'd put a join condition *)
Next Obligation.
Proof.
  intros ? ((f, b), (?, ((gv, w), pre))) ((?, ?), (?, ((?, ?), ?))) ([=] & ? & Hfs) rho; simpl in *; subst; simpl in *.
  destruct Hfs as ((Hgv & [=]) & Hpre); simpl in *; subst.
  rewrite Hgv.
  do 6 f_equiv.
  - apply func_ptr_si_nonexpansive; last done.
    split3; last split; [done..|].
    exists eq_refl; simpl.
    split; intros (?, ?); simpl; last done.
    intros ?; rewrite (Hpre _ _) //.
  - rewrite (Hpre _ _) //.
Qed.
Next Obligation.
Proof.
  intros ? ((f, b), ?) ((?, ?), ?) ?.
  reflexivity.
Qed.

(*+ Adding the specifications to a void ext_spec *)

(*Definition concurrent_simple_specs (cs : compspecs) (ext_link : string -> ident) :=
  (ext_link "acquire"%string, acquire_spec) ::
  (ext_link "release"%string, release_spec) ::
  nil.

Definition concurrent_simple_ext_spec Z (cs : compspecs) (ext_link : string -> ident) :=
  add_funspecs_rec
    ext_link
    (ok_void_spec Z).(@OK_ty)
    (ok_void_spec Z).(@OK_spec)
    (concurrent_simple_specs cs ext_link).

Definition Concurrent_Simple_Espec Z cs ext_link :=
  Build_OracleKind
    Z
    (concurrent_simple_ext_spec Z cs ext_link).*)

Definition concurrent_specs (cs : compspecs) (ext_link : string -> ident) :=
  (ext_link "spawn"%string, spawn_spec) ::
  nil.

Context (Z : Type) `{!externalGS Z Σ}.

Definition concurrent_ext_spec (cs : compspecs) (ext_link : string -> ident) :=
  add_funspecs_rec Z
    ext_link
    (ok_void_spec Z).(OK_spec)
    (concurrent_specs cs ext_link).

Definition Concurrent_Espec cs ext_link :=
  Build_OracleKind
    Z
    (concurrent_ext_spec cs ext_link).

End mpred.
