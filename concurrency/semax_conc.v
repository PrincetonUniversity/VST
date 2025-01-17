Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.SeparationLogic.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
Require Import compcert.cfrontend.Ctypes.
Require Import VST.veric.expr.
Require Import VST.concurrency.semax_conc_pred.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.field_at.
Import Clightdefs.
Import String.
Open Scope funspec_scope.

Definition spawned_funtype := Tfunction (tptr tvoid :: nil) tint cc_default.

Section mpred.

Context `{!VSTGS OK_ty Σ}.

(*+ Specification of each concurrent primitive *)

(* To enable joinable threads, the postcondition would be [tptr tthread]
with a type [tthread] related to the postcondition through a [thread]
predicate in the logic.  The [join] would then also be implemented
using the oracle, as [acquire] is.  The postcondition would be [match
PrePost with existT ty (w, pre, post) => thread th (post w b)
end] *)

(* If we want the spawned function to itself have a higher-order or dependent spec,
   we probably need the DependentType machinery after all. *)
Definition spawn_arg_type := ProdType (ConstType (val * val)) (SigType Type (fun A => ProdType (ProdType
  (DiscreteFunType A (ConstType globals)) (ConstType A))
  (DiscreteFunType A (DiscreteFunType val Mpred)))).

Local Unset Program Cases.

Program Definition spawn_pre : dtfr (ArgsTT spawn_arg_type) := λne x,
  let '(f, b, fs) := x in
  PROP (tc_val (tptr Tvoid) b)
    PARAMS (f; b)
    GLOBALS (let 'existT A ((gv, w), _) := fs in gv w)
    SEP (let 'existT A ((gv, w), pre) := fs in
         (func_ptr
           (WITH y : val, x : A
             PRE [ tptr tvoid ]
               PROP ()
               PARAMS (y)
               GLOBALS (gv x)
               SEP (pre x y)
             POST [ tint ]
               PROP  ()
               RETURN (Vint Int.zero) (* spawned functions must return 0 for now *)
               SEP   ())
           f);
         let 'existT A ((gv, w), pre) := fs in (*valid_pointer b ∧*) pre w b) (* Do we need the valid_pointer here? *).
Next Obligation.
Proof.
  intros ? ((f, b), (?, ((gv, ?), pre))) ((?, ?), (?, ((?, w), ?))) ([=] & ? & Hfs) rho; simpl in *; subst; simpl in *.
  destruct Hfs as ((Hgv & [=]) & Hpre); simpl in *; subst.
  rewrite (Hgv _).
  do 6 f_equiv.
  - apply func_ptr_si_nonexpansive; last done.
    split; last split; [done..|].
    exists eq_refl; simpl.
    split3; intros (?, ?); simpl; try done.
    intros ?; rewrite Hgv (Hpre _ _) //.
  - rewrite (Hpre _ _) //.
Defined.

Program Definition spawn_post : @dtfr Σ (AssertTT spawn_arg_type) := λne x,
  let '(f, b, fs) := x in PROP () LOCAL () SEP ().
Next Obligation.
Proof.
  intros ? ((f, b), ?) ((?, ?), ?) ?.
  reflexivity.
Qed.

Definition spawn_spec := mk_funspec ([tptr spawned_funtype; tptr tvoid], tvoid) cc_default
  spawn_arg_type (λne _, ⊤) spawn_pre spawn_post.

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

#[export] Instance concurrent_ext_spec (cs : compspecs) (ext_link : string -> ident) : ext_spec OK_ty :=
  add_funspecs_rec OK_ty
    ext_link
    (void_spec OK_ty)
    (concurrent_specs cs ext_link).

End mpred.
