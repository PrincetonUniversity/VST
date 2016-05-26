Require Import msl.rmaps.
Require Import msl.msl_standard.
Require Import msl.seplog.
Require Import veric.base.
Require Import veric.compcert_rmaps.
Require Import veric.juicy_mem.
Require Import veric.juicy_mem_lemmas.
Require Import veric.juicy_mem_ops.
Require Import veric.juicy_extspec.
Require Import veric.tycontext.
Require Import veric.expr2.
Require Import veric.semax.
Require Import veric.semax_call.
Require Import sepcomp.extspec.
Require Import floyd.proofauto.

(* Variables to be instantiated once the program is known. *)
Definition _f := 1%positive.      (* alpha-convertible *)
Definition _args := 2%positive.   (* alpha-convertible *)
Definition _lock := 1%positive.   (* alpha-convertible *)
Definition _lock_t := 2%positive. (* 2 is the number given by
clightgen when threads.h is included first *)

Variable voidstar_funtype : type.
Definition tlock := Tstruct _lock_t noattr.
(* Notation tlock := tuint (only parsing). *)

Axiom lock_inv : share -> val -> mpred -> mpred.

Axiom lock_inv_share_join : forall sh1 sh2 sh v R, sepalg.join sh1 sh2 sh ->
  (lock_inv sh1 v R * lock_inv sh2 v R = lock_inv sh v R)%logic.

Axiom lock_inv_isptr : forall sh v R, (`(lock_inv sh v R) |-- !!(isptr v))%logic.

Axiom lock_hold : share -> val -> mpred.

(*+ Deep embedding of [mpred]s *)

Inductive Pred :=
  | Mapsto :  Share.t -> type -> val -> val -> Pred
  | Mapsto_ :  Share.t -> type -> val -> Pred
  | Data_at : forall cs : compspecs, Share.t -> forall t : type, reptype t -> val -> Pred
  | Data_at_ : forall cs : compspecs, Share.t -> type -> val -> Pred
  | Lock_hold : Share.t -> val -> Pred
  | Lock_inv : Share.t -> val -> Pred -> Pred
  | Pred_prop : Prop -> Pred
  | Exp : forall A : Type, (A -> Pred) -> Pred
  | Pred_list : list Pred -> Pred.

Fixpoint Interp (p : Pred) : mpred :=
  match p with
  | Mapsto a b c d => mapsto a b c d
  | Mapsto_ a b c => mapsto_ a b c
  | Data_at a b c d e => @data_at a b c d e
  | Data_at_ a b c d => @data_at_ a b c d
  | Lock_inv a b c => lock_inv a b (Interp c)
  | Lock_hold a b => lock_hold a b
  | Pred_prop a => prop a
  | Exp a b => exp (fun x => Interp (b x))
  | Pred_list l => fold_right sepcon emp (map Interp l)
  end.

(*+ Specification of each concurrent primitive *)

Definition acquire_spec :=
   WITH v : val, sh : share, R : Pred
   PRE [ _lock OF tptr tlock ]
     PROP (readable_share sh)
     LOCAL (temp _lock v)
     SEP (lock_inv sh v (Interp R))
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (lock_inv sh v (Interp R); lock_hold Share.top v; Interp R).

Definition release_spec :=
   WITH v : val, sh : share, R : Pred
   PRE [ _lock OF tptr tlock ]
     PROP (readable_share sh)
     LOCAL (temp _lock v)
     SEP (lock_inv sh v (Interp R); lock_hold Share.top v; Interp R)
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (lock_inv sh v (Interp R)).

Definition makelock_spec cs :=
   WITH v : val, sh : share, R : Pred
   PRE [ _lock OF tptr tlock ]
     PROP (writable_share sh)
     LOCAL (temp _lock v)
     SEP (@data_at_ cs sh tlock v)
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (lock_inv sh v (Interp R); lock_hold Share.top v).

Definition freelock_spec cs :=
   WITH v : val, sh : share, R : Pred
   PRE [ _lock OF tptr tlock ]
     PROP (writable_share sh)
     LOCAL (temp _lock v)
     SEP (lock_inv sh v (Interp R); lock_hold Share.top v)
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (@data_at_ cs sh tlock v).

(* Notes about spawn_thread:

As in makelock/acquire/... we get a universe inconsistency when we add
"WITH P" to the specification.  This universe inconsistency will
eventually disappear in a different model for rmaps tracking
covariance and contravariance.  In the meantime, we use a the deep
embedding [Pred] and an embedding [PrePost] of the pre- and
post-condition depending on Type term [ty].

The spawned function has for argument name [_y], which is
existentially quantified.  The function also can use a list of global
variables [globals].

For now, the specification of the spawned function has to be exactly
of the form that you can see below (inside the "match PrePost ...").
Cao Qinxiang is working on a notion of sub-specification that might
enable us to have smoother specifications.

The postcondition might not be emp, so we have potential memory leaks
when a thread exists (those maps are still handled by the concurrent
machine).

To enable joinable threads, the postcondition would be [tptr tthread]
with a type [tthread] related to the postcondition through a [thread]
predicate in the logic.  The [join] would then also be implemented
using the oracle, as [acquire] is.  The postcondition would be [match
PrePost with existT ty (w, pre, post) => thread th (Interp (post w b))
end] *)

Definition spawn_spec :=
  WITH f : val,
       b : val,
       PrePost :
         { ty : Type &
          (ty *                     (* WITH we call spawn with *)
          (ty -> val -> Pred) *       (* precondition *)
          (ty -> val -> Pred))%type}  (* postcondition *)
   PRE [_f OF tptr voidstar_funtype, _args OF tptr tvoid]
     PROP ()
     LOCAL (temp _args b)
     SEP
     (EX _y : ident, EX globals : list (ident * val),
      match PrePost with existT ty (_, pre, post) =>
      (func_ptr'
        (WITH y : val, x : ty
          PRE [ _y OF tptr tvoid ]
            PROP ()
            (LOCALx (temp _y y :: map (fun x => gvar (fst x) (snd x)) globals)
            (SEP   (Interp (pre x y))))
          POST [tptr tvoid]
            PROP  ()
            LOCAL ()
            SEP   (Interp (post x y)))
       f)
      end;
      match PrePost with existT ty (w, pre, post) =>
      Interp (pre w b)
      end)
   POST [ tvoid  ]
     PROP  ()
     LOCAL ()
     SEP   (emp).

(*+ Adding the specifications to an ext_spec *)

Require Import veric.semax_ext.

Definition threadspecs (cs : compspecs) (ext_link : string -> ident) :=
  (ext_link "acquire"%string, acquire_spec) ::
  (ext_link "release"%string, release_spec) ::
  (ext_link "makelock"%string, makelock_spec cs) ::
  (ext_link "freelock"%string, freelock_spec cs) ::
  (ext_link "spawn"%string, spawn_spec) ::
  nil.

Definition CEspec (cs : compspecs) (ext_link : string -> ident) :=
  add_funspecs
    veric.NullExtension.Espec
    ext_link
    (threadspecs cs ext_link).

Lemma semax_conc' cs (ext_link: Strings.String.string -> ident) id sig callingc A P Q :
  let fs := threadspecs cs ext_link in
  let f := mk_funspec sig callingc A P Q in
  in_funspecs (ext_link id, f) fs ->
  funspecs_norepeat fs ->
  (forall n,
      semax.semax_external
        (** * it seems the Espec is already instanciated *)
        (CEspec cs ext_link) (fst (split (fst sig)))
        (EF_external id (funsig2signature sig callingc)) _ P Q n).
Proof.
  apply semax_ext'.
Qed.

Lemma semax_conc cs (ext_link: Strings.String.string -> ident) id ids sig sig' callingc A P Q :
  let fs := threadspecs cs ext_link in
  let f := mk_funspec sig  callingc A P Q in
  in_funspecs (ext_link id,f) fs ->
  funspecs_norepeat fs ->
  ids = fst (split (fst sig)) ->
  sig' = funsig2signature sig callingc ->
  (forall n, semax.semax_external (CEspec cs ext_link) ids (EF_external id sig') _ P Q n).
Proof.
  apply semax_ext.
Qed.
