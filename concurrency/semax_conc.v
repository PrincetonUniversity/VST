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
Require Import veric.semax_ext_oracle.
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

(*+ Type of the oracle *)

Definition Oracle := list rmap.

(*+ Specification of each concurrent primitive *)

(*
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
 *)

Definition acquire_spec :=
  mk_funspecOracle
    Oracle
    (* ARGS *)
    ([(_lock, tptr tlock)], tvoid)
    cc_default
    (* WITH *)
    (Prop * Oracle * val * share * Pred)
    (* PRE *)
    (fun (x : Prop * Oracle * val * share * Pred) (oracle : Oracle) =>
       match x with
       | (ok, oracle_x, v, sh, R) =>
         PROP (readable_share sh;
                 (match oracle with
                  | nil => ~ok
                  | cons mlock oracle' => oracle' = oracle_x /\ (app_pred (Interp R) mlock <-> ok)
                  end))
         LOCAL (temp _lock v)
         SEP (lock_inv sh v (Interp R))
       end)
    (* POST *)
    (fun (x : Prop * Oracle * val * share * Pred) (oracle : Oracle) =>
       match x with
         (ok, oracle_x, v, sh, R) =>
         PROP (oracle = oracle_x; ok)
         LOCAL ()
         SEP (lock_inv sh v (Interp R); lock_hold Share.top v; Interp R)
       end).

(*
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
*)

Definition release_spec :=
  mk_funspecOracle
    Oracle
    (* ARGS *)
    ([(_lock, tptr tlock)], tvoid)
    cc_default
    (* WITH *)
    (Oracle * val * share * Pred)
    (* PRE *)
    (fun (x : Oracle * val * share * Pred) (oracle : Oracle) =>
       match x with
         (oracle_x, v, sh, R) =>
         PROP (oracle = oracle_x; readable_share sh)
         LOCAL (temp _lock v)
         SEP (lock_inv sh v (Interp R); lock_hold Share.top v; Interp R)
       end)
    (* POST *)
    (fun (x : Oracle * val * share * Pred) (oracle : Oracle) =>
       match x with
         (oracle_x, v, sh, R) =>
         PROP (oracle = oracle_x; readable_share sh)
         LOCAL ()
         SEP (lock_inv sh v (Interp R))
       end).

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

(*+ Adding the specifications to a void ext_spec *)


(*! The void ext_spec *)
Definition void_spec : external_specification juicy_mem external_function (list rmap) :=
    Build_external_specification
      juicy_mem external_function (list rmap)
      (fun ef => False)
      (fun ef Hef ge tys vl m z => False) 
      (fun ef Hef ge ty vl m z => False)
      (fun rv m z => False).

Definition ok_void_spec : OracleKind.
 refine (Build_OracleKind (list rmap) (Build_juicy_ext_spec _ void_spec _ _ _)).
Proof.
  simpl; intros; contradiction.
  simpl; intros; contradiction.
  simpl; intros; intros ? ? ? ?; contradiction.
Defined.

Definition threadspecs (cs : compspecs) (ext_link : string -> ident) := 
  (ext_link "acquire"%string, acquire_spec) ::
  (ext_link "release"%string, release_spec) ::
  nil.

(*
Definition threadspecs (cs : compspecs) (ext_link : string -> ident) :=
  (ext_link "acquire"%string, acquire_spec) ::
  (ext_link "release"%string, release_spec) ::
  (ext_link "makelock"%string, makelock_spec cs) ::
  (ext_link "freelock"%string, freelock_spec cs) ::
  (ext_link "spawn"%string, spawn_spec) ::
  nil.
*)

Definition conc_ext_spec (cs : compspecs) (ext_link : string -> ident) :=
  add_funspecsOracle_rec
    ext_link
    ok_void_spec.(@OK_ty)
    ok_void_spec.(@OK_spec)
    (threadspecs cs ext_link).

Definition Concurrent_Espec cs ext_link := Build_OracleKind _ (conc_ext_spec cs ext_link).

Lemma semax_conc' cs (ext_link: string -> ident) id sig cc A P Q :
  let fs := threadspecs cs ext_link in
  let f := mk_funspecOracle Oracle sig cc A P Q in
  In (ext_link id, f) fs ->
  list_norepet (map fst fs) ->
  (forall n,
      semax_external_oracle
        (Concurrent_Espec cs ext_link) (fst (split (fst sig)))
        (EF_external id (funsig2signature sig cc)) _ P Q n).
Proof.
  intros.
  apply semax_ext'_oracle; auto.
Qed.

Lemma semax_conc cs (ext_link: string -> ident) id ids sig sig' cc A P Q :
  let fs := threadspecs cs ext_link in
  let f := mk_funspecOracle Oracle sig  cc A P Q in
  In (ext_link id,f) fs ->
  list_norepet (map fst fs) ->
  ids = fst (split (fst sig)) ->
  sig' = funsig2signature sig cc ->
  (forall n, semax_external_oracle (Concurrent_Espec cs ext_link) ids (EF_external id sig') _ P Q n).
Proof.
  intros.
  subst.
  apply semax_conc'; hnf; auto.
Qed.
