Require Import veric.base.
Require Import msl.rmaps.
Require Import veric.compcert_rmaps.
Import Mem.
Require Import msl.msl_standard.
Require Import veric.juicy_mem veric.juicy_mem_lemmas veric.juicy_mem_ops.
Require Import sepcomp.extspec.
Require Import veric.juicy_extspec.
Require Import veric.tycontext.
Require Import veric.expr2.
Require Import veric.semax.
Require Import veric.semax_call.

Require Import floyd.proofauto.

(* we don't really know these variables *)
(* let's suppose that for now we don't need _lock_t, we replace lock_t with int *)

Definition _f := 1%positive.      (* alpha-convertible *)
Definition _args := 2%positive.   (* alpha-convertible *)
Definition _lock := 1%positive.   (* alpha-convertible *)
Definition _lock_t := 2%positive. (* 2 is the number given by
clightgen threads.h is included first *)

Variable voidstar_funtype : type.
Definition tlock := Tstruct _lock_t noattr.
(* Notation tlock := tuint (only parsing). *)

Axiom lock_inv : share -> val -> mpred -> mpred.

Axiom lock_inv_share_join : forall sh1 sh2 sh v R, sepalg.join sh1 sh2 sh ->
  lock_inv sh1 v R * lock_inv sh2 v R = lock_inv sh v R.

Axiom lock_inv_isptr : forall sh v R, `(lock_inv sh v R) |-- !!(isptr v).

Inductive Pred :=
  | Mapsto :  Share.t -> type -> val -> val -> Pred
  | Mapsto_ :  Share.t -> type -> val -> Pred
  | Data_at : forall cs : compspecs, Share.t -> forall t : type, reptype t -> val -> Pred
  | Data_at_ : forall cs : compspecs, Share.t -> type -> val -> Pred
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
  | Pred_prop a => prop a
  | Exp a b => exp (fun x => Interp (b x))
  | Pred_list l => fold_right sepcon emp (map Interp l)
  end.

Definition acquire_spec :=
   WITH v : val, sh : share, R : Pred
   PRE [ _lock OF tptr tlock ]
     PROP (readable_share sh)
     LOCAL (temp _lock v)
     SEP ((lock_inv sh v (Interp R)))
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP ((lock_inv sh v (Interp R)) ; Interp R).

Definition release_spec :=
   WITH v : val, sh : share, R : Pred
   PRE [ _lock OF tptr tlock ]
     PROP (readable_share sh)
     LOCAL (temp _lock v)
     SEP ((lock_inv sh v (Interp R)) ; Interp R)
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP ((lock_inv sh v (Interp R))).

Definition makelock_spec cs :=
   WITH v : val, sh : share, R : Pred
   PRE [ _lock OF tptr tlock ]
     PROP (writable_share sh)
     LOCAL (temp _lock v)
     SEP ((@data_at_ cs sh tlock v))
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP ((lock_inv sh v (Interp R))).

(* Definition makelock_spec cs := *)
(*    WITH v : val, sh : share *)
(*    PRE [ _lock OF tptr tlock ] *)
(*      PROP (writable_share sh) *)
(*      LOCAL (temp _lock v) *)
(*      SEP ((@data_at_ cs sh tlock v)) *)
(*    POST [ tvoid ] *)
(*      PROP () *)
(*      LOCAL () *)
(*      SEP ((lock_inv sh v emp)). *)

Definition freelock_spec cs :=
   WITH v : val, sh : share, R : Pred
   PRE [ _lock OF tptr tlock ]
     PROP (writable_share sh)
     LOCAL (temp _lock v)
     SEP (Interp R ; (lock_inv sh v (Interp R)))
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (Interp R ; (@data_at_ cs sh tlock v)).

(* See discussion about spawn in threadlib.v *)

Definition spawn_spec :=
  WITH f : val,
       b : val,
       PrePost : { ty : Type &
                        (ty *                     (* WITH we call spawn with *)
                        (ty -> val -> Pred) *       (* precondition *)
                        (ty -> val -> Pred))%type}  (* postcondition *)
   PRE [_f OF tptr voidstar_funtype, _args OF tptr tvoid]
     PROP ()
     LOCAL (temp _args b)
     SEP
     (EX _y : ident,
match PrePost with existT ty (_, pre, post) =>
      (func_ptr'
        (WITH y : val, x : ty
          PRE [ _y OF tptr tvoid ]
            PROP  ()
            LOCAL (temp _y y)
            SEP   (Interp (pre x y))
          POST [tptr tvoid]
            PROP  ()
            LOCAL ()
            SEP   (Interp (post x y))
       )
       f)
end;
match PrePost with existT ty (w, pre, post) =>
      Interp (pre w b)
end
     )
   POST [ tvoid (* tptr tthread *) ]
   (* EX th : val, *)
     PROP  ()
     LOCAL ((* temp ret_temp th *))
     SEP   (emp
(* match PrePost with existT ty (w, pre, post) => *)
(* thread th (Interp (post w b)) *)
(* end *)
           ).

Require Import veric.semax_ext.
Require veric.NullExtension.

(* this? *)
(*
Variables _acquire _release _makelock _freelock _spawn : ident.

Definition threadspecs cs :=
  (_acquire, acquire_spec) ::
  (_release, release_spec) ::
  (_makelock, makelock_spec cs) ::
  (_freelock, freelock_spec cs) ::
  (_spawn, spawn_spec) ::
  nil.

Definition CEspec cs :=
  add_funspecs
    veric.NullExtension.Espec
    (fun s =>
       match s with
       | "acquire"%string => _acquire
       | "release"%string => _release
       | "makelock"%string => _makelock
       | "freelock"%string => _freelock
       | "spawn"%string => _spawn
       | _ => 1%positive
       end)
    (threadspecs cs).
*)
(* or this? *)

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

(** * question: cs?  *)

(** * question: ext_link? *)

(** * question: Pred? *)

Lemma semax_conc' cs (ext_link: Strings.String.string -> ident) id sig callingc A P Q :
  let fs := threadspecs cs ext_link in
  let f := mk_funspec sig callingc A P Q in
  in_funspecs (ext_link id, f) fs ->
  funspecs_norepeat fs ->
  (forall n, semax.semax_external
        (* veric.SeparationLogicSoundness.SoundSeparationLogic.CSL.semax_external *)
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

(* this makes a dependency (because of the notations for the function
specs), but in real life we'll call this with these specs and use the
proofs in SeparationLogicSoundness to prove this, right? *)

(* later: naming problem:
- all functions use _lock (and spawn uses _f and _args) : alpha-conversion?
- makelock/freelock use _lock_t (but it will be replaced with an integer, right?)
 *)
