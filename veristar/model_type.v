Load loadpath.
Require Import VST.msl.base VST.msl.sepalg.
Require Import veristar.variables.

(** Separation Logic Interface

   This module type axiomatizes the types and operators upon which our
   soundness proof depends.

   NOTE: This module type will probably be made obsolete sometime in the future
   (if we ever get back to working on this project).

   We now believe it's better to axiomatize the separation logic directly
   (i.e., its proof theory) as opposed to axiomatizing the /models/ of the
   separation logic, which is what we do here. *)

Module Type VERISTAR_LOGIC.

(** Locations and values *)

Parameters loc val : Type.
Declare Instance Join_val: Join val.
Declare Instance Perm_val: Perm_alg val.
Declare Instance Sep_val: Sep_alg val.
Declare Instance Canc_val: Canc_alg val.
Parameter val2loc : val -> option loc.
Parameter nil_val : val.
Axiom nil_not_loc : val2loc nil_val = None.

(** The empty value: read "undefined" *)

Parameter empty_val : val.
Axiom emp_empty_val : forall v, identity v <-> v = empty_val.
Definition full (v : val) := forall v2, joins v v2 -> identity v2.
Axiom val2loc_full : forall v l, val2loc v = Some l -> full v.
Axiom nil_full : full nil_val.
Axiom empty_not_full : ~full empty_val.
Axiom val2loc_inj : forall v1 v2 l,
  val2loc v1 = Some l ->  val2loc v2 = Some l -> v1=v2.
Axiom loc_eq_dec : forall l1 l2 : loc, Decidable.decidable (l1=l2).
Axiom nil_dec : forall v, Decidable.decidable (v=nil_val).

(** Variables, environments *)

Definition var : Type := Ident.t.
Parameter env : Type.
Parameter env_get : env -> var -> val.
Parameter env_set : var -> val -> env -> env.
Axiom gss_env : forall (x : var) (v : val) (s : env),
  v<>empty_val -> env_get (env_set x v s) x = v.
Axiom gso_env : forall (x y : var) (v : val) (s : env),
  x<>y -> env_get (env_set x v s) y = env_get s y.
(* For now, we assume vars are defined locations (i.e., we don't yet model
   data fields or deal with undefined vars; that is future work).
   In general, our soundness proof doesn't require the user to exhibit an
   empty environment anyway. *)
(*Parameter empty_env : env.*)
(*Axiom env_gempty : forall x, env_get empty_env x = empty_val.*)
Axiom env_reset : forall s x, env_set x (env_get s x) s = s.
Axiom env_reset2 : forall s x z, env_set x (env_get s x) (env_set x z s) = s.

(** Heaps *)

Parameter heap : Type.
Declare Instance Join_heap: Join heap.
Declare Instance Perm_heap: Perm_alg heap.
Declare Instance Sep_heap: Sep_alg heap.
Declare Instance Canc_heap: Canc_alg heap.
Parameter rawnext: forall (x: loc) (y : val) (s : heap), Prop.
Parameter emp_at : forall (l: loc) (h: heap), Prop.
Axiom heap_gempty : forall h l, identity h -> emp_at l h.
Definition nil_or_loc (v: val) := v=nil_val \/ exists l, val2loc v = Some l.
Axiom mk_heap_rawnext : forall h x0 x y, val2loc (x0) = Some x ->
  nil_or_loc y -> exists h', rawnext x y h' /\ comparable h h'.
Axiom rawnext_out : forall {x x0 x' y h},
  rawnext x y h -> val2loc x0 = Some x' -> x'<>x -> emp_at x' h.

Definition rawnext' x y h := exists h0, join_sub h0 h /\ rawnext x y h0.

Axiom rawnext_at1 : forall {x y h1 h2 h},
  rawnext' x y h1 -> join h1 h2 h -> emp_at x h2 /\ rawnext' x y h.

Axiom rawnext_at2 : forall {x y h1 h2 h},
  join h1 h2 h -> rawnext' x y h -> emp_at x h2 -> rawnext' x y h1.

Axiom  rawnext_not_emp : forall {x y h}, rawnext' x y h -> ~emp_at x h.

Axiom emp_at_join: forall {h1 h2 h},
  join h1 h2 h -> forall l, (emp_at l h1 /\ emp_at l h2) <-> emp_at l h.

Axiom rawnext_unique : forall x z z' s s' t t' r,
  rawnext x z s -> rawnext x z' s' -> join s t r -> join s' t' r ->
  z' = z /\ s'=s.

Axiom vars_defined_locs : forall z (e : env),
  exists v, env_get e z = v /\ nil_or_loc v.

End VERISTAR_LOGIC.
