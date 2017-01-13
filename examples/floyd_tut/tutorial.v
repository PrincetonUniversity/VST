(* NOTE: The LoadPath commands below assume that you run
 * coqide or Proof General with current directory as the one
 * in which this tutorial.v file is located, not some parent
 * directory.
 *)

(* TUTORIAL ON LIFTED EXPRESSIONS.
 * For more information and explanations,
 * see these chapters of Program Logics for Certified Compilers:
 *  Ch. 12 Separation Logic as a logic;
 *  Ch. 21 Lifted separation logics;
 *  Ch. 23 Expressions, values, and assertions
 *)

(* LOADPATHS, assuming this file is located
 *  in vst/examples/___/___.v
 * and that you start coqide/PG from the same directory.
 *)
Add LoadPath "../../msl" as msl.
Add LoadPath "../../compcert" as compcert.
Add LoadPath "../../../compcert" as compcert.
Add LoadPath "../../sepcomp" as sepcomp.
Add LoadPath "../../veric" as veric.
Add LoadPath "../../floyd" as floyd.
(* Instead, you could delete all the [Add LoadPath]
 * commands, and run coqide/PG from the root [vst]
 * directory, with these command-line arguments:
 * -I msl as msl -R compcert -as compcert -I sepcomp -as sepcomp -I veric -as veric -I floyd -as floyd
 *)

(* Import all the definitions of CompCert values and syntax *)
Require Import compcert.exportclight.Clightdefs.

(* Import all the definitions of Separation Logic for C light *)
Require Import veric.SeparationLogic.
Import Extensionality.

(* MATHEMATICAL INTEGERS, 32-BIT INTEGERS *)

(*The mathematical integers are represented by Coq's Z type: *)
Check 0%Z : Z.
Check 1%Z : Z.
(* Recall that the %Z notation means, interpret this notation
 * in the Z notation-scope, not in "nat" or "positive" scope *)

(* CompCert's Int.int implements 32-bit modular arithmetic *)
Goal int = Int.int.      Proof. reflexivity. Qed.

(* Int.repr injects from Z to int, truncating mod 2^32 *)
Check Int.repr :  Z -> int.
Goal Int.repr 0 = Int.repr (Z.pow 2 32).
apply Int.eqm_samerepr.
unfold Int.eqm.
apply Int.eqmod_sym; apply Int.eqmod_mod.
reflexivity.
Qed.

(* Int.signed(x) gives the integer value of x when interpreted
 * as a twos-complement signed 32-bit integer. *)
Check Int.signed: int -> Z.
Goal Int.signed (Int.repr 0) = 0%Z.
Proof. apply Int.signed_repr. compute; split; congruence. Qed.
Goal Int.signed (Int.repr (-1)) = (-1)%Z.
Proof. apply Int.signed_repr. compute; split; congruence. Qed.
Goal Int.signed (Int.repr (Z.pow 2 32 - 1)) = (-1)%Z.
Proof.
 replace (Int.repr (2 ^ 32 - 1)) with (Int.repr (-1)).
 apply Int.signed_repr.
 compute; split; congruence.
 apply Int.eqm_samerepr.
 change (-1)%Z with (0 - 1)%Z.
 apply Int.eqmod_sub.
 apply Int.eqmod_sym; apply Int.eqmod_mod.
 reflexivity.
 apply Int.eqmod_refl.
Qed.

(* Int.unsigned(x) gives the integer value of x when interpreted
 * as an unsigned 32-bit integer. *)
Check Int.unsigned: int -> Z.
Goal Int.unsigned (Int.repr 0) = 0%Z.
Proof. apply Int.unsigned_repr. compute; split; congruence. Qed.
Goal Int.unsigned (Int.repr (-1)) = (Z.pow 2 32 - 1)%Z.
Proof.
 replace  (Int.repr (-1)) with (Int.repr (2 ^ 32 - 1)).
 apply Int.unsigned_repr.
 compute; split; congruence.
 apply Int.eqm_samerepr.
 change (-1)%Z with (0 - 1)%Z.
 apply Int.eqmod_sub.
 apply Int.eqmod_mod.
 reflexivity.
 apply Int.eqmod_refl.
Qed.

(* Some standard definitions *)
Goal Int.zero = Int.repr 0.     Proof. reflexivity. Qed.
Goal Int.one = Int.repr 1.      Proof. reflexivity. Qed.
Definition nullval := Vint Int.zero.

(* COMPCERT VALUES.
 * The contents of a scalar variable (or the results of
 * evaluating an expression) in CompCert C light (or in
 * any of the CompCert languages) is a "val", which may
 * be undefined (uninitialized), an integer (32-bit),
 * a long long integer (64-bit), a floating-point (64-bit),
 * or a pointer.   Shorter-sized integers (8-bit,16-bit)
 * are extended to 32-bit when represented in scalar
 * variables.  Shorter-sized floats (32-bit) are extended to
 * 64-bit when represented in scalar variables.
 *)

Print val.
(* Inductive val : Type :=
    Vundef : val
  | Vint : int -> val
  | Vlong : int64 -> val
  | Vfloat : float -> val
  | Vptr : block -> int -> val
  | maybe others such as Vsingle . . .
*)


(* Inject 0 from Z to int, then from int to val: *)
Check (Vint (Int.repr 0)) : val.

(* A well-typed integer value must be a Vint: *)
Goal forall v, tc_val tint v -> exists i, v = Vint i.
Proof. intros. destruct v; inversion H. eauto. Qed.

(* A well-typed pointer must be either zero or a Vptr *)
Goal forall v, tc_val (tptr tint) v ->
   match v with Vint i => i=Int.zero
                     | Vptr _ _ => True
                     | _ => False
   end.
Proof. intros. destruct v; inversion H; auto.
Qed.

(* C-LIGHT EXPRESSIONS *)
(* C Light expression syntax *)
Print expr.
(* Inductive expr : Type :=
    Econst_int : int -> type -> expr
  | Econst_float : float -> type -> expr
  | Econst_long : int64 -> type -> expr
  | Evar : ident -> type -> expr
  | Etempvar : ident -> type -> expr
  | Ederef : expr -> type -> expr
  | Eaddrof : expr -> type -> expr
  | Eunop : unary_operation -> expr -> type -> expr
  | Ebinop : binary_operation -> expr -> expr -> type -> expr
  | Ecast : expr -> type -> expr
  | Efield : expr -> ident -> type -> expr
  | maybe others . . .
*)

(* LIFTED FUNCTIONS:  DEPRECATED!
   Version 1.6 of VST does not use much use lifted functions,
   so you can mostly ignore Chapter 21 of the PLCC book.
 *)

(* The type [mpred] is for spatial predicates, i.e. predicates
 * that describe heaplets and that are subject to the separation
 * operators,  * emp && || etc.
 *)
Locate mpred.

(* The injection from a proposition (Prop) to an mpred is "prop",
 *  which is also notated !!
 *)
Check prop : Prop -> mpred.

(* In informal "latex" separation logic, the predicate p\mapsto q
 * is a spatial predicate describing a heaplet with just one cell
 * at address p, with contents q.  Our mapsto predicate:
 *)
Check mapsto : share -> type -> val -> val -> mpred.

(* However, your proofs about C programs should
 not use the low-level "mapsto"; instead, use the typed
 version of mapsto, called data_at:
*)

Require Import floyd.proofauto.

Check data_at: Share.t -> forall t : type, reptype t -> val -> mpred.


(* Assertions such as preconditions in Hoare triples have the
 * type    [environ->mpred],  that is, they predicate first
 * on an environment and then on a spatial heaplet.
 *
 * For example, at address (f rho), with full ownership (Tsh),
 * there is a 32-bit integer (type [tint] in the C type system),
 * whose value is Int.zero.
 *)
Check (fun rho => mapsto Tsh tint (f rho) (Vint Int.zero)).
(* And another way of saying the same exact thing: *)
Check `(mapsto Tsh tint) f `(Vint Int.zero).

(* Let's Define a variable-name or two.  Such definitions will
 * typically be imported from file foo.v produced by
 * clightgen when compiling foo.c
 *)
Definition _i : ident := 4%positive.
Definition _s : ident := 5%positive.
Definition _t : ident := 6%positive.
(* Recall that the % notation means, interpret these constants
 * as [positive] numbers, not as nat or Z.  CompCert happens
 * to use the positive type for identifiers, because it has
 * very efficient symbol-table lookup
 *)


(* Each of the following lines says the same thing in a different
 * notation: the value of local-variable
    "s"  in the current environment is zero: *)
Check  (fun rho => prop (Vint Int.zero = eval_id _s rho)).
Check `prop (`(eq (Vint Int.zero)) (eval_id _s)).
Check local (`(eq nullval) (eval_id _s)).
Check local (`eq `nullval (eval_id _s)).

(* You can see from this that [local] is just short for "lifted prop" *)

Require Import floyd.client_lemmas.
Require Import floyd.assert_lemmas.
Open Scope logic.

(* A typical assertion in separation logic is the andp-conjunction
 * of a nospatial "local" conjunct, with a spatial conjunct:
 *)

Check   ( local (`(eq nullval) (eval_id _i))
         &&   `(mapsto Tsh tint) (eval_id _s) (eval_id _i)).

(* Various spatial predicates can be separated from each other
 * with the star operator.  Also there may be some nonspatial
 * predicates that are pure propositions, that is,
 * they don't even depend on the local environment
 *)
Parameter i: int.
Check (prop (i <> Int.zero) && local (`(eq (Vint i)) (eval_id _i)) &&
              ( `(mapsto Tsh tint) (eval_id _s) `(Vint i)
                * `(mapsto Tsh (tptr tint)) (eval_id _t) (eval_id _s))).

(* The notation PROP(...) LOCAL(...) SEP(...) cleanly
 * segregates the pure propositions, the local assertions,
 * and the spatial assertions.  The assertion above
 * can be equivalently written,
 *)
Check (PROP(i<>Int.zero)
       LOCAL(`(eq (Vint i)) (eval_id _i))
       SEP (`(mapsto Tsh tint) (eval_id _s) `(Vint i);
             `(mapsto Tsh (tptr tint)) (eval_id _t) (eval_id _s))).

(* Expression evaluation.  An expression can be evaluated
 * as an r-value using eval_expr, or as an l-value using
 * eval_lvalue.  Although CompCert C light's eval_expr
 * distinguishes between stuck expressions (which
 * fail to evaluate at all) and undefined expressions
 * (which successfully evaluate to Vundef), in the program
 * logic we do not need to distinguish.  Thus, all expressions
 * evaluate to a value; but the stuck expressions and
 * the undefined expressions both evaluate to Vundef.
 *)

(* Our eval_expr function is NOT the same as the
 * eval_expr relation from CompCert.
 *)

Locate eval_expr.
 (* "Locate" tells us that there are two eval_expr's out there,
  * and the one we're using here is the FIRST one, from veric:
  * Constant veric.expr.eval_expr
  * Inductive compcert.cfrontend.Clight.eval_expr
  *)

Check eval_expr : expr -> environ -> val.
Print eval_expr.
(* Fixpoint eval_expr (e: expr) : environ -> val :=
 match e with
 | Econst_int i ty => `(Vint i)
 | Econst_long i ty => `(Vlong i)
 | Econst_float f ty => `(Vfloat f)
 | Etempvar id ty => eval_id id
 | Eaddrof a ty => eval_lvalue a
 | Eunop op a ty =>  `(eval_unop op (typeof a)) (eval_expr a)
 | Ebinop op a1 a2 ty =>
                  `(eval_binop op (typeof a1) (typeof a2)) (eval_expr a1) (eval_expr a2)
 | Ecast a ty => `(eval_cast (typeof a) ty) (eval_expr a)
 | Evar id ty => `(deref_noload ty) (eval_var id ty)
 | Ederef a ty => `(deref_noload ty) (`force_ptr (eval_expr a))
 | Efield a i ty => `(deref_noload ty) (`(eval_field (typeof a) i) (eval_lvalue a))
 end

 with eval_lvalue (e: expr) : environ -> val :=
 match e with
 | Evar id ty => eval_var id ty
 | Ederef a ty => `force_ptr (eval_expr a)
 | Efield a i ty => `(eval_field (typeof a) i) (eval_lvalue a)
 | _  => `Vundef
 end.
*)

(* An environ contains ... *)
Print environ.
(* ... various components for global variables,
  addressable local variables, and nonaddressable locals.
 But users of the separation logic will rarely pick
 apart actual environments; environments will be treated
  abstractly and invisibly, since they really exist only
 at run-time (dynamically), not statically. *)

Check (Etempvar _s tint : expr).
Check (eval_expr (Etempvar _s tint)).
Goal eval_expr (Etempvar _s tint) = eval_id _s.
Proof. reflexivity. Qed.
Check (fun rho : environ => Vint (Int.repr 0)) : environ -> val.
Check ( `(Vint (Int.repr 0)) ) : environ -> val.
Goal `(Vint (Int.repr 0)) = fun rho : environ => Vint (Int.repr 0).
Proof. reflexivity. Qed.
Check (Econst_int (Int.repr 0) tint) : expr.
Check eval_expr (Econst_int (Int.repr 0) tint) : environ -> val.
Goal eval_expr (Econst_int (Int.repr 0) tint) = `(Vint Int.zero).
Proof. reflexivity. Qed.






