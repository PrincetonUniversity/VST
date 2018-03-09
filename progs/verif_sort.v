Require Import floyd.proofauto.
Require Import progs.list_dt.
Require Import progs.sort.
Require Import Sorted.
Require Import Omega.
Require Import Coq.Sorting.Permutation.

Local Open Scope logic.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition apply_spec :=
Definition spawn_spec :=
  WITH f : val,
       b : val,
       PrePost :
         { ty : Type &
          (ty *                     (* WITH clause for spawned function *)
          (ty -> val -> Pred))%type}  (* precondition (postcondition is emp) *)
   PRE [_f OF tptr voidstar_funtype, _args OF tptr tvoid]
     PROP ( )
     LOCAL (temp _args b)
     SEP
     (match PrePost with existT ty (_, pre) =>
      EX _y : ident, EX globals : ty -> list (ident * val),
      (func_ptr'
        (WITH y : val, x : ty
          PRE [ _y OF tptr tvoid ]
            PROP ()
            (LOCALx (temp _y y :: map (fun x => gvar (fst x) (snd x)) (globals x))
            (SEP   (Interp (pre x y))))
          POST [tptr tvoid]
            PROP  ()
            LOCAL ()
            SEP   (emp))
       f)
      end;
        match PrePost with
          existT ty (w, pre) =>
          Interp (pre w b)
      end
     )
   POST [ tvoid  ]
     PROP  ()
     LOCAL ()
     SEP   (emp).