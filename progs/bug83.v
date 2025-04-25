(* THIS FILE DEMONSTRATES A PROBLEM IN COQ,
   and explains something about VST issue #156.
  Please leave it in the VST repository, at least for the time being.
  -- A. Appel, April 2018
*)

Require Import VST.floyd.proofauto.
Require Import VST.floyd.compat. Import NoOracle.
Require Import VST.progs.bst.

Require Export VST.floyd.Funspec_old_Notation.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Definition a : assert := 
  SEPx (data_at_ Tsh (Tstruct _tree noattr) Vundef :: nil).

Definition b : assert := 
  SEPx (data_at(cs := _) Tsh (Tstruct _tree noattr) (default_val (Tstruct _tree noattr)) Vundef :: nil).

Definition c : assert := 
  SEPx (data_at(cs := _) Tsh (Tstruct _tree noattr) (Vundef, (Vundef, (Vundef, Vundef))) Vundef :: nil).

Definition e : assert := 
 @bi_exist _ _ (fun s : val => 
  SEPx (data_at(cs := _) Tsh (Tstruct _tree noattr) (default_val (Tstruct _tree noattr)) Vundef :: nil)).

Definition f : assert := 
 @bi_exist (assert) _ (fun s : val => 
  SEPx (data_at(cs := _) Tsh (Tstruct _tree noattr) (Vundef, (Vundef, (Vundef, Vundef))) Vundef :: nil)).

Definition g : assert := 
 @bi_exist _ _ (fun s : val => 
  SEPx (data_at(cs := CompSpecs) Tsh (Tstruct _tree noattr) (Vundef, (Vundef, (Vundef, Vundef))) Vundef :: nil)).

(* Fail *) Definition h : assert := 
 @bi_exist _ _ (fun s : val => 
  SEPx (data_at(cs := _) Tsh (Tstruct _tree noattr) (Vundef, (Vundef, (Vundef, Vundef))) Vundef :: nil)).

(* Typeclass inference in the presence of dependent types is broken.  
   That is not a new observation; as Gonthier et al. ("How to make ad hoc proof automation 
   less ad hoc", JFP 23 (4): 357–401, 2013) explain, Coq's type-class resolution is 
   triggered after unification, so that unification cannot be informed by type-class resolution.
   In this case, the "compspecs" argument to data_at is used to calculate the appropriate
   type for the value  (Vundef, (Vundef, (Vundef, Vundef))), but that value must be unified
   before "compspecs" is resolved.

   That part I understand.  What is more difficult to understand is, why does Coq give
  such a bizarre error message?

    In environment
    s : val
    The term
     "SEP (data_at Tsh (Tstruct _tree noattr) (Vundef, (Vundef, (Vundef, Vundef))) Vundef)"
    has type "environ -> mpred" while it is expected to have type 
    "mpred".

*)
