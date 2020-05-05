Require Import VST.floyd.proofauto.
Require Import VST.progs.structerr.

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Local Open Scope logic.

Definition t_struct_foo := Tstruct _foo noattr.

Definition f_spec : ident * funspec :=
 DECLARE _f
  WITH u: unit
  PRE [ ]
          PROP  ()
          PARAMS ()
          GLOBALS () 
          SEP   ()
  POST [ Tstruct _foo noattr ]
        PROP () LOCAL()
           SEP ().

Definition g_spec : ident * funspec :=
 DECLARE _g
  WITH ij: val
  PRE [ Tstruct _foo noattr ]
          PROP  ()
          PARAMS (ij)
          GLOBALS () 
          SEP   ()
  POST [ Tvoid ]
        PROP () LOCAL()
           SEP ().

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog tt gv
  POST [ tint ]  
     PROP() 
     LOCAL () 
     SEP(TT).

Definition Gprog : funspecs :=   [f_spec; g_spec; main_spec].

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
Fail start_function.
Abort.

Lemma body_f:  semax_body Vprog Gprog f_f f_spec.
Proof.
Fail start_function.
Abort.
