Require Import VST.floyd.proofauto.
Require Import VST.progs64.fptr_cmp.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition id_spec := 
  DECLARE _id
  WITH x:Z
  PRE [tint] PROP () PARAMS (Vint (Int.repr x)) SEP ()
  POST [tint] 
    PROP ()
    RETURN (Vint (Int.repr x))
    SEP ().

Definition test_id1_spec := 
  DECLARE _test_id1
  WITH gv:globals
  PRE [] PROP () PARAMS () GLOBALS (gv) SEP ()
  POST [tint] 
    PROP ()
    RETURN (Vint (Int.repr 1))
    SEP ().

(*funspecs are not permitted in WITHlist, so the following spec is ill-defined
Definition test_fptr_spec := 
  WITH f:val, phi:funspec
  PRE [tptr (Tfunction (Tcons tint Tnil) tint cc_default)] 
      PROP () PARAMS (f) GLOBALS () SEP (func_ptr' phi f)
  POST [tint] 
    PROP ()
    RETURN (Vint (Int.repr 1))
    SEP ().*)

Definition test_fptr_spec (phi:funspec) := 
  DECLARE _test_fptr
  WITH f:val
  PRE [tptr (Tfunction (tint::nil) tint cc_default)] 
      PROP () PARAMS (f) GLOBALS () SEP (func_ptr' phi f)
  POST [tint] 
    PROP ()
    RETURN (Vint (Int.repr 1))
    SEP ().

Lemma verif_test_fptr phi: semax_body Vprog nil f_test_fptr (test_fptr_spec phi).
Proof. start_function.
  forward_if.
+ sep_apply func_ptr'_emp; forward.
+ rewrite H. sep_apply func_ptr'_isptr. simpl; Intros. contradiction.
Qed.

(*A little adhoc... *)
Definition globals_injective (gv:globals):Prop := 
  forall i j, i <> j -> gv i <> gv j. 

Definition test_fptr_fptr_spec := 
  DECLARE _test_fptr_fptr
  WITH gv:globals
  PRE [] PROP (globals_injective gv) PARAMS () GLOBALS (gv) SEP ()
  POST [tint] 
    PROP ()
    RETURN (Vzero)
    SEP ().

Definition main_spec := 
  DECLARE _main
  WITH gv:globals
  PRE [] PROP (globals_injective gv) PARAMS () GLOBALS (gv) SEP ()
  POST [tint] 
    PROP ()
    RETURN (Vint (Int.repr 2))
    SEP ().

Definition Gprog: funspecs := [test_id1_spec; id_spec; test_fptr_spec (snd id_spec);
                                (_test_id2, snd test_id1_spec); main_spec; test_fptr_fptr_spec].

Lemma verif_test_fptr_fptr: semax_body Vprog Gprog f_test_fptr_fptr test_fptr_fptr_spec.
Proof. start_function.
  make_func_ptr _test_id1.
  make_func_ptr _test_id2.
  unfold test_id1_spec. simpl.
  forward.
  do 2 sep_apply func_ptr'_emp. simpl.
  destruct (EqDec_val (gv _test_id1) (gv _test_id2)).
  - exfalso. apply (H _test_id1 _test_id2); trivial. intros N; inv N.
  - entailer!.
Qed.

Lemma verif_id: semax_body Vprog Gprog f_id id_spec.
Proof. start_function. forward. Qed.  

Lemma verif_test_id1: semax_body Vprog Gprog f_test_id1 test_id1_spec.
Proof. start_function.
  make_func_ptr _id.
  forward_if.
+ sep_apply func_ptr'_emp; forward.
+ rewrite H. sep_apply func_ptr'_isptr. simpl; Intros. contradiction.
Qed.

Lemma verif_test_id2: semax_body Vprog Gprog f_test_id2 (_test_id2, snd test_id1_spec).
Proof. unfold test_id1_spec. simpl snd. start_function.
  make_func_ptr _id. forward_call. forward.
Qed.

Lemma verif_test_main: semax_body Vprog Gprog f_main main_spec.
Proof. start_function. forward_call. forward_call. forward_call. forward. Qed.