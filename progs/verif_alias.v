Require Import VST.floyd.proofauto.
Require Import VST.progs.alias.

#[export] Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition foo_spec := DECLARE _foo WITH p : val
  PRE [ tptr tint, tptr tint ] PROP() PARAMS(p; p) SEP(data_at_ Tsh tint p)
  POST [ tint ] PROP() RETURN(Vint Int.zero) SEP(data_at_ Tsh tint p).

Definition main_spec := DECLARE _main WITH gv : globals
  PRE  [] main_pre prog tt gv
  POST [ tint ] PROP() RETURN (Vint Int.zero) SEP(has_ext tt).

Definition Gprog : funspecs := ltac:(with_library prog [foo_spec; main_spec]).

Lemma body_main : semax_body Vprog Gprog f_main main_spec.
Proof. start_function. forward_call. forward. entailer!. Qed.

Lemma body_foo : semax_body Vprog Gprog f_foo foo_spec.
Proof. start_function. repeat forward. entailer!. Qed.

Definition Espec := add_funspecs NullExtension.Espec (ext_link_prog prog) Gprog.
#[export] Existing Instance Espec.
Lemma prog_correct: semax_prog prog tt Vprog Gprog.
Proof. prove_semax_prog. semax_func_cons body_foo. semax_func_cons body_main. Qed.
