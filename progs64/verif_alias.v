Require Import VST.floyd.proofauto.
Require Import VST.progs64.alias.

Lemma field_compatible_void_long cs p : @field_compatible cs (tptr Tvoid) [] p = @field_compatible cs tlong [] p.
Proof.
  eapply PropExtensionality.propositional_extensionality.
  destruct p;
  cbv [field_compatible align_compatible size_compatible];
  intuition idtac;
  repeat match goal with
         | H : align_compatible_rec _ _ _ |- _ => inversion H; clear H; subst end.
  all : econstructor; eauto.
Qed.

Lemma data_at__void_long cs sh p : @data_at_ cs sh (tptr Tvoid) p = @data_at_ cs sh tlong p.
Proof. rewrite 2data_at__memory_block, field_compatible_void_long; trivial. Qed.

Lemma data_at_void_long_null cs sh p : @data_at cs sh (tptr Tvoid) (Vlong Int64.zero) p = @data_at cs sh tlong (Vlong Int64.zero) p.
Proof.
  cbv [data_at field_at at_offset nested_field_type tptr].
  simpl data_at_rec.
  unfold data_at_rec.
  simpl rank_type.
  simpl type_induction.type_func.
  rewrite field_compatible_void_long; f_equal.
  change (Tlong Signed noattr) with tlong.
  rewrite mapsto_tuint_tptr_nullval.
  reflexivity.
Qed.


#[export] Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition foo_spec := DECLARE _foo WITH p : val
  PRE [ tptr tlong, tptr (tptr Tvoid) ] PROP() PARAMS(p; p) SEP(data_at_ Tsh tlong p)
  POST [ tlong ] PROP() RETURN(Vlong Int64.zero) SEP(data_at_ Tsh tlong p).

Definition main_spec := DECLARE _main WITH gv : globals
  PRE  [] main_pre prog tt gv
  POST [ tint ] PROP() RETURN (Vint Int.zero) SEP(has_ext tt).

Definition Gprog : funspecs := ltac:(with_library prog [foo_spec; main_spec]).

Lemma body_main : semax_body Vprog Gprog f_main main_spec.
Proof. start_function. forward_call. forward. entailer!. Qed.

Lemma body_foo : semax_body Vprog Gprog f_foo foo_spec.
Proof.
  start_function.
  forward.
  match goal with | |- context[data_at ?sh ?t ?Vs ?op] => sep_apply (data_at_data_at_ sh t Vs op) end.
  erewrite <-data_at__void_long.
  forward.
  rewrite data_at_void_long_null.
  forward.
  forward.
  entailer!.
Qed.

Definition Espec := add_funspecs NullExtension.Espec (ext_link_prog prog) Gprog.
#[export] Existing Instance Espec.
Lemma prog_correct: semax_prog prog tt Vprog Gprog.
Proof. prove_semax_prog. semax_func_cons body_foo. semax_func_cons body_main. Qed.
