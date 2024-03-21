Require Import VST.floyd.proofauto.
Require Import VST.progs.alias.

Lemma field_compatible_void_int cs p : @field_compatible cs (tptr Tvoid) [] p = @field_compatible cs tint [] p.
Proof.
  eapply PropExtensionality.propositional_extensionality.
  destruct p;
  cbv [field_compatible align_compatible size_compatible];
  intuition idtac;
  repeat match goal with
         | H : align_compatible_rec _ _ _ |- _ => inversion H; clear H; subst end.
  all : econstructor; eauto.
Qed.

Lemma data_at__void_int cs sh p : @data_at_ cs sh (tptr Tvoid) p = @data_at_ cs sh tint p.
Proof. rewrite 2data_at__memory_block, field_compatible_void_int; trivial. Qed.

Lemma data_at_void_int_null cs sh p : @data_at cs sh (tptr Tvoid) (Vint Int.zero) p = @data_at cs sh tint (Vint Int.zero) p.
Proof.
  cbv [data_at field_at at_offset nested_field_type tptr].
  simpl data_at_rec.
  unfold data_at_rec.
  simpl rank_type.
  simpl type_induction.type_func.
  rewrite field_compatible_void_int; f_equal.
  change (Tint I32 Signed noattr) with tint.
  erewrite mapsto_null_mapsto_pointer; reflexivity.
Qed.


#[export] Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition foo_spec := DECLARE _foo WITH p : val
  PRE [ tptr tint, tptr (tptr Tvoid) ] PROP() PARAMS(p; p) SEP(data_at_ Tsh tint p)
  POST [ tint ] PROP() RETURN(Vint Int.zero) SEP(data_at_ Tsh tint p).

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
  erewrite <-data_at__void_int.
  forward.
  rewrite data_at_void_int_null.
  forward.
  forward.
  entailer!.
Qed.

Definition Espec := add_funspecs NullExtension.Espec (ext_link_prog prog) Gprog.
#[export] Existing Instance Espec.
Lemma prog_correct: semax_prog prog tt Vprog Gprog.
Proof. prove_semax_prog. semax_func_cons body_foo. semax_func_cons body_main. Qed.
