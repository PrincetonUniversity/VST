Require Import VST.floyd.proofauto.
Require Import VST.progs.printf.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Require Import VST.floyd.printf.
Require Import ITree.Eq.Eq.

Instance nat_id : FileId := { file_id := nat; stdin := 0%nat; stdout := 1%nat }.
Instance file_struct : FileStruct := {| FILEid := ___sFILE64; reent := __reent; f_stdin := __stdin; f_stdout := __stdout |}.

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog (write_list stdout (string2bytes "Hello, world!
");; write_list stdout (string2bytes "This is line 2.
")) gv
  POST [ tint ] main_post prog gv.

Definition Gprog : funspecs :=  
   (*ltac:(with_library prog *)(ltac:(make_printf_specs prog) ++ [ main_spec ])(*)*).

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
make_stdio.
repeat do_string2bytes.
repeat (sep_apply data_at_to_cstring; []).
sep_apply (has_ext_ITREE(E := @IO_event file_id)).

forward_printf tt (write_list stdout (string2bytes "This is line 2.
")).
{ rewrite !sepcon_assoc; apply sepcon_derives; cancel.
  apply derives_refl. }
forward_call.
forward.
forward_fprintf outp ((Ers, string2bytes "line", gv ___stringlit_2), (Int.repr 2, tt)) (stdout, Ret tt : @IO_itree (@IO_event file_id)).
{ rewrite 3sepcon_assoc, sepcon_comm, sepcon_assoc; apply sepcon_derives; cancel.
  rewrite bind_ret'; apply derives_refl. }
forward.
Qed.
