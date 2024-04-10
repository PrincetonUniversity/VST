Require Import VST.floyd.proofauto.
Require Import VST.progs64.printf.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Require Import VST.floyd.printf.
Require Import ITree.Eq.

#[export] Instance nat_id : FileId := { file_id := nat; stdin := 0%nat; stdout := 1%nat }.
#[export] Instance file_struct : FileStruct := {| FILEid := ___sFILE64; reent := __reent; f_stdin := __stdin; f_stdout := __stdout |}.

Section printf.

Context `{!VSTGS (@IO_itree (@IO_event file_id)) Σ}.

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog (write_list stdout (string2bytes "Hello, world!
");; write_list stdout (string2bytes "This is line 2.
"))%itree gv
  POST [ tint ] main_post prog gv.

Definition Gprog : funspecs :=  
   (*ltac:(with_library prog *)(ltac:(make_printf_specs prog) ++ [ main_spec ])(*)*).

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
make_stdio (@IO_event file_id).
repeat do_string2bytes.
repeat (sep_apply data_at_to_cstring; []).
sep_apply (has_ext_ITREE).

forward_printf tt (write_list stdout (string2bytes "This is line 2.
")).
{ apply bi.sep_mono; first done.
  cancel. }
forward_call.
forward.
forward_fprintf outp ((Ers, string2bytes "line", gv ___stringlit_2), (Int.repr 2, tt)) (stdout, Ret tt : @IO_itree (@IO_event file_id)).
{ rewrite !bi.sep_assoc (bi.sep_comm _ (ITREE _)) -!bi.sep_assoc; apply bi.sep_mono; [|cancel].
  rewrite bind_ret'; apply derives_refl. }
forward.
Qed.

End printf.
