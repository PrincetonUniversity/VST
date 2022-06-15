Require Import VST.floyd.proofauto.
Require Import VST.progs.printf.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Require Import VST.floyd.printf.
Require Import ITree.Eq.

#[export] Instance nat_id : FileId := { file_id := nat; stdin := 0%nat; stdout := 1%nat }.
#[export] Instance file_struct : FileStruct := {| FILEid := ___sFILE64; reent := __reent; f_stdin := __stdin; f_stdout := __stdout |}.

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog (@write_list _ _  (@ReSum_id (Type->Type) IFun Id_IFun (@IO_event (@file_id nat_id))) stdout
       (string2bytes "Hello, world!
");; write_list stdout (string2bytes "This is line 2.
"))%itree gv
  POST [ tint ] main_post prog gv.

Definition Gprog : funspecs :=  
   (*ltac:(with_library prog *)(ltac:(make_printf_specs prog) ++ [ main_spec ])(*)*).

Definition E := @IO_event file_id.

(** THE FOLLOWING HORRIBLE HACK,
 which modifies the two tactics forward_fprintf and forward_printf 
 to instantiate the second implicit argument of fprintf_spec_sub,
 is a workaround for a change in InterationTrees 5.0, that I don't fully understand,
 that made it unable to fill in this argument by itself.  -- A. Appel, June 2022 
*)
Ltac forward_fprintf outv w w' ::=
 repeat rewrite <- seq_assoc;
 try match goal with |- semax _ _ (Scall _ _) _ =>
   rewrite -> semax_seq_skip
 end;
lazymatch goal with
 | gv: globals |- @semax ?cs _ _ ?Pre (Ssequence (Scall None (Evar _ _) (?f :: Evar ?id _ :: _)) _) _ =>
   let tf := constr:(typeof f) in
   let tf := eval hnf in tf in
   lazymatch tf with Tpointer (Tstruct ?FILEid _) _ =>
     let sub := constr:(@fprintf_spec_sub _ E _ cs FILEid) in
       forward_fprintf' gv Pre id sub outv w w'
   end
end.

Ltac forward_printf w w' ::=
 repeat rewrite <- seq_assoc;
 try match goal with |- semax _ _ (Scall _ _) _ =>
   rewrite -> semax_seq_skip
 end;
match goal with
 | gv: globals |- @semax ?cs _ _ ?Pre (Ssequence (Scall None (Evar _ _) (Evar ?id _ :: _)) _) _ =>
       forward_fprintf' gv Pre id 
      (@printf_spec_sub _ E _ cs)
      nullval w w'
end.


Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
make_stdio.
repeat do_string2bytes.
repeat (sep_apply data_at_to_cstring; []).
sep_apply (has_ext_ITREE(E := E)).

forward_printf tt (@write_list _ (@IO_event file_id) _ stdout (string2bytes "This is line 2.
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
