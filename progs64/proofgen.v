Require Import VST.floyd.proofauto.

Definition spaces (n : nat) : string := String.concat " " (repeat EmptyString (S n)).

Fixpoint code_to_script (s : statement) (level : nat) : string :=
  match s with
  | Sskip | Sassign _ _ | Sset _ _ | Sbreak | Scontinue | Sreturn _ => spaces level ++ "forward.
"
  | Ssequence ((Scall (Some ret) _ _) as s1) ((Sset _ (Etempvar ret2 _)) as s2)
  | Ssequence ((Scall (Some ret) _ _) as s1) ((Sset _ (Ecast (Etempvar ret2 _) _)) as s2) =>
      if eq_dec ret ret2 then spaces level ++ "forward_call.
" else code_to_script s1 level ++ code_to_script s2 level
  | Scall _ _ _ | Sbuiltin _ _ _ _ => spaces level ++ "forward_call.
"
  | Ssequence a b => code_to_script a level ++ code_to_script b level
  | Sifthenelse _ a b => spaces level ++ "forward_if. {
" ++ code_to_script a (level + 2) ++ spaces level ++ "}
" ++ spaces level ++ "{
" ++ code_to_script b (level + 2) ++ spaces level ++ "}
"
  | Sloop (Ssequence (Sifthenelse _ Sskip Sbreak) s) Sskip => spaces level ++ "forward_while. {
" ++ spaces (level + 2) ++ "(* loop pre *) }
" ++ spaces level ++ "{
" ++ code_to_script s (level + 2) ++ spaces level ++ "}
"
  | Sloop s1 s2 => spaces level ++ "forward_loop. {
" ++ spaces (level + 2) ++ "(* loop pre *) }
" ++ spaces level ++ "{
" ++ code_to_script s1 (level + 2) ++ spaces level ++ "}
" ++ spaces level ++ "{
" ++ code_to_script s2 (level + 2) ++ spaces level ++ "}
"
  | Sswitch _ ls => "forward_if.
" ++ stmts_to_script ls level
  | _ => "(* error: goto not supported *)
"
  end
with stmts_to_script (ls : labeled_statements) (level : nat) : string :=
  match ls with
  | LSnil => EmptyString
  | LScons _ s rest => spaces level ++ "{
" ++ code_to_script s (level + 2) ++ spaces level ++ "}
" ++ stmts_to_script rest level
  end.

Definition header : string := "Require Import VST.floyd.proofauto.
Require Import VST.progs64.input.

#[local] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog tt gv
  POST [ tint ] main_post prog gv.

Definition Gprog : funspecs := ltac:(with_library prog [main_spec]).

".

Definition make_script (f : function) : string := header ++
  "Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
" ++ code_to_script (fn_body f) 2 ++ "  try entailer!.
Qed.
".

Require Import VST.progs64.input.

Goal True.
Compute (make_script f_main).
Abort.
