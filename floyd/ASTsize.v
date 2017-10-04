(*Require Import VST.floyd.proofauto.
Import ListNotations.
Require sha.sha.
Require sha.SHA256.
Local Open Scope logic.

Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.vst_lemmas.
Require Import sha.hmac_pure_lemmas.
Require Import sha.hmac_common_lemmas.

Require Import sha.hmac.
Require Import sha.spec_hmac.
*)
Require Import compcert.cfrontend.Clight.
Require Import Coq.Lists.List.

Fixpoint expr_size (e:expr):nat :=
  match e with 
  | Econst_int _ _ => 1
  | Econst_float _ _ => 1
  | Econst_single _ _ => 1
  | Econst_long _ _ => 1
  | Evar _ _ => 1
  | Etempvar _ _ => 1
  | Ederef e1 _ => expr_size e1 + 1 
  | Eaddrof e1 _ => expr_size e1 + 1 
  | Eunop _ e1 _ => expr_size e1 + 1 
  | Ebinop _ e1 e2 _ => expr_size e1 + expr_size e2 + 1 
  | Ecast e1 _ => expr_size e1 + 1 
  | Efield e1 _ _ => expr_size e1 + 1 
  | Esizeof _ _ => 1
  | Ealignof _ _ => 1
end. 

Definition exprlist_size (l:list expr) :=
  @fold_right nat expr (fun e x => plus x (expr_size e)) O l.

Fixpoint ASTsize (s:statement){struct s}:nat := 
  match s with
    Sskip => 1
  | Sassign e1 e2 => expr_size e1 + expr_size e2 + 1
  | Sset x e => expr_size e + 1
  | Scall optid f args => exprlist_size args + 1
  | Sbuiltin oid f types args => exprlist_size args +1
  | Ssequence s1 s2 => ASTsize s1 + ASTsize s2 + 1
  | Sifthenelse e s1 s2 => expr_size e + ASTsize s1 + ASTsize s2 + 1
  | Sloop s1 s2 => ASTsize s1 + ASTsize s2 + 1
  | Sbreak => 1
  | Scontinue => 1
  | Sreturn optexp => match optexp with None => 1 | Some e => expr_size e + 1 end
  | Sswitch e ls => expr_size e + labeled_ASTsize ls  + 1
  | Slabel l s1 => ASTsize s1 + 1
  | Sgoto _ => 1
  end
with labeled_ASTsize (x:labeled_statements) {struct x}:nat := 
  match x with
  | LSnil => 0
  | LScons _ s ls => ASTsize s + labeled_ASTsize ls + 1
end.
(*
Eval compute in ASTsize b.
*)