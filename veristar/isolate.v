Require Import Coq.Lists.List.
Require Import veristar.variables veristar.datatypes.
Require Import compcert.Coqlib.
Require Import VST.veric.Coqlib2.
Require Import ZArith.

Require Import veristar.fresh.
Require Import veristar.veristar.
Require Import veristar.basic.

Definition oracle (ent: entailment) : bool :=
 match VeriStar.check_entailment ent with
 | VeriStar.Valid => true
 | VeriStar.C_example _ => false
 | VeriStar.Aborted _ _ => false
 end.

Bind Scope entail_scope with entailment.
Local Open Scope entail_scope.

Definition incon (a: assertion) : bool :=
   oracle (Entailment a
               (Assertion (Nequ Nil Nil :: nil)
                              match a with (Assertion _ sigma) => sigma end)).

Lemma eq_expr (e1 e2: expr) : {e1=e2}+{e1<>e2}.
Proof.
intros.
 destruct e1; destruct e2; auto; try  decide equality; apply Ident.eq_dec.
Defined.

Fixpoint exorcize (e: expr) (pi: list pn_atom) (sigma0 sigma: list space_atom) (nextv: var)
         : option (list assertion) :=
 match sigma with
 | nil => if incon (Assertion pi (rev sigma0)) then Some nil else None
 | Lseg f f' :: sigma1 =>
          if oracle (Entailment
                         (Assertion pi (rev sigma0 ++ (Lseg f f') :: sigma1))
                         (Assertion (Equ e f :: nil) (rev sigma0 ++ Lseg f f' :: sigma1)))
          then match exorcize e (Equ f f' :: pi)  (Lseg f f' :: sigma0) sigma1 nextv with
                   | Some l => Some (Assertion pi (Next e (Var nextv) :: Lseg (Var nextv) f' :: rev sigma0 ++ sigma1) ::l)
                   | None => None
                  end
          else exorcize e pi (Lseg f f' :: sigma0) sigma1 nextv
 | a :: sigma1 =>
          exorcize e pi (a :: sigma0) sigma1 nextv
 end.

Fixpoint isolate' (e: expr) (pi: list pn_atom) (sigma0 sigma: list space_atom) (nextv: var) (count: nat)
         : option (list assertion) :=
 match sigma with
 | nil => if  lt_dec count 2
              then None
              else if incon (Assertion (Equ e Nil :: pi) (rev sigma0))
                     then exorcize e pi nil (rev sigma0) nextv
                     else None
 | Next e1 e2 :: sigma1 =>
          if eq_expr e e1
          then Some [Assertion pi (Next e e2 :: rev sigma0 ++ sigma1)]
          else if oracle (Entailment
                         (Assertion pi (rev sigma0 ++ (Next e1 e2) :: sigma1))
                         (Assertion (Equ e e1 :: nil) (rev sigma0 ++ (Next e1 e2) :: sigma1)))
          then Some [Assertion pi (Next e e2 :: rev sigma0 ++ sigma1)]
          else isolate' e pi (Next e1 e2 :: sigma0) sigma1 nextv count
 | Lseg f f' :: sigma1 =>
          if oracle (Entailment
                         (Assertion pi (rev sigma0 ++ (Lseg f f') :: sigma1))
                         (Assertion (Equ e f :: Nequ f f' :: nil ) (rev sigma0 ++ (Lseg f f') :: sigma1)))
          then Some [Assertion pi (Next e (Var nextv) :: Lseg (Var nextv) f' :: rev sigma0 ++ sigma1)]
          else if oracle (Entailment
                         (Assertion pi (rev sigma0 ++ (Lseg f f') :: sigma1))
                         (Assertion (Equ e f :: nil) (rev sigma0 ++ (Lseg f f') :: sigma1)))
                 then isolate' e pi (Lseg f f' :: sigma0) sigma1 nextv (S count)
          else isolate' e pi (Lseg f f' :: sigma0) sigma1 nextv count
 end.

Definition isolate (e: expr) (P: assertion) (nextv: var) : option (list assertion) :=
 match P with Assertion pi sigma =>
  isolate' e pi nil sigma nextv 0
 end.




























