
(* Diffie-Hellman definitions. *)

Set Implicit Arguments.

Require Import Crypto.
Require Import RndNat.
Require Export GroupTheory.

Local Open Scope group_scope.

Section DDH.

  Section DDH_Concrete.

    Context`{FCG : FiniteCyclicGroup}.
    Variable A : (GroupElement * GroupElement * GroupElement) -> Comp bool. 

    Definition DDH0 :=
      x <-$ [0 .. order);
      y <-$ [0 .. order);
      b <-$ (A (g^x, g^y, g^(x * y)));
      ret b.
    
    Definition DDH1  :=
      x <-$ [0 .. order);
      y <-$ [0 .. order);
      z <-$ [0 .. order);
      b <-$ (A (g^x, g^y, g^z));
      ret b.

    Definition DDH_Advantage:= | Pr[DDH0] - Pr[DDH1] |.

  End DDH_Concrete. 
  

End DDH.
