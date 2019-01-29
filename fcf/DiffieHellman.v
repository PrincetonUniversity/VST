(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)

(* Diffie-Hellman definitions. *)

Set Implicit Arguments.

Require Import FCF.FCF.
Require Import FCF.RndNat.
Require Export FCF.GroupTheory.

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
