(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)

Set Implicit Arguments.

Require Import FCF.FCF.

Section cAU.

  Variable K D R : Set.
  Hypothesis D_EqDec : EqDec D.
  Hypothesis R_EqDec : EqDec R.
  Variable f : K -> D -> R.
  Variable RndK : Comp K.

  Section cAU.
    Variable A : Comp (D * D).

    Definition Adv_au_once_G :=
      k <-$ RndK;
      [d1, d2] <-$2 A;
      ret (negb (eqb d1 d2) && eqb (f k d1) (f k d2)).
  End cAU.

  Section WCR.

    Variable A : OracleComp D R (D * D).

    Definition WCR_Oracle (k : K)(s : unit)(d : D) :=
      ret (f k d, tt).

    Definition Adv_WCR_G :=
      k <-$ RndK;
      [p, _] <-$2 A _ _ (WCR_Oracle k) tt;
      [d1, d2] <-2 p;
      ret (negb (eqb d1 d2) && eqb (f k d1) (f k d2)).

    Definition Adv_WCR := Pr[Adv_WCR_G].


  End WCR.

End cAU.