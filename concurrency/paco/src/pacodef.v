Require Export VST.concurrency.paco.src.paconotation.
Set Implicit Arguments.

(** * Formalization of Parameterized Coinduction: the Internal Approach

    We use the strict positivization trick (Section 6.1 of the paper)
    in order to define G for arbitrary functions (here called paco{n}).
*)

Section Arg0_def.
Variable gf : rel0 -> rel0.
Implicit Arguments gf [].

CoInductive paco0( r: rel0) : Prop :=
| paco0_pfold pco
    (LE : pco <0= (paco0 r \0/ r))
    (SIM: gf pco)
.
Definition upaco0( r: rel0) := paco0 r \0/ r.
End Arg0_def.
Implicit Arguments paco0 [ ].
Implicit Arguments upaco0 [ ].
Hint Unfold upaco0.

Section Arg0_2_def.
Variable gf_0 gf_1 : rel0 -> rel0 -> rel0.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].

CoInductive paco0_2_0( r_0 r_1: rel0) : Prop :=
| paco0_2_0_pfold pco_0 pco_1
    (LE : pco_0 <0= (paco0_2_0 r_0 r_1 \0/ r_0))
    (LE : pco_1 <0= (paco0_2_1 r_0 r_1 \0/ r_1))
    (SIM: gf_0 pco_0 pco_1)
with paco0_2_1( r_0 r_1: rel0) : Prop :=
| paco0_2_1_pfold pco_0 pco_1
    (LE : pco_0 <0= (paco0_2_0 r_0 r_1 \0/ r_0))
    (LE : pco_1 <0= (paco0_2_1 r_0 r_1 \0/ r_1))
    (SIM: gf_1 pco_0 pco_1)
.
Definition upaco0_2_0( r_0 r_1: rel0) := paco0_2_0 r_0 r_1 \0/ r_0.
Definition upaco0_2_1( r_0 r_1: rel0) := paco0_2_1 r_0 r_1 \0/ r_1.
End Arg0_2_def.
Implicit Arguments paco0_2_0 [ ].
Implicit Arguments upaco0_2_0 [ ].
Hint Unfold upaco0_2_0.
Implicit Arguments paco0_2_1 [ ].
Implicit Arguments upaco0_2_1 [ ].
Hint Unfold upaco0_2_1.

Section Arg0_3_def.
Variable gf_0 gf_1 gf_2 : rel0 -> rel0 -> rel0 -> rel0.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].
Implicit Arguments gf_2 [].

CoInductive paco0_3_0( r_0 r_1 r_2: rel0) : Prop :=
| paco0_3_0_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <0= (paco0_3_0 r_0 r_1 r_2 \0/ r_0))
    (LE : pco_1 <0= (paco0_3_1 r_0 r_1 r_2 \0/ r_1))
    (LE : pco_2 <0= (paco0_3_2 r_0 r_1 r_2 \0/ r_2))
    (SIM: gf_0 pco_0 pco_1 pco_2)
with paco0_3_1( r_0 r_1 r_2: rel0) : Prop :=
| paco0_3_1_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <0= (paco0_3_0 r_0 r_1 r_2 \0/ r_0))
    (LE : pco_1 <0= (paco0_3_1 r_0 r_1 r_2 \0/ r_1))
    (LE : pco_2 <0= (paco0_3_2 r_0 r_1 r_2 \0/ r_2))
    (SIM: gf_1 pco_0 pco_1 pco_2)
with paco0_3_2( r_0 r_1 r_2: rel0) : Prop :=
| paco0_3_2_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <0= (paco0_3_0 r_0 r_1 r_2 \0/ r_0))
    (LE : pco_1 <0= (paco0_3_1 r_0 r_1 r_2 \0/ r_1))
    (LE : pco_2 <0= (paco0_3_2 r_0 r_1 r_2 \0/ r_2))
    (SIM: gf_2 pco_0 pco_1 pco_2)
.
Definition upaco0_3_0( r_0 r_1 r_2: rel0) := paco0_3_0 r_0 r_1 r_2 \0/ r_0.
Definition upaco0_3_1( r_0 r_1 r_2: rel0) := paco0_3_1 r_0 r_1 r_2 \0/ r_1.
Definition upaco0_3_2( r_0 r_1 r_2: rel0) := paco0_3_2 r_0 r_1 r_2 \0/ r_2.
End Arg0_3_def.
Implicit Arguments paco0_3_0 [ ].
Implicit Arguments upaco0_3_0 [ ].
Hint Unfold upaco0_3_0.
Implicit Arguments paco0_3_1 [ ].
Implicit Arguments upaco0_3_1 [ ].
Hint Unfold upaco0_3_1.
Implicit Arguments paco0_3_2 [ ].
Implicit Arguments upaco0_3_2 [ ].
Hint Unfold upaco0_3_2.

Section Arg1_def.
Variable T0 : Type.
Variable gf : rel1 T0 -> rel1 T0.
Implicit Arguments gf [].

CoInductive paco1( r: rel1 T0) x0 : Prop :=
| paco1_pfold pco
    (LE : pco <1= (paco1 r \1/ r))
    (SIM: gf pco x0)
.
Definition upaco1( r: rel1 T0) := paco1 r \1/ r.
End Arg1_def.
Implicit Arguments paco1 [ T0 ].
Implicit Arguments upaco1 [ T0 ].
Hint Unfold upaco1.

Section Arg1_2_def.
Variable T0 : Type.
Variable gf_0 gf_1 : rel1 T0 -> rel1 T0 -> rel1 T0.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].

CoInductive paco1_2_0( r_0 r_1: rel1 T0) x0 : Prop :=
| paco1_2_0_pfold pco_0 pco_1
    (LE : pco_0 <1= (paco1_2_0 r_0 r_1 \1/ r_0))
    (LE : pco_1 <1= (paco1_2_1 r_0 r_1 \1/ r_1))
    (SIM: gf_0 pco_0 pco_1 x0)
with paco1_2_1( r_0 r_1: rel1 T0) x0 : Prop :=
| paco1_2_1_pfold pco_0 pco_1
    (LE : pco_0 <1= (paco1_2_0 r_0 r_1 \1/ r_0))
    (LE : pco_1 <1= (paco1_2_1 r_0 r_1 \1/ r_1))
    (SIM: gf_1 pco_0 pco_1 x0)
.
Definition upaco1_2_0( r_0 r_1: rel1 T0) := paco1_2_0 r_0 r_1 \1/ r_0.
Definition upaco1_2_1( r_0 r_1: rel1 T0) := paco1_2_1 r_0 r_1 \1/ r_1.
End Arg1_2_def.
Implicit Arguments paco1_2_0 [ T0 ].
Implicit Arguments upaco1_2_0 [ T0 ].
Hint Unfold upaco1_2_0.
Implicit Arguments paco1_2_1 [ T0 ].
Implicit Arguments upaco1_2_1 [ T0 ].
Hint Unfold upaco1_2_1.

Section Arg1_3_def.
Variable T0 : Type.
Variable gf_0 gf_1 gf_2 : rel1 T0 -> rel1 T0 -> rel1 T0 -> rel1 T0.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].
Implicit Arguments gf_2 [].

CoInductive paco1_3_0( r_0 r_1 r_2: rel1 T0) x0 : Prop :=
| paco1_3_0_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <1= (paco1_3_0 r_0 r_1 r_2 \1/ r_0))
    (LE : pco_1 <1= (paco1_3_1 r_0 r_1 r_2 \1/ r_1))
    (LE : pco_2 <1= (paco1_3_2 r_0 r_1 r_2 \1/ r_2))
    (SIM: gf_0 pco_0 pco_1 pco_2 x0)
with paco1_3_1( r_0 r_1 r_2: rel1 T0) x0 : Prop :=
| paco1_3_1_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <1= (paco1_3_0 r_0 r_1 r_2 \1/ r_0))
    (LE : pco_1 <1= (paco1_3_1 r_0 r_1 r_2 \1/ r_1))
    (LE : pco_2 <1= (paco1_3_2 r_0 r_1 r_2 \1/ r_2))
    (SIM: gf_1 pco_0 pco_1 pco_2 x0)
with paco1_3_2( r_0 r_1 r_2: rel1 T0) x0 : Prop :=
| paco1_3_2_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <1= (paco1_3_0 r_0 r_1 r_2 \1/ r_0))
    (LE : pco_1 <1= (paco1_3_1 r_0 r_1 r_2 \1/ r_1))
    (LE : pco_2 <1= (paco1_3_2 r_0 r_1 r_2 \1/ r_2))
    (SIM: gf_2 pco_0 pco_1 pco_2 x0)
.
Definition upaco1_3_0( r_0 r_1 r_2: rel1 T0) := paco1_3_0 r_0 r_1 r_2 \1/ r_0.
Definition upaco1_3_1( r_0 r_1 r_2: rel1 T0) := paco1_3_1 r_0 r_1 r_2 \1/ r_1.
Definition upaco1_3_2( r_0 r_1 r_2: rel1 T0) := paco1_3_2 r_0 r_1 r_2 \1/ r_2.
End Arg1_3_def.
Implicit Arguments paco1_3_0 [ T0 ].
Implicit Arguments upaco1_3_0 [ T0 ].
Hint Unfold upaco1_3_0.
Implicit Arguments paco1_3_1 [ T0 ].
Implicit Arguments upaco1_3_1 [ T0 ].
Hint Unfold upaco1_3_1.
Implicit Arguments paco1_3_2 [ T0 ].
Implicit Arguments upaco1_3_2 [ T0 ].
Hint Unfold upaco1_3_2.

Section Arg2_def.
Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable gf : rel2 T0 T1 -> rel2 T0 T1.
Implicit Arguments gf [].

CoInductive paco2( r: rel2 T0 T1) x0 x1 : Prop :=
| paco2_pfold pco
    (LE : pco <2= (paco2 r \2/ r))
    (SIM: gf pco x0 x1)
.
Definition upaco2( r: rel2 T0 T1) := paco2 r \2/ r.
End Arg2_def.
Implicit Arguments paco2 [ T0 T1 ].
Implicit Arguments upaco2 [ T0 T1 ].
Hint Unfold upaco2.

Section Arg2_2_def.
Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable gf_0 gf_1 : rel2 T0 T1 -> rel2 T0 T1 -> rel2 T0 T1.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].

CoInductive paco2_2_0( r_0 r_1: rel2 T0 T1) x0 x1 : Prop :=
| paco2_2_0_pfold pco_0 pco_1
    (LE : pco_0 <2= (paco2_2_0 r_0 r_1 \2/ r_0))
    (LE : pco_1 <2= (paco2_2_1 r_0 r_1 \2/ r_1))
    (SIM: gf_0 pco_0 pco_1 x0 x1)
with paco2_2_1( r_0 r_1: rel2 T0 T1) x0 x1 : Prop :=
| paco2_2_1_pfold pco_0 pco_1
    (LE : pco_0 <2= (paco2_2_0 r_0 r_1 \2/ r_0))
    (LE : pco_1 <2= (paco2_2_1 r_0 r_1 \2/ r_1))
    (SIM: gf_1 pco_0 pco_1 x0 x1)
.
Definition upaco2_2_0( r_0 r_1: rel2 T0 T1) := paco2_2_0 r_0 r_1 \2/ r_0.
Definition upaco2_2_1( r_0 r_1: rel2 T0 T1) := paco2_2_1 r_0 r_1 \2/ r_1.
End Arg2_2_def.
Implicit Arguments paco2_2_0 [ T0 T1 ].
Implicit Arguments upaco2_2_0 [ T0 T1 ].
Hint Unfold upaco2_2_0.
Implicit Arguments paco2_2_1 [ T0 T1 ].
Implicit Arguments upaco2_2_1 [ T0 T1 ].
Hint Unfold upaco2_2_1.

Section Arg2_3_def.
Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable gf_0 gf_1 gf_2 : rel2 T0 T1 -> rel2 T0 T1 -> rel2 T0 T1 -> rel2 T0 T1.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].
Implicit Arguments gf_2 [].

CoInductive paco2_3_0( r_0 r_1 r_2: rel2 T0 T1) x0 x1 : Prop :=
| paco2_3_0_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <2= (paco2_3_0 r_0 r_1 r_2 \2/ r_0))
    (LE : pco_1 <2= (paco2_3_1 r_0 r_1 r_2 \2/ r_1))
    (LE : pco_2 <2= (paco2_3_2 r_0 r_1 r_2 \2/ r_2))
    (SIM: gf_0 pco_0 pco_1 pco_2 x0 x1)
with paco2_3_1( r_0 r_1 r_2: rel2 T0 T1) x0 x1 : Prop :=
| paco2_3_1_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <2= (paco2_3_0 r_0 r_1 r_2 \2/ r_0))
    (LE : pco_1 <2= (paco2_3_1 r_0 r_1 r_2 \2/ r_1))
    (LE : pco_2 <2= (paco2_3_2 r_0 r_1 r_2 \2/ r_2))
    (SIM: gf_1 pco_0 pco_1 pco_2 x0 x1)
with paco2_3_2( r_0 r_1 r_2: rel2 T0 T1) x0 x1 : Prop :=
| paco2_3_2_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <2= (paco2_3_0 r_0 r_1 r_2 \2/ r_0))
    (LE : pco_1 <2= (paco2_3_1 r_0 r_1 r_2 \2/ r_1))
    (LE : pco_2 <2= (paco2_3_2 r_0 r_1 r_2 \2/ r_2))
    (SIM: gf_2 pco_0 pco_1 pco_2 x0 x1)
.
Definition upaco2_3_0( r_0 r_1 r_2: rel2 T0 T1) := paco2_3_0 r_0 r_1 r_2 \2/ r_0.
Definition upaco2_3_1( r_0 r_1 r_2: rel2 T0 T1) := paco2_3_1 r_0 r_1 r_2 \2/ r_1.
Definition upaco2_3_2( r_0 r_1 r_2: rel2 T0 T1) := paco2_3_2 r_0 r_1 r_2 \2/ r_2.
End Arg2_3_def.
Implicit Arguments paco2_3_0 [ T0 T1 ].
Implicit Arguments upaco2_3_0 [ T0 T1 ].
Hint Unfold upaco2_3_0.
Implicit Arguments paco2_3_1 [ T0 T1 ].
Implicit Arguments upaco2_3_1 [ T0 T1 ].
Hint Unfold upaco2_3_1.
Implicit Arguments paco2_3_2 [ T0 T1 ].
Implicit Arguments upaco2_3_2 [ T0 T1 ].
Hint Unfold upaco2_3_2.

Section Arg3_def.
Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable gf : rel3 T0 T1 T2 -> rel3 T0 T1 T2.
Implicit Arguments gf [].

CoInductive paco3( r: rel3 T0 T1 T2) x0 x1 x2 : Prop :=
| paco3_pfold pco
    (LE : pco <3= (paco3 r \3/ r))
    (SIM: gf pco x0 x1 x2)
.
Definition upaco3( r: rel3 T0 T1 T2) := paco3 r \3/ r.
End Arg3_def.
Implicit Arguments paco3 [ T0 T1 T2 ].
Implicit Arguments upaco3 [ T0 T1 T2 ].
Hint Unfold upaco3.

Section Arg3_2_def.
Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable gf_0 gf_1 : rel3 T0 T1 T2 -> rel3 T0 T1 T2 -> rel3 T0 T1 T2.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].

CoInductive paco3_2_0( r_0 r_1: rel3 T0 T1 T2) x0 x1 x2 : Prop :=
| paco3_2_0_pfold pco_0 pco_1
    (LE : pco_0 <3= (paco3_2_0 r_0 r_1 \3/ r_0))
    (LE : pco_1 <3= (paco3_2_1 r_0 r_1 \3/ r_1))
    (SIM: gf_0 pco_0 pco_1 x0 x1 x2)
with paco3_2_1( r_0 r_1: rel3 T0 T1 T2) x0 x1 x2 : Prop :=
| paco3_2_1_pfold pco_0 pco_1
    (LE : pco_0 <3= (paco3_2_0 r_0 r_1 \3/ r_0))
    (LE : pco_1 <3= (paco3_2_1 r_0 r_1 \3/ r_1))
    (SIM: gf_1 pco_0 pco_1 x0 x1 x2)
.
Definition upaco3_2_0( r_0 r_1: rel3 T0 T1 T2) := paco3_2_0 r_0 r_1 \3/ r_0.
Definition upaco3_2_1( r_0 r_1: rel3 T0 T1 T2) := paco3_2_1 r_0 r_1 \3/ r_1.
End Arg3_2_def.
Implicit Arguments paco3_2_0 [ T0 T1 T2 ].
Implicit Arguments upaco3_2_0 [ T0 T1 T2 ].
Hint Unfold upaco3_2_0.
Implicit Arguments paco3_2_1 [ T0 T1 T2 ].
Implicit Arguments upaco3_2_1 [ T0 T1 T2 ].
Hint Unfold upaco3_2_1.

Section Arg3_3_def.
Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable gf_0 gf_1 gf_2 : rel3 T0 T1 T2 -> rel3 T0 T1 T2 -> rel3 T0 T1 T2 -> rel3 T0 T1 T2.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].
Implicit Arguments gf_2 [].

CoInductive paco3_3_0( r_0 r_1 r_2: rel3 T0 T1 T2) x0 x1 x2 : Prop :=
| paco3_3_0_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <3= (paco3_3_0 r_0 r_1 r_2 \3/ r_0))
    (LE : pco_1 <3= (paco3_3_1 r_0 r_1 r_2 \3/ r_1))
    (LE : pco_2 <3= (paco3_3_2 r_0 r_1 r_2 \3/ r_2))
    (SIM: gf_0 pco_0 pco_1 pco_2 x0 x1 x2)
with paco3_3_1( r_0 r_1 r_2: rel3 T0 T1 T2) x0 x1 x2 : Prop :=
| paco3_3_1_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <3= (paco3_3_0 r_0 r_1 r_2 \3/ r_0))
    (LE : pco_1 <3= (paco3_3_1 r_0 r_1 r_2 \3/ r_1))
    (LE : pco_2 <3= (paco3_3_2 r_0 r_1 r_2 \3/ r_2))
    (SIM: gf_1 pco_0 pco_1 pco_2 x0 x1 x2)
with paco3_3_2( r_0 r_1 r_2: rel3 T0 T1 T2) x0 x1 x2 : Prop :=
| paco3_3_2_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <3= (paco3_3_0 r_0 r_1 r_2 \3/ r_0))
    (LE : pco_1 <3= (paco3_3_1 r_0 r_1 r_2 \3/ r_1))
    (LE : pco_2 <3= (paco3_3_2 r_0 r_1 r_2 \3/ r_2))
    (SIM: gf_2 pco_0 pco_1 pco_2 x0 x1 x2)
.
Definition upaco3_3_0( r_0 r_1 r_2: rel3 T0 T1 T2) := paco3_3_0 r_0 r_1 r_2 \3/ r_0.
Definition upaco3_3_1( r_0 r_1 r_2: rel3 T0 T1 T2) := paco3_3_1 r_0 r_1 r_2 \3/ r_1.
Definition upaco3_3_2( r_0 r_1 r_2: rel3 T0 T1 T2) := paco3_3_2 r_0 r_1 r_2 \3/ r_2.
End Arg3_3_def.
Implicit Arguments paco3_3_0 [ T0 T1 T2 ].
Implicit Arguments upaco3_3_0 [ T0 T1 T2 ].
Hint Unfold upaco3_3_0.
Implicit Arguments paco3_3_1 [ T0 T1 T2 ].
Implicit Arguments upaco3_3_1 [ T0 T1 T2 ].
Hint Unfold upaco3_3_1.
Implicit Arguments paco3_3_2 [ T0 T1 T2 ].
Implicit Arguments upaco3_3_2 [ T0 T1 T2 ].
Hint Unfold upaco3_3_2.

Section Arg4_def.
Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable gf : rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3.
Implicit Arguments gf [].

CoInductive paco4( r: rel4 T0 T1 T2 T3) x0 x1 x2 x3 : Prop :=
| paco4_pfold pco
    (LE : pco <4= (paco4 r \4/ r))
    (SIM: gf pco x0 x1 x2 x3)
.
Definition upaco4( r: rel4 T0 T1 T2 T3) := paco4 r \4/ r.
End Arg4_def.
Implicit Arguments paco4 [ T0 T1 T2 T3 ].
Implicit Arguments upaco4 [ T0 T1 T2 T3 ].
Hint Unfold upaco4.

Section Arg4_2_def.
Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable gf_0 gf_1 : rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].

CoInductive paco4_2_0( r_0 r_1: rel4 T0 T1 T2 T3) x0 x1 x2 x3 : Prop :=
| paco4_2_0_pfold pco_0 pco_1
    (LE : pco_0 <4= (paco4_2_0 r_0 r_1 \4/ r_0))
    (LE : pco_1 <4= (paco4_2_1 r_0 r_1 \4/ r_1))
    (SIM: gf_0 pco_0 pco_1 x0 x1 x2 x3)
with paco4_2_1( r_0 r_1: rel4 T0 T1 T2 T3) x0 x1 x2 x3 : Prop :=
| paco4_2_1_pfold pco_0 pco_1
    (LE : pco_0 <4= (paco4_2_0 r_0 r_1 \4/ r_0))
    (LE : pco_1 <4= (paco4_2_1 r_0 r_1 \4/ r_1))
    (SIM: gf_1 pco_0 pco_1 x0 x1 x2 x3)
.
Definition upaco4_2_0( r_0 r_1: rel4 T0 T1 T2 T3) := paco4_2_0 r_0 r_1 \4/ r_0.
Definition upaco4_2_1( r_0 r_1: rel4 T0 T1 T2 T3) := paco4_2_1 r_0 r_1 \4/ r_1.
End Arg4_2_def.
Implicit Arguments paco4_2_0 [ T0 T1 T2 T3 ].
Implicit Arguments upaco4_2_0 [ T0 T1 T2 T3 ].
Hint Unfold upaco4_2_0.
Implicit Arguments paco4_2_1 [ T0 T1 T2 T3 ].
Implicit Arguments upaco4_2_1 [ T0 T1 T2 T3 ].
Hint Unfold upaco4_2_1.

Section Arg4_3_def.
Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable gf_0 gf_1 gf_2 : rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].
Implicit Arguments gf_2 [].

CoInductive paco4_3_0( r_0 r_1 r_2: rel4 T0 T1 T2 T3) x0 x1 x2 x3 : Prop :=
| paco4_3_0_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <4= (paco4_3_0 r_0 r_1 r_2 \4/ r_0))
    (LE : pco_1 <4= (paco4_3_1 r_0 r_1 r_2 \4/ r_1))
    (LE : pco_2 <4= (paco4_3_2 r_0 r_1 r_2 \4/ r_2))
    (SIM: gf_0 pco_0 pco_1 pco_2 x0 x1 x2 x3)
with paco4_3_1( r_0 r_1 r_2: rel4 T0 T1 T2 T3) x0 x1 x2 x3 : Prop :=
| paco4_3_1_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <4= (paco4_3_0 r_0 r_1 r_2 \4/ r_0))
    (LE : pco_1 <4= (paco4_3_1 r_0 r_1 r_2 \4/ r_1))
    (LE : pco_2 <4= (paco4_3_2 r_0 r_1 r_2 \4/ r_2))
    (SIM: gf_1 pco_0 pco_1 pco_2 x0 x1 x2 x3)
with paco4_3_2( r_0 r_1 r_2: rel4 T0 T1 T2 T3) x0 x1 x2 x3 : Prop :=
| paco4_3_2_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <4= (paco4_3_0 r_0 r_1 r_2 \4/ r_0))
    (LE : pco_1 <4= (paco4_3_1 r_0 r_1 r_2 \4/ r_1))
    (LE : pco_2 <4= (paco4_3_2 r_0 r_1 r_2 \4/ r_2))
    (SIM: gf_2 pco_0 pco_1 pco_2 x0 x1 x2 x3)
.
Definition upaco4_3_0( r_0 r_1 r_2: rel4 T0 T1 T2 T3) := paco4_3_0 r_0 r_1 r_2 \4/ r_0.
Definition upaco4_3_1( r_0 r_1 r_2: rel4 T0 T1 T2 T3) := paco4_3_1 r_0 r_1 r_2 \4/ r_1.
Definition upaco4_3_2( r_0 r_1 r_2: rel4 T0 T1 T2 T3) := paco4_3_2 r_0 r_1 r_2 \4/ r_2.
End Arg4_3_def.
Implicit Arguments paco4_3_0 [ T0 T1 T2 T3 ].
Implicit Arguments upaco4_3_0 [ T0 T1 T2 T3 ].
Hint Unfold upaco4_3_0.
Implicit Arguments paco4_3_1 [ T0 T1 T2 T3 ].
Implicit Arguments upaco4_3_1 [ T0 T1 T2 T3 ].
Hint Unfold upaco4_3_1.
Implicit Arguments paco4_3_2 [ T0 T1 T2 T3 ].
Implicit Arguments upaco4_3_2 [ T0 T1 T2 T3 ].
Hint Unfold upaco4_3_2.

Section Arg5_def.
Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable gf : rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4.
Implicit Arguments gf [].

CoInductive paco5( r: rel5 T0 T1 T2 T3 T4) x0 x1 x2 x3 x4 : Prop :=
| paco5_pfold pco
    (LE : pco <5= (paco5 r \5/ r))
    (SIM: gf pco x0 x1 x2 x3 x4)
.
Definition upaco5( r: rel5 T0 T1 T2 T3 T4) := paco5 r \5/ r.
End Arg5_def.
Implicit Arguments paco5 [ T0 T1 T2 T3 T4 ].
Implicit Arguments upaco5 [ T0 T1 T2 T3 T4 ].
Hint Unfold upaco5.

Section Arg5_2_def.
Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable gf_0 gf_1 : rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].

CoInductive paco5_2_0( r_0 r_1: rel5 T0 T1 T2 T3 T4) x0 x1 x2 x3 x4 : Prop :=
| paco5_2_0_pfold pco_0 pco_1
    (LE : pco_0 <5= (paco5_2_0 r_0 r_1 \5/ r_0))
    (LE : pco_1 <5= (paco5_2_1 r_0 r_1 \5/ r_1))
    (SIM: gf_0 pco_0 pco_1 x0 x1 x2 x3 x4)
with paco5_2_1( r_0 r_1: rel5 T0 T1 T2 T3 T4) x0 x1 x2 x3 x4 : Prop :=
| paco5_2_1_pfold pco_0 pco_1
    (LE : pco_0 <5= (paco5_2_0 r_0 r_1 \5/ r_0))
    (LE : pco_1 <5= (paco5_2_1 r_0 r_1 \5/ r_1))
    (SIM: gf_1 pco_0 pco_1 x0 x1 x2 x3 x4)
.
Definition upaco5_2_0( r_0 r_1: rel5 T0 T1 T2 T3 T4) := paco5_2_0 r_0 r_1 \5/ r_0.
Definition upaco5_2_1( r_0 r_1: rel5 T0 T1 T2 T3 T4) := paco5_2_1 r_0 r_1 \5/ r_1.
End Arg5_2_def.
Implicit Arguments paco5_2_0 [ T0 T1 T2 T3 T4 ].
Implicit Arguments upaco5_2_0 [ T0 T1 T2 T3 T4 ].
Hint Unfold upaco5_2_0.
Implicit Arguments paco5_2_1 [ T0 T1 T2 T3 T4 ].
Implicit Arguments upaco5_2_1 [ T0 T1 T2 T3 T4 ].
Hint Unfold upaco5_2_1.

Section Arg5_3_def.
Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable gf_0 gf_1 gf_2 : rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].
Implicit Arguments gf_2 [].

CoInductive paco5_3_0( r_0 r_1 r_2: rel5 T0 T1 T2 T3 T4) x0 x1 x2 x3 x4 : Prop :=
| paco5_3_0_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <5= (paco5_3_0 r_0 r_1 r_2 \5/ r_0))
    (LE : pco_1 <5= (paco5_3_1 r_0 r_1 r_2 \5/ r_1))
    (LE : pco_2 <5= (paco5_3_2 r_0 r_1 r_2 \5/ r_2))
    (SIM: gf_0 pco_0 pco_1 pco_2 x0 x1 x2 x3 x4)
with paco5_3_1( r_0 r_1 r_2: rel5 T0 T1 T2 T3 T4) x0 x1 x2 x3 x4 : Prop :=
| paco5_3_1_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <5= (paco5_3_0 r_0 r_1 r_2 \5/ r_0))
    (LE : pco_1 <5= (paco5_3_1 r_0 r_1 r_2 \5/ r_1))
    (LE : pco_2 <5= (paco5_3_2 r_0 r_1 r_2 \5/ r_2))
    (SIM: gf_1 pco_0 pco_1 pco_2 x0 x1 x2 x3 x4)
with paco5_3_2( r_0 r_1 r_2: rel5 T0 T1 T2 T3 T4) x0 x1 x2 x3 x4 : Prop :=
| paco5_3_2_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <5= (paco5_3_0 r_0 r_1 r_2 \5/ r_0))
    (LE : pco_1 <5= (paco5_3_1 r_0 r_1 r_2 \5/ r_1))
    (LE : pco_2 <5= (paco5_3_2 r_0 r_1 r_2 \5/ r_2))
    (SIM: gf_2 pco_0 pco_1 pco_2 x0 x1 x2 x3 x4)
.
Definition upaco5_3_0( r_0 r_1 r_2: rel5 T0 T1 T2 T3 T4) := paco5_3_0 r_0 r_1 r_2 \5/ r_0.
Definition upaco5_3_1( r_0 r_1 r_2: rel5 T0 T1 T2 T3 T4) := paco5_3_1 r_0 r_1 r_2 \5/ r_1.
Definition upaco5_3_2( r_0 r_1 r_2: rel5 T0 T1 T2 T3 T4) := paco5_3_2 r_0 r_1 r_2 \5/ r_2.
End Arg5_3_def.
Implicit Arguments paco5_3_0 [ T0 T1 T2 T3 T4 ].
Implicit Arguments upaco5_3_0 [ T0 T1 T2 T3 T4 ].
Hint Unfold upaco5_3_0.
Implicit Arguments paco5_3_1 [ T0 T1 T2 T3 T4 ].
Implicit Arguments upaco5_3_1 [ T0 T1 T2 T3 T4 ].
Hint Unfold upaco5_3_1.
Implicit Arguments paco5_3_2 [ T0 T1 T2 T3 T4 ].
Implicit Arguments upaco5_3_2 [ T0 T1 T2 T3 T4 ].
Hint Unfold upaco5_3_2.

Section Arg6_def.
Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable gf : rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5.
Implicit Arguments gf [].

CoInductive paco6( r: rel6 T0 T1 T2 T3 T4 T5) x0 x1 x2 x3 x4 x5 : Prop :=
| paco6_pfold pco
    (LE : pco <6= (paco6 r \6/ r))
    (SIM: gf pco x0 x1 x2 x3 x4 x5)
.
Definition upaco6( r: rel6 T0 T1 T2 T3 T4 T5) := paco6 r \6/ r.
End Arg6_def.
Implicit Arguments paco6 [ T0 T1 T2 T3 T4 T5 ].
Implicit Arguments upaco6 [ T0 T1 T2 T3 T4 T5 ].
Hint Unfold upaco6.

Section Arg6_2_def.
Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable gf_0 gf_1 : rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].

CoInductive paco6_2_0( r_0 r_1: rel6 T0 T1 T2 T3 T4 T5) x0 x1 x2 x3 x4 x5 : Prop :=
| paco6_2_0_pfold pco_0 pco_1
    (LE : pco_0 <6= (paco6_2_0 r_0 r_1 \6/ r_0))
    (LE : pco_1 <6= (paco6_2_1 r_0 r_1 \6/ r_1))
    (SIM: gf_0 pco_0 pco_1 x0 x1 x2 x3 x4 x5)
with paco6_2_1( r_0 r_1: rel6 T0 T1 T2 T3 T4 T5) x0 x1 x2 x3 x4 x5 : Prop :=
| paco6_2_1_pfold pco_0 pco_1
    (LE : pco_0 <6= (paco6_2_0 r_0 r_1 \6/ r_0))
    (LE : pco_1 <6= (paco6_2_1 r_0 r_1 \6/ r_1))
    (SIM: gf_1 pco_0 pco_1 x0 x1 x2 x3 x4 x5)
.
Definition upaco6_2_0( r_0 r_1: rel6 T0 T1 T2 T3 T4 T5) := paco6_2_0 r_0 r_1 \6/ r_0.
Definition upaco6_2_1( r_0 r_1: rel6 T0 T1 T2 T3 T4 T5) := paco6_2_1 r_0 r_1 \6/ r_1.
End Arg6_2_def.
Implicit Arguments paco6_2_0 [ T0 T1 T2 T3 T4 T5 ].
Implicit Arguments upaco6_2_0 [ T0 T1 T2 T3 T4 T5 ].
Hint Unfold upaco6_2_0.
Implicit Arguments paco6_2_1 [ T0 T1 T2 T3 T4 T5 ].
Implicit Arguments upaco6_2_1 [ T0 T1 T2 T3 T4 T5 ].
Hint Unfold upaco6_2_1.

Section Arg6_3_def.
Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable gf_0 gf_1 gf_2 : rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].
Implicit Arguments gf_2 [].

CoInductive paco6_3_0( r_0 r_1 r_2: rel6 T0 T1 T2 T3 T4 T5) x0 x1 x2 x3 x4 x5 : Prop :=
| paco6_3_0_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <6= (paco6_3_0 r_0 r_1 r_2 \6/ r_0))
    (LE : pco_1 <6= (paco6_3_1 r_0 r_1 r_2 \6/ r_1))
    (LE : pco_2 <6= (paco6_3_2 r_0 r_1 r_2 \6/ r_2))
    (SIM: gf_0 pco_0 pco_1 pco_2 x0 x1 x2 x3 x4 x5)
with paco6_3_1( r_0 r_1 r_2: rel6 T0 T1 T2 T3 T4 T5) x0 x1 x2 x3 x4 x5 : Prop :=
| paco6_3_1_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <6= (paco6_3_0 r_0 r_1 r_2 \6/ r_0))
    (LE : pco_1 <6= (paco6_3_1 r_0 r_1 r_2 \6/ r_1))
    (LE : pco_2 <6= (paco6_3_2 r_0 r_1 r_2 \6/ r_2))
    (SIM: gf_1 pco_0 pco_1 pco_2 x0 x1 x2 x3 x4 x5)
with paco6_3_2( r_0 r_1 r_2: rel6 T0 T1 T2 T3 T4 T5) x0 x1 x2 x3 x4 x5 : Prop :=
| paco6_3_2_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <6= (paco6_3_0 r_0 r_1 r_2 \6/ r_0))
    (LE : pco_1 <6= (paco6_3_1 r_0 r_1 r_2 \6/ r_1))
    (LE : pco_2 <6= (paco6_3_2 r_0 r_1 r_2 \6/ r_2))
    (SIM: gf_2 pco_0 pco_1 pco_2 x0 x1 x2 x3 x4 x5)
.
Definition upaco6_3_0( r_0 r_1 r_2: rel6 T0 T1 T2 T3 T4 T5) := paco6_3_0 r_0 r_1 r_2 \6/ r_0.
Definition upaco6_3_1( r_0 r_1 r_2: rel6 T0 T1 T2 T3 T4 T5) := paco6_3_1 r_0 r_1 r_2 \6/ r_1.
Definition upaco6_3_2( r_0 r_1 r_2: rel6 T0 T1 T2 T3 T4 T5) := paco6_3_2 r_0 r_1 r_2 \6/ r_2.
End Arg6_3_def.
Implicit Arguments paco6_3_0 [ T0 T1 T2 T3 T4 T5 ].
Implicit Arguments upaco6_3_0 [ T0 T1 T2 T3 T4 T5 ].
Hint Unfold upaco6_3_0.
Implicit Arguments paco6_3_1 [ T0 T1 T2 T3 T4 T5 ].
Implicit Arguments upaco6_3_1 [ T0 T1 T2 T3 T4 T5 ].
Hint Unfold upaco6_3_1.
Implicit Arguments paco6_3_2 [ T0 T1 T2 T3 T4 T5 ].
Implicit Arguments upaco6_3_2 [ T0 T1 T2 T3 T4 T5 ].
Hint Unfold upaco6_3_2.

Section Arg7_def.
Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable gf : rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6.
Implicit Arguments gf [].

CoInductive paco7( r: rel7 T0 T1 T2 T3 T4 T5 T6) x0 x1 x2 x3 x4 x5 x6 : Prop :=
| paco7_pfold pco
    (LE : pco <7= (paco7 r \7/ r))
    (SIM: gf pco x0 x1 x2 x3 x4 x5 x6)
.
Definition upaco7( r: rel7 T0 T1 T2 T3 T4 T5 T6) := paco7 r \7/ r.
End Arg7_def.
Implicit Arguments paco7 [ T0 T1 T2 T3 T4 T5 T6 ].
Implicit Arguments upaco7 [ T0 T1 T2 T3 T4 T5 T6 ].
Hint Unfold upaco7.

Section Arg7_2_def.
Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable gf_0 gf_1 : rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].

CoInductive paco7_2_0( r_0 r_1: rel7 T0 T1 T2 T3 T4 T5 T6) x0 x1 x2 x3 x4 x5 x6 : Prop :=
| paco7_2_0_pfold pco_0 pco_1
    (LE : pco_0 <7= (paco7_2_0 r_0 r_1 \7/ r_0))
    (LE : pco_1 <7= (paco7_2_1 r_0 r_1 \7/ r_1))
    (SIM: gf_0 pco_0 pco_1 x0 x1 x2 x3 x4 x5 x6)
with paco7_2_1( r_0 r_1: rel7 T0 T1 T2 T3 T4 T5 T6) x0 x1 x2 x3 x4 x5 x6 : Prop :=
| paco7_2_1_pfold pco_0 pco_1
    (LE : pco_0 <7= (paco7_2_0 r_0 r_1 \7/ r_0))
    (LE : pco_1 <7= (paco7_2_1 r_0 r_1 \7/ r_1))
    (SIM: gf_1 pco_0 pco_1 x0 x1 x2 x3 x4 x5 x6)
.
Definition upaco7_2_0( r_0 r_1: rel7 T0 T1 T2 T3 T4 T5 T6) := paco7_2_0 r_0 r_1 \7/ r_0.
Definition upaco7_2_1( r_0 r_1: rel7 T0 T1 T2 T3 T4 T5 T6) := paco7_2_1 r_0 r_1 \7/ r_1.
End Arg7_2_def.
Implicit Arguments paco7_2_0 [ T0 T1 T2 T3 T4 T5 T6 ].
Implicit Arguments upaco7_2_0 [ T0 T1 T2 T3 T4 T5 T6 ].
Hint Unfold upaco7_2_0.
Implicit Arguments paco7_2_1 [ T0 T1 T2 T3 T4 T5 T6 ].
Implicit Arguments upaco7_2_1 [ T0 T1 T2 T3 T4 T5 T6 ].
Hint Unfold upaco7_2_1.

Section Arg7_3_def.
Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable gf_0 gf_1 gf_2 : rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].
Implicit Arguments gf_2 [].

CoInductive paco7_3_0( r_0 r_1 r_2: rel7 T0 T1 T2 T3 T4 T5 T6) x0 x1 x2 x3 x4 x5 x6 : Prop :=
| paco7_3_0_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <7= (paco7_3_0 r_0 r_1 r_2 \7/ r_0))
    (LE : pco_1 <7= (paco7_3_1 r_0 r_1 r_2 \7/ r_1))
    (LE : pco_2 <7= (paco7_3_2 r_0 r_1 r_2 \7/ r_2))
    (SIM: gf_0 pco_0 pco_1 pco_2 x0 x1 x2 x3 x4 x5 x6)
with paco7_3_1( r_0 r_1 r_2: rel7 T0 T1 T2 T3 T4 T5 T6) x0 x1 x2 x3 x4 x5 x6 : Prop :=
| paco7_3_1_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <7= (paco7_3_0 r_0 r_1 r_2 \7/ r_0))
    (LE : pco_1 <7= (paco7_3_1 r_0 r_1 r_2 \7/ r_1))
    (LE : pco_2 <7= (paco7_3_2 r_0 r_1 r_2 \7/ r_2))
    (SIM: gf_1 pco_0 pco_1 pco_2 x0 x1 x2 x3 x4 x5 x6)
with paco7_3_2( r_0 r_1 r_2: rel7 T0 T1 T2 T3 T4 T5 T6) x0 x1 x2 x3 x4 x5 x6 : Prop :=
| paco7_3_2_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <7= (paco7_3_0 r_0 r_1 r_2 \7/ r_0))
    (LE : pco_1 <7= (paco7_3_1 r_0 r_1 r_2 \7/ r_1))
    (LE : pco_2 <7= (paco7_3_2 r_0 r_1 r_2 \7/ r_2))
    (SIM: gf_2 pco_0 pco_1 pco_2 x0 x1 x2 x3 x4 x5 x6)
.
Definition upaco7_3_0( r_0 r_1 r_2: rel7 T0 T1 T2 T3 T4 T5 T6) := paco7_3_0 r_0 r_1 r_2 \7/ r_0.
Definition upaco7_3_1( r_0 r_1 r_2: rel7 T0 T1 T2 T3 T4 T5 T6) := paco7_3_1 r_0 r_1 r_2 \7/ r_1.
Definition upaco7_3_2( r_0 r_1 r_2: rel7 T0 T1 T2 T3 T4 T5 T6) := paco7_3_2 r_0 r_1 r_2 \7/ r_2.
End Arg7_3_def.
Implicit Arguments paco7_3_0 [ T0 T1 T2 T3 T4 T5 T6 ].
Implicit Arguments upaco7_3_0 [ T0 T1 T2 T3 T4 T5 T6 ].
Hint Unfold upaco7_3_0.
Implicit Arguments paco7_3_1 [ T0 T1 T2 T3 T4 T5 T6 ].
Implicit Arguments upaco7_3_1 [ T0 T1 T2 T3 T4 T5 T6 ].
Hint Unfold upaco7_3_1.
Implicit Arguments paco7_3_2 [ T0 T1 T2 T3 T4 T5 T6 ].
Implicit Arguments upaco7_3_2 [ T0 T1 T2 T3 T4 T5 T6 ].
Hint Unfold upaco7_3_2.

Section Arg8_def.
Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable gf : rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7.
Implicit Arguments gf [].

CoInductive paco8( r: rel8 T0 T1 T2 T3 T4 T5 T6 T7) x0 x1 x2 x3 x4 x5 x6 x7 : Prop :=
| paco8_pfold pco
    (LE : pco <8= (paco8 r \8/ r))
    (SIM: gf pco x0 x1 x2 x3 x4 x5 x6 x7)
.
Definition upaco8( r: rel8 T0 T1 T2 T3 T4 T5 T6 T7) := paco8 r \8/ r.
End Arg8_def.
Implicit Arguments paco8 [ T0 T1 T2 T3 T4 T5 T6 T7 ].
Implicit Arguments upaco8 [ T0 T1 T2 T3 T4 T5 T6 T7 ].
Hint Unfold upaco8.

Section Arg8_2_def.
Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable gf_0 gf_1 : rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].

CoInductive paco8_2_0( r_0 r_1: rel8 T0 T1 T2 T3 T4 T5 T6 T7) x0 x1 x2 x3 x4 x5 x6 x7 : Prop :=
| paco8_2_0_pfold pco_0 pco_1
    (LE : pco_0 <8= (paco8_2_0 r_0 r_1 \8/ r_0))
    (LE : pco_1 <8= (paco8_2_1 r_0 r_1 \8/ r_1))
    (SIM: gf_0 pco_0 pco_1 x0 x1 x2 x3 x4 x5 x6 x7)
with paco8_2_1( r_0 r_1: rel8 T0 T1 T2 T3 T4 T5 T6 T7) x0 x1 x2 x3 x4 x5 x6 x7 : Prop :=
| paco8_2_1_pfold pco_0 pco_1
    (LE : pco_0 <8= (paco8_2_0 r_0 r_1 \8/ r_0))
    (LE : pco_1 <8= (paco8_2_1 r_0 r_1 \8/ r_1))
    (SIM: gf_1 pco_0 pco_1 x0 x1 x2 x3 x4 x5 x6 x7)
.
Definition upaco8_2_0( r_0 r_1: rel8 T0 T1 T2 T3 T4 T5 T6 T7) := paco8_2_0 r_0 r_1 \8/ r_0.
Definition upaco8_2_1( r_0 r_1: rel8 T0 T1 T2 T3 T4 T5 T6 T7) := paco8_2_1 r_0 r_1 \8/ r_1.
End Arg8_2_def.
Implicit Arguments paco8_2_0 [ T0 T1 T2 T3 T4 T5 T6 T7 ].
Implicit Arguments upaco8_2_0 [ T0 T1 T2 T3 T4 T5 T6 T7 ].
Hint Unfold upaco8_2_0.
Implicit Arguments paco8_2_1 [ T0 T1 T2 T3 T4 T5 T6 T7 ].
Implicit Arguments upaco8_2_1 [ T0 T1 T2 T3 T4 T5 T6 T7 ].
Hint Unfold upaco8_2_1.

Section Arg8_3_def.
Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable gf_0 gf_1 gf_2 : rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].
Implicit Arguments gf_2 [].

CoInductive paco8_3_0( r_0 r_1 r_2: rel8 T0 T1 T2 T3 T4 T5 T6 T7) x0 x1 x2 x3 x4 x5 x6 x7 : Prop :=
| paco8_3_0_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <8= (paco8_3_0 r_0 r_1 r_2 \8/ r_0))
    (LE : pco_1 <8= (paco8_3_1 r_0 r_1 r_2 \8/ r_1))
    (LE : pco_2 <8= (paco8_3_2 r_0 r_1 r_2 \8/ r_2))
    (SIM: gf_0 pco_0 pco_1 pco_2 x0 x1 x2 x3 x4 x5 x6 x7)
with paco8_3_1( r_0 r_1 r_2: rel8 T0 T1 T2 T3 T4 T5 T6 T7) x0 x1 x2 x3 x4 x5 x6 x7 : Prop :=
| paco8_3_1_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <8= (paco8_3_0 r_0 r_1 r_2 \8/ r_0))
    (LE : pco_1 <8= (paco8_3_1 r_0 r_1 r_2 \8/ r_1))
    (LE : pco_2 <8= (paco8_3_2 r_0 r_1 r_2 \8/ r_2))
    (SIM: gf_1 pco_0 pco_1 pco_2 x0 x1 x2 x3 x4 x5 x6 x7)
with paco8_3_2( r_0 r_1 r_2: rel8 T0 T1 T2 T3 T4 T5 T6 T7) x0 x1 x2 x3 x4 x5 x6 x7 : Prop :=
| paco8_3_2_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <8= (paco8_3_0 r_0 r_1 r_2 \8/ r_0))
    (LE : pco_1 <8= (paco8_3_1 r_0 r_1 r_2 \8/ r_1))
    (LE : pco_2 <8= (paco8_3_2 r_0 r_1 r_2 \8/ r_2))
    (SIM: gf_2 pco_0 pco_1 pco_2 x0 x1 x2 x3 x4 x5 x6 x7)
.
Definition upaco8_3_0( r_0 r_1 r_2: rel8 T0 T1 T2 T3 T4 T5 T6 T7) := paco8_3_0 r_0 r_1 r_2 \8/ r_0.
Definition upaco8_3_1( r_0 r_1 r_2: rel8 T0 T1 T2 T3 T4 T5 T6 T7) := paco8_3_1 r_0 r_1 r_2 \8/ r_1.
Definition upaco8_3_2( r_0 r_1 r_2: rel8 T0 T1 T2 T3 T4 T5 T6 T7) := paco8_3_2 r_0 r_1 r_2 \8/ r_2.
End Arg8_3_def.
Implicit Arguments paco8_3_0 [ T0 T1 T2 T3 T4 T5 T6 T7 ].
Implicit Arguments upaco8_3_0 [ T0 T1 T2 T3 T4 T5 T6 T7 ].
Hint Unfold upaco8_3_0.
Implicit Arguments paco8_3_1 [ T0 T1 T2 T3 T4 T5 T6 T7 ].
Implicit Arguments upaco8_3_1 [ T0 T1 T2 T3 T4 T5 T6 T7 ].
Hint Unfold upaco8_3_1.
Implicit Arguments paco8_3_2 [ T0 T1 T2 T3 T4 T5 T6 T7 ].
Implicit Arguments upaco8_3_2 [ T0 T1 T2 T3 T4 T5 T6 T7 ].
Hint Unfold upaco8_3_2.

Section Arg9_def.
Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable T8 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6), Type.
Variable gf : rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8.
Implicit Arguments gf [].

CoInductive paco9( r: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) x0 x1 x2 x3 x4 x5 x6 x7 x8 : Prop :=
| paco9_pfold pco
    (LE : pco <9= (paco9 r \9/ r))
    (SIM: gf pco x0 x1 x2 x3 x4 x5 x6 x7 x8)
.
Definition upaco9( r: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) := paco9 r \9/ r.
End Arg9_def.
Implicit Arguments paco9 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 ].
Implicit Arguments upaco9 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 ].
Hint Unfold upaco9.

Section Arg9_2_def.
Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable T8 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6), Type.
Variable gf_0 gf_1 : rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].

CoInductive paco9_2_0( r_0 r_1: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) x0 x1 x2 x3 x4 x5 x6 x7 x8 : Prop :=
| paco9_2_0_pfold pco_0 pco_1
    (LE : pco_0 <9= (paco9_2_0 r_0 r_1 \9/ r_0))
    (LE : pco_1 <9= (paco9_2_1 r_0 r_1 \9/ r_1))
    (SIM: gf_0 pco_0 pco_1 x0 x1 x2 x3 x4 x5 x6 x7 x8)
with paco9_2_1( r_0 r_1: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) x0 x1 x2 x3 x4 x5 x6 x7 x8 : Prop :=
| paco9_2_1_pfold pco_0 pco_1
    (LE : pco_0 <9= (paco9_2_0 r_0 r_1 \9/ r_0))
    (LE : pco_1 <9= (paco9_2_1 r_0 r_1 \9/ r_1))
    (SIM: gf_1 pco_0 pco_1 x0 x1 x2 x3 x4 x5 x6 x7 x8)
.
Definition upaco9_2_0( r_0 r_1: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) := paco9_2_0 r_0 r_1 \9/ r_0.
Definition upaco9_2_1( r_0 r_1: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) := paco9_2_1 r_0 r_1 \9/ r_1.
End Arg9_2_def.
Implicit Arguments paco9_2_0 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 ].
Implicit Arguments upaco9_2_0 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 ].
Hint Unfold upaco9_2_0.
Implicit Arguments paco9_2_1 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 ].
Implicit Arguments upaco9_2_1 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 ].
Hint Unfold upaco9_2_1.

Section Arg9_3_def.
Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable T8 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6), Type.
Variable gf_0 gf_1 gf_2 : rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].
Implicit Arguments gf_2 [].

CoInductive paco9_3_0( r_0 r_1 r_2: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) x0 x1 x2 x3 x4 x5 x6 x7 x8 : Prop :=
| paco9_3_0_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <9= (paco9_3_0 r_0 r_1 r_2 \9/ r_0))
    (LE : pco_1 <9= (paco9_3_1 r_0 r_1 r_2 \9/ r_1))
    (LE : pco_2 <9= (paco9_3_2 r_0 r_1 r_2 \9/ r_2))
    (SIM: gf_0 pco_0 pco_1 pco_2 x0 x1 x2 x3 x4 x5 x6 x7 x8)
with paco9_3_1( r_0 r_1 r_2: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) x0 x1 x2 x3 x4 x5 x6 x7 x8 : Prop :=
| paco9_3_1_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <9= (paco9_3_0 r_0 r_1 r_2 \9/ r_0))
    (LE : pco_1 <9= (paco9_3_1 r_0 r_1 r_2 \9/ r_1))
    (LE : pco_2 <9= (paco9_3_2 r_0 r_1 r_2 \9/ r_2))
    (SIM: gf_1 pco_0 pco_1 pco_2 x0 x1 x2 x3 x4 x5 x6 x7 x8)
with paco9_3_2( r_0 r_1 r_2: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) x0 x1 x2 x3 x4 x5 x6 x7 x8 : Prop :=
| paco9_3_2_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <9= (paco9_3_0 r_0 r_1 r_2 \9/ r_0))
    (LE : pco_1 <9= (paco9_3_1 r_0 r_1 r_2 \9/ r_1))
    (LE : pco_2 <9= (paco9_3_2 r_0 r_1 r_2 \9/ r_2))
    (SIM: gf_2 pco_0 pco_1 pco_2 x0 x1 x2 x3 x4 x5 x6 x7 x8)
.
Definition upaco9_3_0( r_0 r_1 r_2: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) := paco9_3_0 r_0 r_1 r_2 \9/ r_0.
Definition upaco9_3_1( r_0 r_1 r_2: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) := paco9_3_1 r_0 r_1 r_2 \9/ r_1.
Definition upaco9_3_2( r_0 r_1 r_2: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) := paco9_3_2 r_0 r_1 r_2 \9/ r_2.
End Arg9_3_def.
Implicit Arguments paco9_3_0 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 ].
Implicit Arguments upaco9_3_0 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 ].
Hint Unfold upaco9_3_0.
Implicit Arguments paco9_3_1 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 ].
Implicit Arguments upaco9_3_1 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 ].
Hint Unfold upaco9_3_1.
Implicit Arguments paco9_3_2 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 ].
Implicit Arguments upaco9_3_2 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 ].
Hint Unfold upaco9_3_2.

Section Arg10_def.
Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable T8 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6), Type.
Variable T9 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7), Type.
Variable gf : rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9.
Implicit Arguments gf [].

CoInductive paco10( r: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Prop :=
| paco10_pfold pco
    (LE : pco <10= (paco10 r \10/ r))
    (SIM: gf pco x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
.
Definition upaco10( r: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) := paco10 r \10/ r.
End Arg10_def.
Implicit Arguments paco10 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Implicit Arguments upaco10 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Hint Unfold upaco10.

Section Arg10_2_def.
Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable T8 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6), Type.
Variable T9 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7), Type.
Variable gf_0 gf_1 : rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].

CoInductive paco10_2_0( r_0 r_1: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Prop :=
| paco10_2_0_pfold pco_0 pco_1
    (LE : pco_0 <10= (paco10_2_0 r_0 r_1 \10/ r_0))
    (LE : pco_1 <10= (paco10_2_1 r_0 r_1 \10/ r_1))
    (SIM: gf_0 pco_0 pco_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
with paco10_2_1( r_0 r_1: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Prop :=
| paco10_2_1_pfold pco_0 pco_1
    (LE : pco_0 <10= (paco10_2_0 r_0 r_1 \10/ r_0))
    (LE : pco_1 <10= (paco10_2_1 r_0 r_1 \10/ r_1))
    (SIM: gf_1 pco_0 pco_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
.
Definition upaco10_2_0( r_0 r_1: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) := paco10_2_0 r_0 r_1 \10/ r_0.
Definition upaco10_2_1( r_0 r_1: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) := paco10_2_1 r_0 r_1 \10/ r_1.
End Arg10_2_def.
Implicit Arguments paco10_2_0 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Implicit Arguments upaco10_2_0 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Hint Unfold upaco10_2_0.
Implicit Arguments paco10_2_1 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Implicit Arguments upaco10_2_1 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Hint Unfold upaco10_2_1.

Section Arg10_3_def.
Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable T8 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6), Type.
Variable T9 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7), Type.
Variable gf_0 gf_1 gf_2 : rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].
Implicit Arguments gf_2 [].

CoInductive paco10_3_0( r_0 r_1 r_2: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Prop :=
| paco10_3_0_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <10= (paco10_3_0 r_0 r_1 r_2 \10/ r_0))
    (LE : pco_1 <10= (paco10_3_1 r_0 r_1 r_2 \10/ r_1))
    (LE : pco_2 <10= (paco10_3_2 r_0 r_1 r_2 \10/ r_2))
    (SIM: gf_0 pco_0 pco_1 pco_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
with paco10_3_1( r_0 r_1 r_2: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Prop :=
| paco10_3_1_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <10= (paco10_3_0 r_0 r_1 r_2 \10/ r_0))
    (LE : pco_1 <10= (paco10_3_1 r_0 r_1 r_2 \10/ r_1))
    (LE : pco_2 <10= (paco10_3_2 r_0 r_1 r_2 \10/ r_2))
    (SIM: gf_1 pco_0 pco_1 pco_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
with paco10_3_2( r_0 r_1 r_2: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Prop :=
| paco10_3_2_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <10= (paco10_3_0 r_0 r_1 r_2 \10/ r_0))
    (LE : pco_1 <10= (paco10_3_1 r_0 r_1 r_2 \10/ r_1))
    (LE : pco_2 <10= (paco10_3_2 r_0 r_1 r_2 \10/ r_2))
    (SIM: gf_2 pco_0 pco_1 pco_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
.
Definition upaco10_3_0( r_0 r_1 r_2: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) := paco10_3_0 r_0 r_1 r_2 \10/ r_0.
Definition upaco10_3_1( r_0 r_1 r_2: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) := paco10_3_1 r_0 r_1 r_2 \10/ r_1.
Definition upaco10_3_2( r_0 r_1 r_2: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) := paco10_3_2 r_0 r_1 r_2 \10/ r_2.
End Arg10_3_def.
Implicit Arguments paco10_3_0 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Implicit Arguments upaco10_3_0 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Hint Unfold upaco10_3_0.
Implicit Arguments paco10_3_1 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Implicit Arguments upaco10_3_1 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Hint Unfold upaco10_3_1.
Implicit Arguments paco10_3_2 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Implicit Arguments upaco10_3_2 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Hint Unfold upaco10_3_2.

Section Arg11_def.
Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable T8 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6), Type.
Variable T9 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7), Type.
Variable T10 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8), Type.
Variable gf : rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10.
Implicit Arguments gf [].

CoInductive paco11( r: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Prop :=
| paco11_pfold pco
    (LE : pco <11= (paco11 r \11/ r))
    (SIM: gf pco x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
.
Definition upaco11( r: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) := paco11 r \11/ r.
End Arg11_def.
Implicit Arguments paco11 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 ].
Implicit Arguments upaco11 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 ].
Hint Unfold upaco11.

Section Arg11_2_def.
Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable T8 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6), Type.
Variable T9 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7), Type.
Variable T10 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8), Type.
Variable gf_0 gf_1 : rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].

CoInductive paco11_2_0( r_0 r_1: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Prop :=
| paco11_2_0_pfold pco_0 pco_1
    (LE : pco_0 <11= (paco11_2_0 r_0 r_1 \11/ r_0))
    (LE : pco_1 <11= (paco11_2_1 r_0 r_1 \11/ r_1))
    (SIM: gf_0 pco_0 pco_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
with paco11_2_1( r_0 r_1: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Prop :=
| paco11_2_1_pfold pco_0 pco_1
    (LE : pco_0 <11= (paco11_2_0 r_0 r_1 \11/ r_0))
    (LE : pco_1 <11= (paco11_2_1 r_0 r_1 \11/ r_1))
    (SIM: gf_1 pco_0 pco_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
.
Definition upaco11_2_0( r_0 r_1: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) := paco11_2_0 r_0 r_1 \11/ r_0.
Definition upaco11_2_1( r_0 r_1: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) := paco11_2_1 r_0 r_1 \11/ r_1.
End Arg11_2_def.
Implicit Arguments paco11_2_0 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 ].
Implicit Arguments upaco11_2_0 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 ].
Hint Unfold upaco11_2_0.
Implicit Arguments paco11_2_1 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 ].
Implicit Arguments upaco11_2_1 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 ].
Hint Unfold upaco11_2_1.

Section Arg11_3_def.
Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable T8 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6), Type.
Variable T9 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7), Type.
Variable T10 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8), Type.
Variable gf_0 gf_1 gf_2 : rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].
Implicit Arguments gf_2 [].

CoInductive paco11_3_0( r_0 r_1 r_2: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Prop :=
| paco11_3_0_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <11= (paco11_3_0 r_0 r_1 r_2 \11/ r_0))
    (LE : pco_1 <11= (paco11_3_1 r_0 r_1 r_2 \11/ r_1))
    (LE : pco_2 <11= (paco11_3_2 r_0 r_1 r_2 \11/ r_2))
    (SIM: gf_0 pco_0 pco_1 pco_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
with paco11_3_1( r_0 r_1 r_2: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Prop :=
| paco11_3_1_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <11= (paco11_3_0 r_0 r_1 r_2 \11/ r_0))
    (LE : pco_1 <11= (paco11_3_1 r_0 r_1 r_2 \11/ r_1))
    (LE : pco_2 <11= (paco11_3_2 r_0 r_1 r_2 \11/ r_2))
    (SIM: gf_1 pco_0 pco_1 pco_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
with paco11_3_2( r_0 r_1 r_2: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Prop :=
| paco11_3_2_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <11= (paco11_3_0 r_0 r_1 r_2 \11/ r_0))
    (LE : pco_1 <11= (paco11_3_1 r_0 r_1 r_2 \11/ r_1))
    (LE : pco_2 <11= (paco11_3_2 r_0 r_1 r_2 \11/ r_2))
    (SIM: gf_2 pco_0 pco_1 pco_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
.
Definition upaco11_3_0( r_0 r_1 r_2: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) := paco11_3_0 r_0 r_1 r_2 \11/ r_0.
Definition upaco11_3_1( r_0 r_1 r_2: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) := paco11_3_1 r_0 r_1 r_2 \11/ r_1.
Definition upaco11_3_2( r_0 r_1 r_2: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) := paco11_3_2 r_0 r_1 r_2 \11/ r_2.
End Arg11_3_def.
Implicit Arguments paco11_3_0 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 ].
Implicit Arguments upaco11_3_0 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 ].
Hint Unfold upaco11_3_0.
Implicit Arguments paco11_3_1 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 ].
Implicit Arguments upaco11_3_1 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 ].
Hint Unfold upaco11_3_1.
Implicit Arguments paco11_3_2 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 ].
Implicit Arguments upaco11_3_2 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 ].
Hint Unfold upaco11_3_2.

Section Arg12_def.
Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable T8 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6), Type.
Variable T9 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7), Type.
Variable T10 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8), Type.
Variable T11 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9), Type.
Variable gf : rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11.
Implicit Arguments gf [].

CoInductive paco12( r: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Prop :=
| paco12_pfold pco
    (LE : pco <12= (paco12 r \12/ r))
    (SIM: gf pco x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
.
Definition upaco12( r: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) := paco12 r \12/ r.
End Arg12_def.
Implicit Arguments paco12 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 ].
Implicit Arguments upaco12 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 ].
Hint Unfold upaco12.

Section Arg12_2_def.
Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable T8 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6), Type.
Variable T9 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7), Type.
Variable T10 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8), Type.
Variable T11 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9), Type.
Variable gf_0 gf_1 : rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].

CoInductive paco12_2_0( r_0 r_1: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Prop :=
| paco12_2_0_pfold pco_0 pco_1
    (LE : pco_0 <12= (paco12_2_0 r_0 r_1 \12/ r_0))
    (LE : pco_1 <12= (paco12_2_1 r_0 r_1 \12/ r_1))
    (SIM: gf_0 pco_0 pco_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
with paco12_2_1( r_0 r_1: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Prop :=
| paco12_2_1_pfold pco_0 pco_1
    (LE : pco_0 <12= (paco12_2_0 r_0 r_1 \12/ r_0))
    (LE : pco_1 <12= (paco12_2_1 r_0 r_1 \12/ r_1))
    (SIM: gf_1 pco_0 pco_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
.
Definition upaco12_2_0( r_0 r_1: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) := paco12_2_0 r_0 r_1 \12/ r_0.
Definition upaco12_2_1( r_0 r_1: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) := paco12_2_1 r_0 r_1 \12/ r_1.
End Arg12_2_def.
Implicit Arguments paco12_2_0 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 ].
Implicit Arguments upaco12_2_0 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 ].
Hint Unfold upaco12_2_0.
Implicit Arguments paco12_2_1 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 ].
Implicit Arguments upaco12_2_1 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 ].
Hint Unfold upaco12_2_1.

Section Arg12_3_def.
Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable T8 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6), Type.
Variable T9 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7), Type.
Variable T10 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8), Type.
Variable T11 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9), Type.
Variable gf_0 gf_1 gf_2 : rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].
Implicit Arguments gf_2 [].

CoInductive paco12_3_0( r_0 r_1 r_2: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Prop :=
| paco12_3_0_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <12= (paco12_3_0 r_0 r_1 r_2 \12/ r_0))
    (LE : pco_1 <12= (paco12_3_1 r_0 r_1 r_2 \12/ r_1))
    (LE : pco_2 <12= (paco12_3_2 r_0 r_1 r_2 \12/ r_2))
    (SIM: gf_0 pco_0 pco_1 pco_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
with paco12_3_1( r_0 r_1 r_2: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Prop :=
| paco12_3_1_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <12= (paco12_3_0 r_0 r_1 r_2 \12/ r_0))
    (LE : pco_1 <12= (paco12_3_1 r_0 r_1 r_2 \12/ r_1))
    (LE : pco_2 <12= (paco12_3_2 r_0 r_1 r_2 \12/ r_2))
    (SIM: gf_1 pco_0 pco_1 pco_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
with paco12_3_2( r_0 r_1 r_2: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Prop :=
| paco12_3_2_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <12= (paco12_3_0 r_0 r_1 r_2 \12/ r_0))
    (LE : pco_1 <12= (paco12_3_1 r_0 r_1 r_2 \12/ r_1))
    (LE : pco_2 <12= (paco12_3_2 r_0 r_1 r_2 \12/ r_2))
    (SIM: gf_2 pco_0 pco_1 pco_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
.
Definition upaco12_3_0( r_0 r_1 r_2: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) := paco12_3_0 r_0 r_1 r_2 \12/ r_0.
Definition upaco12_3_1( r_0 r_1 r_2: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) := paco12_3_1 r_0 r_1 r_2 \12/ r_1.
Definition upaco12_3_2( r_0 r_1 r_2: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) := paco12_3_2 r_0 r_1 r_2 \12/ r_2.
End Arg12_3_def.
Implicit Arguments paco12_3_0 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 ].
Implicit Arguments upaco12_3_0 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 ].
Hint Unfold upaco12_3_0.
Implicit Arguments paco12_3_1 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 ].
Implicit Arguments upaco12_3_1 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 ].
Hint Unfold upaco12_3_1.
Implicit Arguments paco12_3_2 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 ].
Implicit Arguments upaco12_3_2 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 ].
Hint Unfold upaco12_3_2.

Section Arg13_def.
Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable T8 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6), Type.
Variable T9 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7), Type.
Variable T10 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8), Type.
Variable T11 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9), Type.
Variable T12 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10), Type.
Variable gf : rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12.
Implicit Arguments gf [].

CoInductive paco13( r: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Prop :=
| paco13_pfold pco
    (LE : pco <13= (paco13 r \13/ r))
    (SIM: gf pco x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
.
Definition upaco13( r: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) := paco13 r \13/ r.
End Arg13_def.
Implicit Arguments paco13 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 ].
Implicit Arguments upaco13 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 ].
Hint Unfold upaco13.

Section Arg13_2_def.
Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable T8 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6), Type.
Variable T9 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7), Type.
Variable T10 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8), Type.
Variable T11 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9), Type.
Variable T12 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10), Type.
Variable gf_0 gf_1 : rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].

CoInductive paco13_2_0( r_0 r_1: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Prop :=
| paco13_2_0_pfold pco_0 pco_1
    (LE : pco_0 <13= (paco13_2_0 r_0 r_1 \13/ r_0))
    (LE : pco_1 <13= (paco13_2_1 r_0 r_1 \13/ r_1))
    (SIM: gf_0 pco_0 pco_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
with paco13_2_1( r_0 r_1: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Prop :=
| paco13_2_1_pfold pco_0 pco_1
    (LE : pco_0 <13= (paco13_2_0 r_0 r_1 \13/ r_0))
    (LE : pco_1 <13= (paco13_2_1 r_0 r_1 \13/ r_1))
    (SIM: gf_1 pco_0 pco_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
.
Definition upaco13_2_0( r_0 r_1: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) := paco13_2_0 r_0 r_1 \13/ r_0.
Definition upaco13_2_1( r_0 r_1: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) := paco13_2_1 r_0 r_1 \13/ r_1.
End Arg13_2_def.
Implicit Arguments paco13_2_0 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 ].
Implicit Arguments upaco13_2_0 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 ].
Hint Unfold upaco13_2_0.
Implicit Arguments paco13_2_1 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 ].
Implicit Arguments upaco13_2_1 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 ].
Hint Unfold upaco13_2_1.

Section Arg13_3_def.
Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable T8 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6), Type.
Variable T9 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7), Type.
Variable T10 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8), Type.
Variable T11 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9), Type.
Variable T12 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10), Type.
Variable gf_0 gf_1 gf_2 : rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].
Implicit Arguments gf_2 [].

CoInductive paco13_3_0( r_0 r_1 r_2: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Prop :=
| paco13_3_0_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <13= (paco13_3_0 r_0 r_1 r_2 \13/ r_0))
    (LE : pco_1 <13= (paco13_3_1 r_0 r_1 r_2 \13/ r_1))
    (LE : pco_2 <13= (paco13_3_2 r_0 r_1 r_2 \13/ r_2))
    (SIM: gf_0 pco_0 pco_1 pco_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
with paco13_3_1( r_0 r_1 r_2: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Prop :=
| paco13_3_1_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <13= (paco13_3_0 r_0 r_1 r_2 \13/ r_0))
    (LE : pco_1 <13= (paco13_3_1 r_0 r_1 r_2 \13/ r_1))
    (LE : pco_2 <13= (paco13_3_2 r_0 r_1 r_2 \13/ r_2))
    (SIM: gf_1 pco_0 pco_1 pco_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
with paco13_3_2( r_0 r_1 r_2: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Prop :=
| paco13_3_2_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <13= (paco13_3_0 r_0 r_1 r_2 \13/ r_0))
    (LE : pco_1 <13= (paco13_3_1 r_0 r_1 r_2 \13/ r_1))
    (LE : pco_2 <13= (paco13_3_2 r_0 r_1 r_2 \13/ r_2))
    (SIM: gf_2 pco_0 pco_1 pco_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
.
Definition upaco13_3_0( r_0 r_1 r_2: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) := paco13_3_0 r_0 r_1 r_2 \13/ r_0.
Definition upaco13_3_1( r_0 r_1 r_2: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) := paco13_3_1 r_0 r_1 r_2 \13/ r_1.
Definition upaco13_3_2( r_0 r_1 r_2: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) := paco13_3_2 r_0 r_1 r_2 \13/ r_2.
End Arg13_3_def.
Implicit Arguments paco13_3_0 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 ].
Implicit Arguments upaco13_3_0 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 ].
Hint Unfold upaco13_3_0.
Implicit Arguments paco13_3_1 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 ].
Implicit Arguments upaco13_3_1 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 ].
Hint Unfold upaco13_3_1.
Implicit Arguments paco13_3_2 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 ].
Implicit Arguments upaco13_3_2 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 ].
Hint Unfold upaco13_3_2.

Section Arg14_def.
Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable T8 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6), Type.
Variable T9 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7), Type.
Variable T10 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8), Type.
Variable T11 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9), Type.
Variable T12 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10), Type.
Variable T13 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11), Type.
Variable gf : rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13.
Implicit Arguments gf [].

CoInductive paco14( r: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : Prop :=
| paco14_pfold pco
    (LE : pco <14= (paco14 r \14/ r))
    (SIM: gf pco x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
.
Definition upaco14( r: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) := paco14 r \14/ r.
End Arg14_def.
Implicit Arguments paco14 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 ].
Implicit Arguments upaco14 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 ].
Hint Unfold upaco14.

Section Arg14_2_def.
Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable T8 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6), Type.
Variable T9 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7), Type.
Variable T10 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8), Type.
Variable T11 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9), Type.
Variable T12 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10), Type.
Variable T13 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11), Type.
Variable gf_0 gf_1 : rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].

CoInductive paco14_2_0( r_0 r_1: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : Prop :=
| paco14_2_0_pfold pco_0 pco_1
    (LE : pco_0 <14= (paco14_2_0 r_0 r_1 \14/ r_0))
    (LE : pco_1 <14= (paco14_2_1 r_0 r_1 \14/ r_1))
    (SIM: gf_0 pco_0 pco_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
with paco14_2_1( r_0 r_1: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : Prop :=
| paco14_2_1_pfold pco_0 pco_1
    (LE : pco_0 <14= (paco14_2_0 r_0 r_1 \14/ r_0))
    (LE : pco_1 <14= (paco14_2_1 r_0 r_1 \14/ r_1))
    (SIM: gf_1 pco_0 pco_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
.
Definition upaco14_2_0( r_0 r_1: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) := paco14_2_0 r_0 r_1 \14/ r_0.
Definition upaco14_2_1( r_0 r_1: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) := paco14_2_1 r_0 r_1 \14/ r_1.
End Arg14_2_def.
Implicit Arguments paco14_2_0 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 ].
Implicit Arguments upaco14_2_0 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 ].
Hint Unfold upaco14_2_0.
Implicit Arguments paco14_2_1 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 ].
Implicit Arguments upaco14_2_1 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 ].
Hint Unfold upaco14_2_1.

Section Arg14_3_def.
Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable T8 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6), Type.
Variable T9 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7), Type.
Variable T10 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8), Type.
Variable T11 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9), Type.
Variable T12 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10), Type.
Variable T13 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11), Type.
Variable gf_0 gf_1 gf_2 : rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].
Implicit Arguments gf_2 [].

CoInductive paco14_3_0( r_0 r_1 r_2: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : Prop :=
| paco14_3_0_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <14= (paco14_3_0 r_0 r_1 r_2 \14/ r_0))
    (LE : pco_1 <14= (paco14_3_1 r_0 r_1 r_2 \14/ r_1))
    (LE : pco_2 <14= (paco14_3_2 r_0 r_1 r_2 \14/ r_2))
    (SIM: gf_0 pco_0 pco_1 pco_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
with paco14_3_1( r_0 r_1 r_2: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : Prop :=
| paco14_3_1_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <14= (paco14_3_0 r_0 r_1 r_2 \14/ r_0))
    (LE : pco_1 <14= (paco14_3_1 r_0 r_1 r_2 \14/ r_1))
    (LE : pco_2 <14= (paco14_3_2 r_0 r_1 r_2 \14/ r_2))
    (SIM: gf_1 pco_0 pco_1 pco_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
with paco14_3_2( r_0 r_1 r_2: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : Prop :=
| paco14_3_2_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <14= (paco14_3_0 r_0 r_1 r_2 \14/ r_0))
    (LE : pco_1 <14= (paco14_3_1 r_0 r_1 r_2 \14/ r_1))
    (LE : pco_2 <14= (paco14_3_2 r_0 r_1 r_2 \14/ r_2))
    (SIM: gf_2 pco_0 pco_1 pco_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
.
Definition upaco14_3_0( r_0 r_1 r_2: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) := paco14_3_0 r_0 r_1 r_2 \14/ r_0.
Definition upaco14_3_1( r_0 r_1 r_2: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) := paco14_3_1 r_0 r_1 r_2 \14/ r_1.
Definition upaco14_3_2( r_0 r_1 r_2: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) := paco14_3_2 r_0 r_1 r_2 \14/ r_2.
End Arg14_3_def.
Implicit Arguments paco14_3_0 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 ].
Implicit Arguments upaco14_3_0 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 ].
Hint Unfold upaco14_3_0.
Implicit Arguments paco14_3_1 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 ].
Implicit Arguments upaco14_3_1 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 ].
Hint Unfold upaco14_3_1.
Implicit Arguments paco14_3_2 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 ].
Implicit Arguments upaco14_3_2 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 ].
Hint Unfold upaco14_3_2.

Section Arg15_def.
Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable T8 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6), Type.
Variable T9 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7), Type.
Variable T10 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8), Type.
Variable T11 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9), Type.
Variable T12 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10), Type.
Variable T13 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11), Type.
Variable T14 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) (x13: @T13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12), Type.
Variable gf : rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14.
Implicit Arguments gf [].

CoInductive paco15( r: rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : Prop :=
| paco15_pfold pco
    (LE : pco <15= (paco15 r \15/ r))
    (SIM: gf pco x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14)
.
Definition upaco15( r: rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14) := paco15 r \15/ r.
End Arg15_def.
Implicit Arguments paco15 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 ].
Implicit Arguments upaco15 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 ].
Hint Unfold upaco15.

Section Arg15_2_def.
Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable T8 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6), Type.
Variable T9 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7), Type.
Variable T10 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8), Type.
Variable T11 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9), Type.
Variable T12 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10), Type.
Variable T13 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11), Type.
Variable T14 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) (x13: @T13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12), Type.
Variable gf_0 gf_1 : rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].

CoInductive paco15_2_0( r_0 r_1: rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : Prop :=
| paco15_2_0_pfold pco_0 pco_1
    (LE : pco_0 <15= (paco15_2_0 r_0 r_1 \15/ r_0))
    (LE : pco_1 <15= (paco15_2_1 r_0 r_1 \15/ r_1))
    (SIM: gf_0 pco_0 pco_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14)
with paco15_2_1( r_0 r_1: rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : Prop :=
| paco15_2_1_pfold pco_0 pco_1
    (LE : pco_0 <15= (paco15_2_0 r_0 r_1 \15/ r_0))
    (LE : pco_1 <15= (paco15_2_1 r_0 r_1 \15/ r_1))
    (SIM: gf_1 pco_0 pco_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14)
.
Definition upaco15_2_0( r_0 r_1: rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14) := paco15_2_0 r_0 r_1 \15/ r_0.
Definition upaco15_2_1( r_0 r_1: rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14) := paco15_2_1 r_0 r_1 \15/ r_1.
End Arg15_2_def.
Implicit Arguments paco15_2_0 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 ].
Implicit Arguments upaco15_2_0 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 ].
Hint Unfold upaco15_2_0.
Implicit Arguments paco15_2_1 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 ].
Implicit Arguments upaco15_2_1 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 ].
Hint Unfold upaco15_2_1.

Section Arg15_3_def.
Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable T8 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6), Type.
Variable T9 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7), Type.
Variable T10 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8), Type.
Variable T11 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9), Type.
Variable T12 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10), Type.
Variable T13 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11), Type.
Variable T14 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) (x13: @T13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12), Type.
Variable gf_0 gf_1 gf_2 : rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].
Implicit Arguments gf_2 [].

CoInductive paco15_3_0( r_0 r_1 r_2: rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : Prop :=
| paco15_3_0_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <15= (paco15_3_0 r_0 r_1 r_2 \15/ r_0))
    (LE : pco_1 <15= (paco15_3_1 r_0 r_1 r_2 \15/ r_1))
    (LE : pco_2 <15= (paco15_3_2 r_0 r_1 r_2 \15/ r_2))
    (SIM: gf_0 pco_0 pco_1 pco_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14)
with paco15_3_1( r_0 r_1 r_2: rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : Prop :=
| paco15_3_1_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <15= (paco15_3_0 r_0 r_1 r_2 \15/ r_0))
    (LE : pco_1 <15= (paco15_3_1 r_0 r_1 r_2 \15/ r_1))
    (LE : pco_2 <15= (paco15_3_2 r_0 r_1 r_2 \15/ r_2))
    (SIM: gf_1 pco_0 pco_1 pco_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14)
with paco15_3_2( r_0 r_1 r_2: rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : Prop :=
| paco15_3_2_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <15= (paco15_3_0 r_0 r_1 r_2 \15/ r_0))
    (LE : pco_1 <15= (paco15_3_1 r_0 r_1 r_2 \15/ r_1))
    (LE : pco_2 <15= (paco15_3_2 r_0 r_1 r_2 \15/ r_2))
    (SIM: gf_2 pco_0 pco_1 pco_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14)
.
Definition upaco15_3_0( r_0 r_1 r_2: rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14) := paco15_3_0 r_0 r_1 r_2 \15/ r_0.
Definition upaco15_3_1( r_0 r_1 r_2: rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14) := paco15_3_1 r_0 r_1 r_2 \15/ r_1.
Definition upaco15_3_2( r_0 r_1 r_2: rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14) := paco15_3_2 r_0 r_1 r_2 \15/ r_2.
End Arg15_3_def.
Implicit Arguments paco15_3_0 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 ].
Implicit Arguments upaco15_3_0 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 ].
Hint Unfold upaco15_3_0.
Implicit Arguments paco15_3_1 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 ].
Implicit Arguments upaco15_3_1 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 ].
Hint Unfold upaco15_3_1.
Implicit Arguments paco15_3_2 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 ].
Implicit Arguments upaco15_3_2 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 ].
Hint Unfold upaco15_3_2.

