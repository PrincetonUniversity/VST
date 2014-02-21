Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Bool.
Require Import Zbool.
Require Import BinPos. 

Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Values.
Require Import compcert.lib.Maps.

Require Import msl.Axioms.

Require Import sepcomp.StructuredInjections.
Require Import sepcomp.mem_lemmas.
Require Import sepcomp.effect_simulations.
Require Import sepcomp.pred_lemmas.
Require Import sepcomp.seq_lemmas.
Require Import sepcomp.inj_lemmas.

(* nwp = no wild pointers *)

Definition nwp_aux m (IN OUT : block -> bool) :=
  forall b ofs, 
  IN b -> 
  Mem.perm m b ofs Cur Readable -> 
  forall b' ofs' n, 
    ZMap.get ofs (Mem.mem_contents m) !! b = Pointer b' ofs' n -> 
    OUT b'.

Definition nwp m := [fun bs => nwp_aux m bs bs].

Lemma nwp_REACH_closed1 bs m : 
  nwp m bs -> 
  REACH_closed m bs.
Proof.
move=> A; rewrite/REACH_closed=> b; rewrite REACHAX=> [][]L B.
elim: L b B=> //; first by move=> b; rewrite reach_reach'.
move=> [b' ofs'] L' IH b; rewrite reach_reach'=> /=.
move: {A}(A b' ofs').
case: (ZMap.get _ _ !! _)=> // b'' n n' A []B []C.
rewrite -reach_reach'; move/(IH _)=> D.
by move: (A D C b'' n n' erefl); rewrite -B.
Qed.

Lemma nwp_REACH_closed2 bs m : 
  REACH_closed m bs -> 
  nwp m bs.
Proof.
rewrite/REACH_closed=> A b ofs B C b' ofs' n D; apply: A.
by rewrite REACHAX; exists [:: (b,ofs)]; rewrite reach_reach' /= D.
Qed.

Lemma REACH_closedP bs m : REACH_closed m bs <-> nwp m bs.
Proof.
split; first by apply: nwp_REACH_closed2.
by apply: nwp_REACH_closed1.
Qed.

(* nwp_aux is invariant over disjoint memory updates -- phi1 is the frame *)

Lemma nwp_aux_update phi1 phi2 m m' : 
  (forall b, phi2 b=true -> Mem.valid_block m b) -> 
  nwp_aux m phi2 (fun b => phi1 b || phi2 b) -> 
  Mem.unchanged_on (fun b ofs => phi2 b) m m' -> 
  nwp_aux m' phi1 (fun b => phi1 b || phi2 b) -> 
  nwp_aux m' phi2 (fun b => phi1 b || phi2 b).
Proof.
move=> val A unch C b ofs D E b' ofs' n F.
have G: Mem.perm m b ofs Cur Readable.
  by case: unch; move/(_ b ofs Cur Readable D (val _ D))=> ->.
apply: (A b ofs D G b' ofs' n).
by case: unch=> _; move/(_ _ _ D G)=> <-.
Qed.

Lemma nwp_aux_pre phi1 phi1' phi2 m :
  {subset phi1' <= phi1} -> 
  nwp_aux m phi1 phi2 -> 
  nwp_aux m phi1' phi2.
Proof.
move=> sub A b ofs B C b' ofs' n D.
by move: (sub _ B); move/(A b ofs); move/(_ C b' ofs' n D).
Qed.

Lemma nwp_aux_post phi1 phi2 phi2' m :
  {subset phi2 <= phi2'} -> 
  nwp_aux m phi1 phi2 -> 
  nwp_aux m phi1 phi2'.
Proof.
move=> sub A b ofs B C b' ofs' n D.
by apply: sub; apply: (A _ _ B C b' ofs' n D).
Qed.

Lemma nwp_unchanged_on m m' bs : 
  nwp m bs -> 
  mem_forward m m' -> 
  Mem.unchanged_on (fun b ofs => bs b) m m' -> 
  (forall b, bs b -> Mem.valid_block m b) ->
  nwp m' bs.
Proof.
by move=> A B C D; apply nwp_aux_update 
  with (phi1 := fun b => false) (phi2 := bs) (m := m).
Qed.

Lemma join_sm_REACH_closed mu1 mu1' mu2 m1 m1' : 
  Mem.unchanged_on (fun b ofs => 
    locBlocksSrc mu2 b && frgnBlocksSrc mu1 b=false) m1 m1' -> 
  intern_incr mu1 mu1' -> 
  REACH_closed m1 (vis (join_sm mu1 mu2)) ->
  REACH_closed m1' (vis mu1') ->
  REACH_closed m1' (vis (join_sm mu1' mu2)).
Proof.
rewrite !REACH_closedP.
move=> unch incr X Y.
move=> b ofs A B b' ofs' n C.
move: A X Y.
rewrite/vis.
rewrite/join_sm/=/in_mem/=.
move/orP.
case.
move/orP.
case.
move=> A X Y.
move: (Y b ofs).
rewrite A=> /=.
move/(_ erefl B _ _ _ C).
move/orP.
case.
by move=> ->.
move=> D.
move: (X b ofs).
Abort. (*TODO*)

  