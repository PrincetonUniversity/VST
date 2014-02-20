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

Definition nwp m (bs : block -> bool) :=
  forall b ofs, 
  bs b -> 
  Mem.perm m b ofs Cur Readable -> 
  forall b' ofs' n, 
    ZMap.get ofs (Mem.mem_contents m) !! b = Pointer b' ofs' n -> 
    bs b'.

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

Lemma nwp_unchanged_on m m' bs : 
  nwp m bs -> 
  mem_forward m m' -> 
  Mem.unchanged_on (fun b ofs => bs b) m m' -> 
  (forall b, bs b -> Mem.valid_block m b) ->
  nwp m' bs.
Proof.
move=> A fwd B U b ofs C D b' ofs' n E.
have V: Mem.valid_block m b by move: C; apply: U.
have D': Mem.perm m b ofs Cur Readable.
  by case: B; move/(_ b ofs Cur Readable C V)=> ->.
have E': ZMap.get ofs (Mem.mem_contents m) !! b = Pointer b' ofs' n.
  by case: B=> _; move/(_ b ofs C D')=> <-.
by move: (A b ofs C D' _ _ _ E')=> F.
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

  