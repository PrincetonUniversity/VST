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

(* nwp_aux is invariant over disjoint memory updates -- phi2 is the frame *)

Lemma nwp_aux_pre phi1 phi1' phi2 m :
  nwp_aux m phi1 phi2 -> 
  {subset phi1' <= phi1} -> 
  nwp_aux m phi1' phi2.
Proof.
move=> A sub b ofs B C b' ofs' n D.
by move: (sub _ B); move/(A b ofs); move/(_ C b' ofs' n D).
Qed.

Lemma nwp_aux_post phi1 phi2 phi2' m :
  nwp_aux m phi1 phi2 -> 
  {subset phi2 <= phi2'} -> 
  nwp_aux m phi1 phi2'.
Proof.
move=> A sub b ofs B C b' ofs' n D.
by apply: sub; apply: (A _ _ B C b' ofs' n D).
Qed.

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

Lemma nwp_union phi1 phi2 m : 
  nwp_aux m phi1 (fun b => phi1 b || phi2 b) -> 
  nwp_aux m phi2 (fun b => phi1 b || phi2 b) -> 
  nwp m (fun b => phi1 b || phi2 b).
Proof.
move=> A B b ofs; move/orP; case=> C D b' ofs' n E.
by apply: (A b ofs C D b' ofs' n E).
by apply: (B b ofs C D b' ofs' n E).
Qed.

Lemma nwp_aux_update_spec1 priv1 pub1 priv2 pub2 m m' : 
  let phi1 := fun b => priv1 b || pub1 b || pub2 b in
  let phi2 := fun b => priv2 b in
  (forall b, phi2 b=true -> Mem.valid_block m b) -> 
  nwp m (fun b => phi1 b || phi2 b) -> 
  Mem.unchanged_on (fun b ofs => phi2 b) m m' -> 
  nwp m' phi1 -> 
  nwp m' (fun b => phi1 b || phi2 b).
Proof.
move=> phi1 phi2 A B C D.
have X: nwp_aux m phi2 (fun b : block => phi1 b || phi2 b).
  apply nwp_aux_pre with (phi1 := (fun b => phi1 b || phi2 b))=> //.
  by move=> b; rewrite/in_mem/= => ->; apply/orP; right.
have Y: nwp_aux m' phi1 (fun b : block => phi1 b || phi2 b).
  apply nwp_aux_post with (phi2 := phi1)=> //.
  by move=> b; rewrite/in_mem/= => ->; apply/orP; left.
move: (@nwp_aux_update phi1 phi2 m m' A X C Y)=> E.
by apply: (nwp_union Y E).
Qed.

Lemma nwp_aux_update_spec2 loc1 frgn1 loc2 frgn2 m m' : 
  let phi1 := fun b => loc1 b || frgn1 b || frgn2 b in
  let phi2 := fun b => loc2 b && ~~frgn1 b in
  (forall b, phi2 b=true -> Mem.valid_block m b) -> 
  nwp m (fun b => phi1 b || phi2 b) -> 
  Mem.unchanged_on (fun b ofs => phi2 b) m m' -> 
  nwp m' phi1 -> 
  nwp m' (fun b => phi1 b || phi2 b).
Proof.
move=> phi1 phi2 A B C D.
have X: nwp_aux m phi2 (fun b : block => phi1 b || phi2 b).
  apply nwp_aux_pre with (phi1 := (fun b => phi1 b || phi2 b))=> //.
  by move=> b; rewrite/in_mem/= => ->; apply/orP; right.
have Y: nwp_aux m' phi1 (fun b : block => phi1 b || phi2 b).
  apply nwp_aux_post with (phi2 := phi1)=> //.
  by move=> b; rewrite/in_mem/= => ->; apply/orP; left.
move: (@nwp_aux_update phi1 phi2 m m' A X C Y)=> E.
by apply: (nwp_union Y E).
Qed.

Lemma nwp_aux_update_spec3 phi1 phi1' phi2 m m' : 
  (forall b, phi2 b=true -> Mem.valid_block m b) -> 
  nwp_aux m phi2 (fun b => phi1 b || phi2 b) -> 
  Mem.unchanged_on (fun b ofs => phi2 b) m m' -> 
  (forall b, phi1 b=true -> phi1' b=true) -> 
  nwp_aux m' phi1' (fun b => phi1' b || phi2 b) -> 
  nwp_aux m' phi2 (fun b => phi1' b || phi2 b).
Proof.
move=> A B C D E.
apply: (nwp_aux_update (m:=m))=> //.
apply: (nwp_aux_post (phi2:=(fun b => phi1 b || phi2 b)))=> //.
move=> b; rewrite/in_mem/=; case F: (phi1 b)=> //= X.
by apply/orP; left; apply: (D _ F).
by apply/orP; right.
Qed.

Lemma nwp_aux_update_spec4 loc1 loc1' frgn1 loc2 frgn2 m m' : 
  let phi1 := fun b => loc1 b || frgn1 b || frgn2 b in
  let phi1' := fun b => loc1' b || frgn1 b || frgn2 b in
  let phi2 := fun b => loc2 b && ~~frgn1 b in
  (forall b, phi1 b -> phi1' b) -> 
  (forall b, phi2 b=true -> Mem.valid_block m b) -> 
  nwp m (fun b => phi1 b || phi2 b) -> 
  Mem.unchanged_on (fun b ofs => phi2 b) m m' -> 
  nwp m' phi1' -> 
  nwp m' (fun b => phi1' b || phi2 b).
Proof.
move=> phi1 phi1' phi2 A B C D E.
have X: nwp_aux m phi2 (fun b : block => phi1 b || phi2 b).
  apply nwp_aux_pre with (phi1 := (fun b => phi1 b || phi2 b))=> //.
  by move=> b; rewrite/in_mem/= => ->; apply/orP; right.
have Y: nwp_aux m' phi1' (fun b : block => phi1' b || phi2 b).
  apply nwp_aux_post with (phi2 := phi1')=> //.
  by move=> b; rewrite/in_mem/= => ->; apply/orP; left.
move: (@nwp_aux_update_spec3 phi1 phi1' phi2 m m' B X D A Y)=> F.
by apply: (nwp_union Y F).
Qed.

Lemma nwp_aux_update_spec5 loc1 loc1' frgn1 loc2 frgn2 m m' : 
  let phi1 := fun b => loc1 b || (frgn1 b && frgn2 b) in
  let phi1' := fun b => loc1' b || (frgn1 b && frgn2 b) in
  let phi2 := fun b => loc2 b && ~~frgn1 b in
  (forall b, phi1 b -> phi1' b) -> 
  (forall b, phi2 b=true -> Mem.valid_block m b) -> 
  nwp m (fun b => phi1 b || phi2 b) -> 
  Mem.unchanged_on (fun b ofs => phi2 b) m m' -> 
  nwp m' phi1' -> 
  nwp m' (fun b => phi1' b || phi2 b).
Proof.
move=> phi1 phi1' phi2 A B C D E.
have X: nwp_aux m phi2 (fun b : block => phi1 b || phi2 b).
  apply nwp_aux_pre with (phi1 := (fun b => phi1 b || phi2 b))=> //.
  by move=> b; rewrite/in_mem/= => ->; apply/orP; right.
have Y: nwp_aux m' phi1' (fun b : block => phi1' b || phi2 b).
  apply nwp_aux_post with (phi2 := phi1')=> //.
  by move=> b; rewrite/in_mem/= => ->; apply/orP; left.
move: (@nwp_aux_update_spec3 phi1 phi1' phi2 m m' B X D A Y)=> F.
by apply: (nwp_union Y F).
Qed.

Lemma join_sm_REACH_closed mu1 mu1' mu2 m1 m1' : 
  Mem.unchanged_on (fun b ofs => 
    locBlocksSrc mu2 b && ~~frgnBlocksSrc mu1 b) m1 m1' -> 
  (forall b, frgnBlocksSrc mu1 b -> locBlocksSrc mu2 b || frgnBlocksSrc mu2 b) -> 
  intern_incr mu1 mu1' -> 
  REACH_closed m1 (vis (join_sm mu1 mu2)) ->
  REACH_closed m1' (vis mu1') ->
  REACH_closed m1' (vis (join_sm mu1' mu2)).
Proof.
rewrite !REACH_closedP.
move=> A contain B.
rewrite/vis/join_sm/=/in_mem/= => C D.
set phi1 := (fun b => 
  locBlocksSrc mu1 b || frgnBlocksSrc mu1 b).
set phi1' := (fun b => 
  locBlocksSrc mu1' b || frgnBlocksSrc mu1 b).
set phi2 := (fun b => locBlocksSrc mu2 b && ~~frgnBlocksSrc mu1 b).
have val: forall b, phi2 b = true -> Mem.valid_block m1 b. admit. (*by sm_valid*)
set phi0 := fun b => locBlocksSrc mu1 b || locBlocksSrc mu2 b
               || frgnBlocksSrc mu1 b && frgnBlocksSrc mu2 b.
have sub: forall b, phi1 b = true -> phi1' b = true.
  admit. (*by intern_incr*)
have sub':
  forall b,
    locBlocksSrc mu1 b || locBlocksSrc mu2 b
      || frgnBlocksSrc mu1 b && frgnBlocksSrc mu2 b ->
    locBlocksSrc mu1 b || frgnBlocksSrc mu1 b
      || locBlocksSrc mu2 b && ~~ frgnBlocksSrc mu1 b.
  move=> b.
  case: (locBlocksSrc mu1 b)=> //=.
  case: (locBlocksSrc mu2 b)=> //=.
  case: (frgnBlocksSrc mu1 b)=> //.
  by move/andP=> []->.
have X: nwp_aux m1 phi2 (fun b : block => phi1 b || phi2 b). 
  apply: (nwp_aux_pre (phi1 := phi0)).
  apply: (nwp_aux_post (phi2 := phi0))=> //.
  move=> b; rewrite/phi2/phi0/in_mem/=.
  by move/andP=> []-> _; apply/orP; left; apply/orP; right.
have eq: (frgnBlocksSrc mu1=frgnBlocksSrc mu1'). admit. (*by intern_incr*)
have Y: nwp_aux m1' phi1' (fun b : block => phi1' b || phi2 b).
  apply: (nwp_aux_pre 
    (phi1 := (fun b => locBlocksSrc mu1' b || frgnBlocksSrc mu1' b))).
  apply: (nwp_aux_post 
    (phi2 := (fun b => locBlocksSrc mu1' b || frgnBlocksSrc mu1' b)))=> //.
  by move=> b; rewrite/phi1'/phi2/in_mem/= eq=> ->.
  by move=> b; rewrite/phi1'/in_mem/= eq.
move: (@nwp_aux_update_spec3 phi1 phi1' phi2 m1 m1' val X A sub Y)=> E.
apply: (nwp_aux_pre (phi1 := fun b => phi1' b || phi2 b)).
apply: (nwp_aux_post (phi2 := fun b => phi1' b || phi2 b))=> //.
by apply: nwp_union.
move=> b; rewrite/in_mem/=/phi1'/phi2.
case U: (locBlocksSrc mu1' b)=> //=.
rewrite eq; case V: (frgnBlocksSrc mu1' b)=> //=.
by move=> _; apply: contain; rewrite eq.
move=> b; rewrite/in_mem/=/phi1'/phi2.
case: (locBlocksSrc mu1' b)=> //=.
case: (locBlocksSrc mu2)=> //=.
move=> _.
by case: (frgnBlocksSrc mu1 b).
rewrite eq.
by move/andP=> [] -> _.
Qed.

  