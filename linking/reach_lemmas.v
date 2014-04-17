Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Bool.
Require Import Zbool.
Require Import BinPos. 
Require Import eq_dec.

Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Values.
Require Import compcert.lib.Maps.

Require Import msl.Axioms.

Require Import linking.sepcomp. Import SepComp.

Require Import linking.pred_lemmas.
Require Import linking.seq_lemmas.
Require Import linking.inj_lemmas.
Require Import linking.join_sm.

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
  (forall b, 
     frgnBlocksSrc mu1 b -> 
     locBlocksSrc mu2 b || frgnBlocksSrc mu2 b) -> 
  intern_incr mu1 mu1' -> 
  smvalid_src mu2 m1 -> 
  REACH_closed m1 (vis (join_sm mu1 mu2)) ->
  REACH_closed m1' (vis mu1') ->
  REACH_closed m1' (vis (join_sm mu1' mu2)).
Proof.
rewrite !REACH_closedP.
move=> A contain B valid.
rewrite/vis/join_sm/=/in_mem/= => C D.
set phi1 := (fun b => 
  locBlocksSrc mu1 b || frgnBlocksSrc mu1 b).
set phi1' := (fun b => 
  locBlocksSrc mu1' b || frgnBlocksSrc mu1 b).
set phi2 := (fun b => locBlocksSrc mu2 b && ~~frgnBlocksSrc mu1 b).
have val: forall b, phi2 b = true -> Mem.valid_block m1 b. 
  rewrite/phi2=> b; move/andP=> []X Y.  
  by move: (valid b); rewrite/DOM/DomSrc X; apply.
set phi0 := fun b => locBlocksSrc mu1 b || locBlocksSrc mu2 b
               || frgnBlocksSrc mu1 b && frgnBlocksSrc mu2 b.
have sub: forall b, phi1 b = true -> phi1' b = true.
  rewrite/phi1/phi1'=> b; case/orP=> X.
  by case: B=> _ []_ []; move/(_ b); rewrite X=> Y _; rewrite Y.
  by rewrite X; apply/orP; right.
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
have eq: (frgnBlocksSrc mu1=frgnBlocksSrc mu1'). 
  by case: B=> _ []_ []_ []_ []_ []_ []->.
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

Lemma join_sm_REACH_closed' mu1 mu1' mu2 m1 m1' : 
  DisjointLS mu1 mu2 -> 
  Mem.unchanged_on (fun b ofs => vis mu1 b = false) m1 m1' -> 
  (forall b, 
     frgnBlocksSrc mu1 b -> 
     locBlocksSrc mu2 b || frgnBlocksSrc mu2 b) -> 
  intern_incr mu1 mu1' -> 
  smvalid_src mu2 m1 -> 
  REACH_closed m1 (vis (join_sm mu1 mu2)) ->
  REACH_closed m1' (vis mu1') ->
  REACH_closed m1' (vis (join_sm mu1' mu2)).
Proof.
move=> A B C D E F G.
have unch: 
  Mem.unchanged_on (fun b ofs => 
    locBlocksSrc mu2 b && ~~frgnBlocksSrc mu1 b) m1 m1'.
  apply mem_unchanged_on_sub with (Q:=(fun b ofs => vis mu1 b=false))=> //.
  move=> b _; rewrite/vis.
  case H: (locBlocksSrc mu2 b)=> //=.
  case I: (frgnBlocksSrc mu1 b)=> //=.                                   
  move: A; move/(DisjointP _); move/(_ b); rewrite H.
  by case=> //; case: (locBlocksSrc mu1 b).
by apply: (join_sm_REACH_closed unch C D E F G).
Qed.

Lemma join_all_REACH_closed 
      (mu_trash mu mu' : Inj.t) (mus : seq Inj.t) m1 m1' : 
  DisjointLS mu mu_trash -> 
  All (DisjointLS mu) [seq Inj.mu x | x <- mus] -> 
  Mem.unchanged_on (fun b ofs => vis mu b = false) m1 m1' -> 
  (forall b, 
     frgnBlocksSrc mu b -> 
     let mu_rest := join_all mu_trash mus 
     in locBlocksSrc mu_rest b || frgnBlocksSrc mu_rest b) -> 
  intern_incr mu mu' -> 
  smvalid_src mu_trash m1 -> 
  All (fun mu0 => smvalid_src mu0 m1) [seq Inj.mu x | x <- mus] -> 
  REACH_closed m1 (vis (join_all mu_trash (mu :: mus))) -> 
  REACH_closed m1' (vis mu') ->
  REACH_closed m1' (vis (join_all mu_trash (mu' :: mus))).
Proof.
move=> /= A B C D E F G H I.
have disj: DisjointLS mu (join_all mu_trash mus). 
  by apply: join_all_disjoint_src; split.
have val: smvalid_src (join_all mu_trash mus) m1. 
  apply: join_all_valid_src=> //.
  by move: G; rewrite -All_comp3.
by apply: (join_sm_REACH_closed' disj C D E val H I).
Qed.

Lemma reach_trans m B L0 L1 b0 ofs0 b1 :
  reach m B (L0 ++ [::(b0,ofs0)]) b1 -> 
  reach m B L1 b0 -> 
  reach m B (L0 ++ [::(b0,ofs0) & L1]) b1.
Proof.
elim: L0 b0 ofs0 b1 L1.
move=> b0 ofs0 b1 L1 /=; inversion 1; subst=> A.
by eapply reach_cons; eauto.
case=> bb ofss L IH b0 ofs0 b1; inversion 1; subst=> /= A.
by eapply reach_cons; eauto.
Qed.

Lemma notin_REACHP m B b : 
  b \notin REACH m B ->
  forall l, ~reach m B l b.
Proof.
move/negP=> H l H2; apply: H.
by rewrite /is_true /in_mem; rewrite /= REACHAX; exists l.
Qed.

Lemma valid_dec m b : Mem.valid_block m b -> valid_block_dec m b.
Proof. by rewrite /is_left; case l: (valid_block_dec m b). Qed.

Lemma valid_dec' m b : valid_block_dec m b -> Mem.valid_block m b.
Proof. by rewrite /is_left; case l: (valid_block_dec m b). Qed.

Section reach_upd.

Variable B : block -> bool.

Variable E : block -> Z -> bool.

Variable m1 m1' : mem.

Variable VIS' : block -> bool.

Variable E_sub : forall b ofs, E b ofs -> VIS' b.    

Variable localloc_sub : {subset freshloc m1 m1' <= VIS'}.

Lemma reach_upd_inE b : 
  b \notin REACH m1 B -> 
  b \in REACH m1' B -> 
  Mem.unchanged_on (fun b ofs => E b ofs=false) m1 m1' -> 
  exists b0 ofs L, [/\ reach m1' B L b, List.In (b0,ofs) L & VIS' b0].
Proof.
rewrite /is_true /in_mem /= => H; rewrite REACHAX=> [][]L rch unch. 
elim: L b H rch.
move=> b H; inversion 1; subst; move: {H}(negP H)=> H.
have H3: forall l, ~ reach m1 B l b.
{ by apply: notin_REACHP; apply/negP; apply: H. }
by elimtype False; apply: (H3 [::]); apply: reach_nil.
case=> b0 ofs0 L IH b H; inversion 1; subst.
have H7: forall l, ~ reach m1 B l b by apply: notin_REACHP.
case get: (ZMap.get ofs0 (Mem.mem_contents m1) !! b0)=> [||b' off' n'].
exists b0,ofs0,[::(b0,ofs0) & L]; split=> //; first by left.
case e: (E b0 ofs0); first by apply: (E_sub e).
case f: (valid_block_dec m1 b0)=> [valid|nvalid].
have H5': Mem.perm m1 b0 ofs0 Cur Readable.
{ case: unch; move/(_ _ _ _ _ e valid); case/(_ Cur Readable)=> E1 E2.
  by move=> _; apply: E2. }
by case: unch=> _; move/(_ _ _ e H5'); rewrite H6 get.
apply: localloc_sub; apply/andP; split=> //.
have X: Mem.valid_block m1' b0.
{ by move: H5; apply: Mem.perm_valid_block. }
by move: X; move/valid_dec.
by apply/negP; move/valid_dec'=> X; clear f; apply: nvalid.
exists b0,ofs0,[::(b0,ofs0) & L]; split=> //; first by left.
case e: (E b0 ofs0); first by apply: (E_sub e).
case f: (valid_block_dec m1 b0)=> [valid|nvalid].
have H5': Mem.perm m1 b0 ofs0 Cur Readable.
{ case: unch; move/(_ _ _ _ _ e valid); case/(_ Cur Readable)=> E1 E2.
  by move=> _; apply: E2. }
by case: unch=> _; move/(_ _ _ e H5'); rewrite H6 get.
apply: localloc_sub; apply/andP; split=> //.
have X: Mem.valid_block m1' b0.
{ by move: H5; apply: Mem.perm_valid_block. }
by move: X; move/valid_dec.
by apply/negP; move/valid_dec'=> X; clear f; apply: nvalid.
case p: (Mem.perm_dec m1 b0 ofs0 Cur Readable)=> [prm|nprm].
 
{ case e: (eq_dec (b,off) (b',off'))=> [pf|pf].
  inversion pf; subst; clear e pf.
  case f: (REACH m1 B b0).
  move: f; rewrite REACHAX; case=> L0 rch0.
  elimtype False; apply: (H7 [::(b0,ofs0) & L0]).
  by apply: (reach_cons _ _ _ _ _ _ _ _ rch0 prm get).
  have H8: ~~ REACH m1 B b0=true by apply/negP; rewrite f. 
  case: (IH _ H8 H3)=> bM []offM []L0 []rch' inL0 inE.
  exists bM,offM,[::(b0,ofs0) & L0]; split=> //.
  by eapply reach_cons; eauto.
  by right. 

  exists b0,ofs0,[::(b0,ofs0) & L]; split=> //; first by left.
  case f: (E b0 ofs0); first by apply: (E_sub f).
  case g: (valid_block_dec m1 b0)=> [valid|nvalid].
  have H5': Mem.perm m1 b0 ofs0 Cur Readable.
  { case: unch; move/(_ _ _ _ _ f valid); case/(_ Cur Readable)=> E1 E2.
    by move=> _; apply: E2. }
  case: unch=> _; move/(_ _ _ f H5'); rewrite H6 get=> H8.
  by move: pf e; case: H8=> -> -> _ pf; elimtype False; apply: pf.
  apply: localloc_sub; apply/andP; split=> //.
  have X: Mem.valid_block m1' b0.
  { by move: H5; apply: Mem.perm_valid_block. }
  by move: X; move/valid_dec.
  by apply/negP; move/valid_dec'=> X; clear g; apply: nvalid. }

{ exists b0,ofs0,[::(b0,ofs0) & L]; split=> //; first by left.
  case f: (E b0 ofs0); first by apply: (E_sub f).
  case g: (valid_block_dec m1 b0)=> [valid|nvalid].
  have H5': Mem.perm m1 b0 ofs0 Cur Readable.
  { case: unch; move/(_ _ _ _ _ f valid); case/(_ Cur Readable)=> E1 E2.
    by move=> _; apply: E2. }
  by clear p; elimtype False; apply: nprm.
  apply: localloc_sub; apply/andP; split=> //.
  have X: Mem.valid_block m1' b0.
  { by move: H5; apply: Mem.perm_valid_block. }
  by move: X; move/valid_dec.
  by apply/negP; move/valid_dec'=> X; clear g; apply: nvalid. }
Qed.  

Lemma reach_split m X (Y : block -> bool) l1 l2 b0 ofs b : 
  Y b0 ->
  reach m X ((l1 ++ [::(b0,ofs)]) ++ l2) b -> 
  reach m Y (l1 ++ [::(b0,ofs)]) b.
Proof.
elim: l1 b=> //=.
move=> b H; inversion 1; subst; apply: reach_cons; eauto.
by apply: reach_nil.
case=> b1 ofs1 L IH b H; inversion 1; subst.
by apply: reach_cons; eauto.
Qed.

Lemma reach_upd b : 
  b \notin REACH m1 B -> 
  b \in REACH m1' B -> 
  Mem.unchanged_on (fun b ofs => E b ofs=false) m1 m1' -> 
  b \in REACH m1' VIS'.
Proof.
move=> H H2 H3; case: (reach_upd_inE H H2 H3). 
move=> b0 []ofs []L []rch inL inE.
rewrite /in_mem /= /is_true REACHAX.
have [L0 [L1 L_eq]]: exists l0 l1, L = (l0 ++ [::(b0,ofs)]) ++ l1.
{ clear - inL; elim: L inL=> // a L IH /=; case.
  by move=> ->; exists [::],L.
  by case/IH=> l0 []l1 ->; exists [::a & l0],l1. }
exists (L0++[::(b0,ofs)]); move: rch; rewrite L_eq.
by apply: reach_split. 
Qed.

End reach_upd.
  
  