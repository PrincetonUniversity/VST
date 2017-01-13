Load loadpath.
(* make sure to fix loadpath to point to Ssreflect theories *)
Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq
               fintype finfun finset fingraph path.
(* as well as AF libraries on your machine *)
Require Import AlmostFull AFConstructions.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Module TRANS.
Record Sig
  (clause: finType) (* clause is some finite type *)
  (entails: {set clause} -> clause -> bool) (* clauseset s entails clause c *)
  (redund: {set clause} -> clause -> bool) (* clause c is redundant in s *)
  : Type := Make {

(* entailment is closed under set union *)
entailsU: forall (c: clause) (s1 s2: {set clause}),
  entails s1 c -> entails (s1 :|: s2) c;

(* redundancy is closed under set union *)
redundU: forall (c: clause) (s1 s2: {set clause}),
  redund s1 c -> redund (s1 :|: s2) c;

(* a clause can't contribute to its own redundancy *)
redundU2: forall (c: clause) (s: {set clause}),
  redund (c |: s) c -> redund s c;

(* when redundant clause c2 is removed, c remains redundant -- this axiom
   encodes a sort of transitivity condition on the redundancy criteria *)
redundD: forall (c c2: clause) (s: {set clause}),
  redund s c -> redund s c2 -> redund (s :\ c2) c
}.
End TRANS.

(* here we prove that the following transition relation terminates:
Definition trans (s s': clauseset) :=
  [exists c: clause,
    if [&& c \in add s & c \notin s] then s' == c |: s
    else if [&& c \in rem s & c \in s] then s' == s :\ c
         else false].
*)

Module Terminate. Section Terminate.
Variable (clause: finType)
         (entails: {set clause} -> clause -> bool)
         (redund: {set clause} -> clause -> bool)
         (Trans: TRANS.Sig entails redund).

Notation redundU := (TRANS.redundU Trans).
Notation redundU2 := (TRANS.redundU2 Trans).
Notation redundD := (TRANS.redundD Trans).

(*Notation clauseset := ({set clause}).*)
Definition clauseset := set_finType clause.

(* set of clauses addable to s *)
Definition add (s: clauseset) : clauseset :=
  [set c | [&& ~~redund s c &
    [exists s0: clauseset, [&& s0 \subset s & entails s0 c]]]].

(* set of clauses removable from s *)
Definition rem (s: clauseset) : clauseset := [set c | redund s c].

(* the transition relation, expressed as a function to bool *)
Definition trans (s s': clauseset) :=
  [exists c: clause,
    if [&& c \in add s & c \notin s] then s' == c |: s
    else if [&& c \in rem s & c \in s] then s' == s :\ c
         else false].

(* a derivation is the graph induced by the refl. transitive closure of trans *)
Notation deriv := (connect trans).

Lemma deriv0 (s: clauseset) : deriv s s.
Proof. by apply: connect0. Qed.

Lemma deriv1 {s s'' s': clauseset} :
  trans s s'' -> deriv s'' s' -> deriv s s'.
Proof. by move/connect1=>H1 H2; apply: (connect_trans H1 H2). Qed.

Lemma deriv_trans {s s'' s': clauseset} :
  deriv s s'' -> deriv s'' s' -> deriv s s'.
Proof. by move=>H1 H2; apply: (connect_trans H1 H2). Qed.

Definition deriv_plus (s1 s3: clauseset) :=
  [exists s2: clauseset, [&& trans s1 s2 & deriv s2 s3]].

Lemma deriv_plus1 {s s'' s': clauseset} :
  trans s s'' -> deriv s'' s' -> deriv_plus s s'.
Proof. by move=> H1 H2; apply/existsP; exists s''; apply/andP. Qed.

Lemma deriv_plus_trans {s s'' s': clauseset} :
  deriv_plus s s'' -> deriv_plus s'' s' -> deriv_plus s s'.
Proof.
move/existsP=>[x]; move/andP=>[H1 H2]; move/existsP=>[y]; move/andP=>[H3 H4].
apply/existsP; exists x; apply/andP; split=>//.
by apply:(deriv_trans H2 (deriv1 H3 H4)).
Qed.

(* predicate a is closed under "edge" relation e *)
Definition closed {T: finType} (e: rel T) (a: pred T) :=
  forall x y : T, e x y -> a x -> a y.

Lemma closed_connect (T: finType) (e: rel T) (a: pred T) : closed e a ->
  forall x y, connect e x y -> a x -> a y.
Proof.
move=> Ha x y; move/connectP=> [p Hp ->] {y}.
elim: p x Hp => [|y p Hrec] x //=; move/andP=> [Hxp Hp].
by move=> Hax; apply: Hrec=>//; apply: (Ha _ _ Hxp).
Qed.

Lemma remU (c: clause) (s1 s2: clauseset) :
  c \in rem s1 -> c \in rem (s1 :|: s2).
Proof. by rewrite/rem !inE=> H1; apply: redundU. Qed.

(* removability is invariant under the transition relation *)
Lemma rem_trans_closed (c: clause) : closed trans (fun s => c \in rem s).
Proof.
move=> x y Htrans /= Hrem.
move: Htrans; rewrite/trans; move/existsP=> [c2].
case H1: (_ && _).
- by move/eqP=> ->; rewrite setUC; apply: remU.
case H2: (_ && _).
- move/eqP=> ->; rewrite/rem; move: Hrem H2; rewrite/rem !inE=> Hrem.
  by move/andP=> [H2] H3; apply: redundD.
done.
Qed.

(* removability is closed under the derivation relation *)
Lemma rem_deriv_closed (c: clause) : closed deriv (fun s => c \in rem s).
Proof.
rewrite/closed=> x y H1 H2.
by apply: (closed_connect (@rem_trans_closed c) H1).
Qed.

Definition removed (c: clause) {s s'': clauseset} (step: trans s s'') :=
  (c \in s) && (c \notin s'').

(* if a clause was removed at some step, then it was removable *)
Lemma removed_rem (c: clause) (s s'': clauseset) (step: trans s s'') :
  removed c step -> c \in rem s.
Proof.
move/andP=>[H1 H2]; move: step; rewrite/trans; move/existsP=> [x].
case: ifP.
- move/andP=> [H3] H4; move/eqP=> H5; rewrite H5 in H2.
have H6: c \in x |: s by rewrite setUC; apply: set1Ul.
by move: (negP H2).
case: ifP.
- move/andP=> [H4] H5 H3; move/eqP=> H6; rewrite H6 in H2.
rewrite in_setD1 negb_and in H2.
move: (orP H2); case; first by move/negbNE/eqP=> ->.
by move/negP.
done.
Qed.

Definition added (c: clause) {s s'': clauseset} (step: trans s s'') :=
  (c \notin s) && (c \in s'').

Lemma added_add (c: clause) (s s'': clauseset) (step: trans s s'') :
  added c step -> c \in add s.
Proof.
rewrite/added; move/andP=> [H1] H2.
rewrite/trans in step; move: (existsP step)=> [c2].
case H3: (_ && _).
- move/eqP=> H4; rewrite/add inE; apply/andP.
  have H5: c = c2.
  move: H2; rewrite H4 !inE; move/orP; case; first by move/eqP.
  by move: (negP H1).
  split; move: (andP H3); rewrite -H5; rewrite/add inE=>[[H6]] H7.
  + by move: (andP H6)=> [[H8]].
  + by move: (andP H6)=> [[H8]].
case H4: (_ && _).
- move/eqP=> H5; rewrite/add inE; apply/andP.
  have H6: c = c2.
  move: H2; rewrite H5 !inE; move/andP=> [H6] H7.
  by move: (negP H1).
  move: (andP H4); rewrite -H6; rewrite/add inE=>[[H7]] H8.
  by move: (negP H1).
- done.
Qed.

(* removable clauses are not added *)
Lemma rem_not_added (c: clause) (s s'': clauseset) (step: trans s s'') :
  c \in rem s -> ~~added c step.
Proof.
rewrite/rem inE=> H1; apply/negP; move/(@added_add _).
rewrite/add inE; move/andP=> [H2]; move/existsP=> [c2]; move/andP=> [H3] H4.
by move: (negP H2).
Qed.

Lemma removed_not_added (c: clause) (s s'': clauseset) (step: trans s s'') :
  removed c step -> ~~added c step.
Proof. by move/(@removed_rem _); apply: rem_not_added. Qed.

(* main lemma 1: removed clauses are never re-added by a later step *)
Lemma removed_never_added
  (c: clause) (s1 s2 s3 s4: clauseset)
  (step1: trans s1 s2) (trace: deriv s2 s3) (step2: trans s3 s4) :
  removed c step1 -> ~~added c step2.
Proof.
move/(@removed_rem _).
move/(@rem_trans_closed _ _ s2 step1).
move/(@rem_deriv_closed _ _ s3 trace).
by apply: rem_not_added.
Qed.

Lemma removed_notin
  (c: clause) (s s': clauseset) (trace: deriv s s') :
  c \notin s -> c \in rem s -> c \notin s'.
Proof.
move=> H1 H2; move: (connectP trace)=> [p].
elim: p s s' H1 H2 trace; first by move=> s s' H1 H2 trace /= _ ->.
move=> s2 p IH s s' H1 H2 trace /= /andP [H3] H4 Heq; move: Heq trace=> -> trace.
apply: (IH s2)=>//.
 move: H3; rewrite/trans; move/existsP=> [x]; case: ifP.
 move/andP; rewrite/add !inE=> [[H5]]; move: (andP H5)=> [H6].
 rewrite/rem !inE in H2.
 have H7: x <> c by move=> H7; rewrite H7 in H6; apply: (negP H6).
 move=> _ _ /eqP=> ->; apply/negP=> H8; move: (setUP H8); case.
 by rewrite !inE; move/negP; apply=> H9; move: (eqP H9) H7=> ->.
 by move: (negP H1).
 move=> _; case: ifP; last by done.
 move=> _ /eqP=> ->; apply/negP=> H5; apply: (negP H1).
 by rewrite !inE in H5; move: (andP H5)=> [][].
 have H5: deriv s s2 by apply: (deriv1 H3 (deriv0 s2)).
 by apply: (@rem_deriv_closed c s s2 H5).
by apply/connectP; exists p.
Qed.

Lemma redundD2 (c: clause) (s: clauseset) : redund s c -> redund (s :\ c) c.
Proof.
move: (@redundU c s [set c])=> H1.
move: (@redundD c c (s :|: [set c]))=> H2.
move=> H3; move: (H1 H3)=> H4; move: (H2 H4 H4).
by rewrite setDUl setDv setU0.
Qed.

Lemma added_not_rem (c: clause) (s s'': clauseset) (step: trans s s'') :
  added c step -> c \notin rem s''.
Proof.
move=> H1; move: (added_add H1); rewrite/add/rem !inE.
move/andP=>[]; move/negP=>H2; move/existsP=>[x]; move/andP=>[H3] H4.
apply/negP; move: (existsP step)=>[y].
case: ifP.
move/andP=>[H5] H6; move/eqP=> H7; move: H7 step H1=> -> step H1.
have ->: y = c.
- rewrite/added in H1; move: (andP H1)=>{H1} [H7] H8.
  move: H8 H7; rewrite !inE; move/orP; case; first by move/eqP.
  by move=> ?; move/negP.
by move=>Hred; apply: H2; apply: redundU2.
case: ifP.
move/andP=> [H5] H6 _; move/eqP=> H7; move: H7 step H1=> -> step H1.
rewrite/added in H1; move: (andP H1)=>{H1} [H7] H8.
by move: (negP H7) H8; rewrite !inE=> ?; move/andP=>[].
done.
Qed.

(* main lemma 2 as we proved it on paper: if a clause is added to set s,
   then later removed to produce set s', s != s'.

   unfortunately, this lemma is not strong enough to prove our main theorem.
   redund_sub below proves the required (stronger) property. *)
Lemma added_removed_neq
  (c: clause) (s1 s2 s3 s4: clauseset)
  (step1: trans s1 s2) (trace: deriv s2 s3) (step2: trans s3 s4) :
  added c step1 -> removed c step2 -> s1 != s4.
Proof.
move=> H1 H2; move: (added_not_rem H1) (removed_rem H2).
move: H1 H2; rewrite/added/removed; move/andP=> [H3] H4; move/andP=> [H5] H6.
move: H3 H4 H5 H6; rewrite/rem/trans !inE.
move/negP=> H3 H4 H5; move/negP=> H6; move/negP=> H7 H8.
apply/negP=> H9; move: (eqP H9)=> {H9} H9.
move: H9 step1 H3=> -> step1 H3.
move: step2; rewrite/trans; move/existsP=> [x].
case: ifP.
- move/andP=> [H9] H10; move/eqP=> H11; move: H11 H6 step1 H3=> -> H6 step1 H3.
by apply: H3; rewrite !inE; apply/orP; right.
- move=> _; case: ifP.
move/andP=> [H9] H10; move/eqP=> H11; move: H11 H6 step1 H3=> -> H6 step1 H3.
have H11: x = c.
  (*warning: classical argument here depends on decidability of clause equality*)
  + have H12: ~~ (x != c).
  apply/negP=> H12; move: {H12} (negP H12)=> H12.
  apply: H3; apply/setD1P; split=>//.
  by apply/negP=> H13; move: (eqP H13) H12=> ->.
 by move: (negbNE H12); move/eqP.
rewrite H11 in H9 H10 H6 step1 H3; move: (redundD2 H8)=> H12.
have Hadded: added c step1.
 rewrite/added; apply/andP; split=>//.
 by apply/negP=> H13; move: (setD1P H13).
by move: (added_add Hadded); rewrite/add !inE; move/andP=>[]; move/negP.
done.
Qed.

Lemma redundD3 (c c2: clause) (s: clauseset) :
  redund (s :\ c2) c -> redund s c.
Proof.
move=> H1; case H2: (c2 \in s).
have: redund (c2 |: (s :\ c2)) c by rewrite setUC; apply: redundU.
by rewrite setD1K.
have: s :\ c2 = s.
 apply/setP=> x; rewrite in_setD1; case Heq: (x == c2)=>//.
 by move: {Heq} (eqP Heq)=> ->; rewrite H2.
by move=> <-.
Qed.

(*main lemma 2' (redund_sub):
   if c \in s, c is not redundant in s and s -->* s',
   then either:
     (1) c \in s', or
     (2) c \notin s' and there exists a clauseset t such that
     t is a subset of s' but not a subset of the first set s

  as a corollary, we have that when c is added in some step s --> s''
  and s'' -->* s', then s != s'.

  proof sketch:
  since c is added in s --> s'', c is not redundant in s''.
  also, we know that c \notin s and c \in s'' (since c was just added).

  by lemma 2', either c \in s' (in which case s != s' since c \notin s),
  or there exists a clauseset t such that t is a subset of s' but not of s''.
  since s'' = s \cup {c}, t is not a subset of s either, so s != s'.
*)
Lemma redund_sub (c: clause) (s s': clauseset) :
  c \in s -> ~redund s c -> deriv s s' ->
  (c \in s') \/
  (c \notin s' /\ exists t: clauseset, t \subset s' /\ ~t \subset s).
Proof.
move=> H1 H2; move/connectP=> [p] [H3] ->; elim: p c s H1 H2 H3.
by move=> c s H1 H2 H3; left.
move=> s2 p IH c s H1 /= H2 /andP [H3] H4.
move: (H3); rewrite/trans; move/existsP=> [x]; case: ifP.
(*add*)
case Hin: (c \in last s2 p); first by left.
case H5: (x == c); first by move: (eqP H5)=> ->; move/andP=> [H6]; move/negP.
move/andP=> [H6] H7 /eqP=> Heq; move: Heq H3 H4 Hin=> -> H3 H4 Hin.
case H8: (redund (x |: s) c).
- (*redund*) right; split=>//.
have H12: ~redund (x |: s) x.
 move: H6; rewrite/add !inE; move/andP=> [H13].
 by move: (negP H13)=> H14 _ H15; apply: H14; apply: redundU2.
move: (IH x (x |: s) (@setU11 _ x _) H12 H4); case.
move=> Hin2; exists [set x]; split; first by rewrite sub1set.
by rewrite sub1set=> H13; apply: (negP H7).
move=> [H9] [t] [H10] H11.
exists t; split=>//.
by move=> H13; apply: H11; rewrite -(set0U t); apply: setUSS=>//; apply: sub0set.
- (*not redund*) have H9: ~redund (x |: s) c by rewrite H8.
move: (IH c (x |: s) (setU1r _ H1) H9 H4); case; first by rewrite Hin.
move=> [H10] [t] [H11] H12; right; split=>//.
exists t; split=>//.
by move=> H13; apply: H12; rewrite -(set0U t); apply: setUSS=>//; apply: sub0set.
(*remove*)
move=> _; case: ifP; last by done.
move/andP=> [H5] H6; move/eqP=> H7; move: H7 H3 H4=> -> H3 H4.
case Heq: (x == c).
(*c removed: impossible*)
by move: (eqP Heq) H5; rewrite/rem !inE=> ->.
(*x != c removed*)
have H7: ~redund (s :\ x) c by move=> H7; apply: H2; apply: (redundD3 H7).
have H8: c \in (s :\ x).
 apply/setD1P; split=>//.
 by apply/negP; move=> H8; move: (eqP H8) Heq=> ->; rewrite eq_refl.
move: H5; rewrite/rem !inE=> H5.
move: (IH c (s :\ x) H8 H7 H4); case; first by move=> ?; left.
move=>[H9] [t] [H10] H11.
right; split=>//.
exists t.
split=>//.
have H12: x \notin t.
 have H13: x \notin last (s :\ x) p.
  have H14: removed x H3
   by rewrite/removed; apply/andP; split=>//; rewrite setD11.
  have H15: deriv (s :\ x) (last (s :\ x) p) by apply/connectP; exists p.
  apply: (@removed_notin x (s :\ x) (last (s :\ x) p) H15).
  by rewrite setD11.
  by rewrite/rem !inE; apply: redundD2.
 by apply/negP=> H14; apply: (negP H13); move: (subsetP H10); apply.
by move=> H13; apply: H11; rewrite subsetD1; apply/andP; split.
Qed.

Lemma added_trans (c: clause) (s s'': clauseset) (step: trans s s'') :
  added c step -> s'' = (c |: s).
Proof.
rewrite/added; move: step; rewrite/trans; move/existsP=> [x]; case: ifP.
move/andP=> [H1] H2 /eqP=> -> /andP=> [[H3]] H4.
rewrite in_setU1 in H4; move: H4; move/orP; case; first by move/eqP=> ->.
by move: (negP H3).
case: ifP; last by done.
move/andP=> [H1] H2 H3 /eqP=> -> /andP=> [[H4]] H5.
by move: (negP H4) (setD1P H5)=> H6 [H7] H8.
Qed.

Lemma trans_neq (s: clauseset) : ~trans s s.
Proof.
rewrite/trans; move/existsP=> [c]; case: ifP.
move/andP=> [H1]; move/negP=> H2; move/eqP=> H3; move: H3 H2=> -> H2.
by apply: H2; apply: setU11.
move=> _; case: ifP.
move/andP=> [H1] H2; move/eqP=> H3; move: H3 H2=> ->.
by rewrite in_setD1; move/andP=> []; move/eqP.
done.
Qed.

Definition adds (c: clause) (s s': clauseset) (trace: deriv s s') :=
  [&& c \notin s & c \in s'].

Lemma deriv_plus_eq_removed
  (c: clause) (s1 s2: clauseset) (step1: trans s1 s2) (trace: deriv s2 s1) :
  removed c step1 -> adds c trace.
Proof. by rewrite/removed/adds; move/andP=> [H1] H2; apply/andP; split. Qed.

Lemma adds_added (c: clause) (s1 s4: clauseset) (trace: deriv s1 s4) :
  adds c trace ->
  exists s2, exists s3, exists step: trans s2 s3,
    [&& deriv s1 s2, added c step & deriv s3 s4].
Proof.
rewrite/adds; move/andP=> [H1] H2.
move: (connectP trace)=> [p]; move: trace=> _; elim: p s1 s4 H1 H2.
by move=> ? ? H1 H2 /= H3 H4; move: H4 H1 H2=> ->; move/negP.
move=> s p IH s1 s4 H1 /= H2 /andP=> [[H3]] H4 H5; move: H5 H2=> -> H2.
(*FIXME*) generalize H3 as H3'; intro.
move: H3; rewrite{1}/trans; move/existsP=> [x]; case: ifP.
(*add*) move/andP=> [H5] H6; move/eqP=> H7; rewrite H7 in H2 H3' H4.
case Heq: (x == c).
(*c added*) move: {Heq} (eqP Heq)=> Heq; rewrite Heq in H2 H3' H4 H5 H6.
exists s1; exists (c |: s1); exists H3'.
apply/andP; split; first by apply: connect0.
apply/andP; split.
- by rewrite/added; apply/andP; split; last by apply: setU11.
- by apply/connectP; exists p=>//; rewrite H7 Heq.
have H8: c \notin (x |: s1).
 apply/negP=> H8; apply: (negP H1).
 rewrite in_setU1 in H8; move: (orP H8); case; last by done.
 by move/eqP=> Heq2; move: Heq2 Heq=> ->; rewrite eq_refl.
move: (IH _ _ H8 H2 H4 (Coq.Init.Logic.eq_refl _))=> [s2][s3][step].
move/andP=> [H9]; move/andP=> [H10] H11.
exists s2; exists s3; exists step.
apply/andP; split; first by apply: (deriv1 H3' H9).
by rewrite H7; apply/andP; split.
(*remove*)
move=> _; case: ifP.
move/andP=> [H5] H6; move/eqP=> H7; rewrite H7 in H2 H3' H4.
case Heq: (x == c).
(* c removed *) move: {Heq} (eqP Heq)=> Heq; rewrite Heq in H2 H3' H4 H5 H6.
have H8: c \notin (s1 :\ c) by rewrite setD11.
move: (IH _ _ H8 H2 H4 (Coq.Init.Logic.eq_refl _))=> [s2][s3][step].
move/andP=> [H9]; move/andP=> [H10] H11.
exists s2; exists s3; exists step.
apply/andP; split; first by apply: (deriv1 H3' H9).
by rewrite H7 Heq; apply/andP; split.
have H8: c \notin (s1 :\ x).
 rewrite in_setD1; apply/negP=> H8; move: {H8} (andP H8)=> [H8] H9.
 by apply: (negP H1).
move: (IH _ _ H8 H2 H4 (Coq.Init.Logic.eq_refl _))=> [s2][s3][step].
move/andP=> [H9]; move/andP=> [H10] H11.
exists s2; exists s3; exists step.
apply/andP; split; first by apply: (deriv1 H3' H9).
by rewrite H7; apply/andP; split.
done.
Qed.

Definition removes (c: clause) (s s': clauseset) (trace: deriv s s') :=
  [&& c \in s & c \notin s'].

Lemma deriv_plus_eq_added
  (c: clause) (s1 s2: clauseset) (step1: trans s1 s2) (trace: deriv s2 s1) :
  added c step1 -> removes c trace.
Proof. by rewrite/added/removes; move/andP=> [H1] H2; apply/andP; split. Qed.

Definition unique (s: clauseset) :=
  [forall s': clauseset, deriv_plus s s' ==> (s != s')].

(* main theorem: every clauseset s is distinguishable from every s'
   reachable from s under deriv^{+} *)
Lemma deriv_unique : forall (s: clauseset), unique s.
Proof.
move=> s; rewrite/uniq/deriv_plus; apply/forallP=> s'; apply/implyP.
move/existsP=> [s'']; move/andP=> [H1] H2; apply/negP.
move: {H2} (connectP H2)=> [p] H2 ->; elim: p s s'' s' H1 H2=>/=.
by move=> ? ? ? H1 _; move/eqP=> H2; move: H2 H1=> ->; move/trans_neq.
move=> s2 p IH s s'' _ H1 /andP=> [[H2]] H3 Heq.
move: {Heq} (eqP Heq)=> Heq; move: Heq H1=> -> H1.
move: H2; rewrite/trans; move/existsP=> [c]; case: ifP.
move/andP; rewrite/add !inE=> [[H4]] H5 H6.
move: (andP H4)=> [H7] _.
have H8: ~redund (c |: s'') c.
 by move=> H9; move: H7; move/negP; apply; apply: redundU2.
have H9: c \in c |: s'' by apply: setU11.
have H10: deriv (c |: s'') s''.
 move: (eqP H6) H1 H3=> -> H1 H3.
 have H11: deriv (c |: s'') (last (c |: s'') p).
  apply/connectP; exists p=>//.
 by apply: (deriv_trans H11 (deriv1 H1 (deriv0 s''))).
move: (@redund_sub c (c |: s'') s'' H9 H8 H10); case; first by move: (negP H5).
move=> [H11] [t] [H12] H13.
by apply: H13; rewrite -(set0U t); apply: setUSS=>//; apply: sub0set.
move=> _; case: ifP; last by done.
move/andP=> [H2] H4 /eqP=> H5; move: H5 H1 H3=> -> H1 H3.
have H5: deriv (s'' :\ c) s''.
 have H6: deriv (s'' :\ c) (last (s'' :\ c) p) by apply/connectP; exists p.
 by apply: (deriv_trans H6 (deriv1 H1 (deriv0 s''))).
have H6: adds c H5.
 rewrite/adds; apply/andP; split=>//; apply/negP=> H6.
 by rewrite setD11 in H6.
move: (adds_added H6)=> [s3] [s4] [step] /andP [H7] /andP [H8] H9.
have H10: trans s'' (s'' :\ c).
 rewrite/trans; apply/existsP; exists c; case: ifP.
 by move/andP=> [_] /negP=> H10.
 move=> _; case: ifP; first by done.
 by move/andP=> H10; exfalso; apply: H10; split.
have H11: removed c H10.
 rewrite/removed; apply/andP; split=>//.
 by apply/negP; rewrite setD11.
by apply: (negP (removed_never_added H7 step H11)).
Qed.

(* here's a different characterization based on sequences of states *)

Lemma path_take {T: finType} (e: rel T) (x y: T) (p: seq T) (n: nat) :
  path e x p -> path e x (take n p).
Proof.
elim: n x p; first by move=> x p; rewrite take0.
move=> n IH x p H1; elim: p H1=> // z s2 H1 /=; move/andP=> [H2] H3.
by apply/andP; split=> //; apply: IH.
Qed.

Lemma last_take {T: finType} (e: rel T) (x y: T) (p p1 p2: seq T) :
  x \in p -> last y (take ((index x p).+1) p) = x.
Proof.
elim: p x y=> //.
move=> z p IH x y H1 /=.
case Heq: (z == x); first by rewrite take0=> /=; move: (eqP Heq).
rewrite IH=> //.
move: H1; rewrite in_cons; move/orP; case=> //.
by move/eqP=> H2; move: H2 Heq=> ->; rewrite eq_refl.
Qed.

Lemma subpath_prop {T: finType} (e: rel T) (x y: T) (p: seq T) :
  path e x p -> y \in p ->
  exists p', path e x p' /\ last x p' = y.
Proof.
move=> H1 H2; exists (take ((index y p).+1) p); split.
- by apply: path_take.
- by rewrite last_take.
Qed.

(* "path trans s p" means the sequence (s :: p) defines a graph with
   edges related by trans.  uniq is pairwise difference. *)

Lemma deriv_unique2 : forall (s: clauseset) (p: seq clauseset),
  path trans s p -> uniq (s :: p).
Proof.
move=> s p H1.
elim: p s H1=>//.
move=> s2 p IH s /= /andP [H1] H2.
apply/andP; split.
apply/negP; rewrite in_cons=> H3.
move: (orP H3); case.
move/eqP=> H4; rewrite H4 in H1.
move: (deriv_unique s2); rewrite/unique; move/forallP/(_ s2).
by move/implyP; move/(_ (deriv_plus1 H1 (deriv0 s2))); move/negP.
move=> H4; move: (subpath_prop H2 H4)=> [p'] [H5] H6.
have H7: deriv_plus s s.
 have H7: deriv s2 s by apply/connectP; exists p'.
 by apply: (deriv_plus1 H1 H7).
move: (deriv_unique s); move/forallP/(_ s)/implyP/(_ H7)/negP.
by rewrite eq_refl.
by apply: (IH s2 H2).
Qed.

(* now we prove that equality on clausesets is AF *)

(* cs2id: an injection from clausesets to values of type Finite #|clauseset|.
   enum_rank produces a value of type 'I_(#|clauseset|), where 'I_n is the
   type of ordinals < n. *)
Program Definition cs2id (s: clauseset) : Finite #|clauseset| :=
  @FinIntro #|clauseset| (enum_rank s) _.
Next Obligation. by apply: (ltP (ltn_ord (enum_rank s))). Qed.

Lemma af_rank_clauseset : almost_full (@eq_op clauseset).
move: (af_cofmap cs2id (af_finite #|clauseset|)).
rewrite/almost_full; move=> [p] H1; exists p.
apply: (@sec_strengthen _ _ (fun x y => eq_fin (cs2id x) (cs2id y)))=> // x y.
rewrite/cs2id=> /=; case=> H2; apply/eqP.
by apply: enum_rank_inj; apply: (ord_inj H2).
Qed.

Lemma clos_trans_1n_deriv_plus (s1 s2: clauseset) :
  Relation_Operators.clos_trans_1n clauseset
    (fun s s' : clauseset => trans s s') s1 s2 ->
  deriv_plus s1 s2.
Proof.
elim=> x y; first by move=> H1; apply/existsP; exists y; apply/andP.
move=> z H1 H2; rewrite/deriv_plus; move/existsP=> [w] /andP [H3] H4.
apply/existsP; exists y; apply/andP; split=> //.
by apply: (deriv1 H3 H4).
Qed.

Lemma wf_trans : well_founded trans.
Proof.
elim: af_rank_clauseset=> p H1; apply: (wf_from_af _ H1).
move=> x y [H2] /eqP H3; move: (clos_trans_1n_deriv_plus H2)=> H4.
move: (deriv_unique x); rewrite/unique; move/forallP /(_ y).
by move/implyP /(_ H4); rewrite H3; move/negP.
Qed.

End Terminate. End Terminate.

(* Here we specialize the termination proof to the redundancy relation used in,
   e.g., Nieuwenhuis and Rubio, "Paramodulation-based theorem proving". *)

Require Import ordtype.

Section Ordered.
Variable clause: finType.
(* The entailment relation should satisfy the following two properties. *)
Variable entails: {set clause} -> clause -> bool.
(* entails is closed under set union *)
Variable entailsU:
  forall c s1 s2,
  entails s1 c -> entails (s1 :|: s2) c.
(* entails satisfies a sort of "cut" property *)
Variable entailsT:
  forall c d s1 s2,
  entails s2 d -> entails (d |: s1) c -> entails (s1 :|: s2) c.

Notation clauseset := ({set clause}).

(* define an ord instance for the clause type *)
Definition clause_ordMixin := [fin_ordMixin of clause].
Canonical Structure clause_ordType := OrdType clause clause_ordMixin.

Definition smaller_than (s: clauseset) (c: clause) := [set d in s | ord d c].

(* c is redundant in S when {d in S | d < c} |= c *)
Definition redund (s: clauseset) (c: clause) := entails (smaller_than s c) c.

Lemma redundU c s1 s2 : redund s1 c -> redund (s1 :|: s2) c.
Proof.
rewrite/redund/smaller_than.
have H1: [set d in s1 | ord d c] \subset [set d in s1 :|: s2 | ord d c].
 apply/subsetP=> x; rewrite !inE; move/andP=> [H1] H2; apply/andP; split=> //.
 by apply/orP; left.
by move: (setUidPr H1)=> <-; apply: entailsU.
Qed.

Lemma redundU2 c s : redund (c |: s) c -> redund s c.
Proof.
rewrite/redund/smaller_than.
have H1: [set d in c |: s | ord d c] \subset [set d in s | ord d c].
 apply/subsetP=> x; rewrite !inE; move/andP=> [H1] H2; apply/andP; split=> //.
 move: (orP H1); case=> //.
 move/eqP=> H3; move: H3 H2=> -> H2.
 by move: (@irr clause_ordType); move/(_ c); rewrite H2.
by move: (setUidPr H1)=> <-; apply: entailsU.
Qed.

Lemma redundD c c2 s : redund s c -> redund s c2 -> redund (s :\ c2) c.
Proof.
rewrite/redund/smaller_than.
case Hin: (c2 \in s).
case Hord: (ord c2 c).
(*c2 \in s /\ c2 < c*)
move=> H1 H2.
have H3: [set d in s | ord d c2] \subset [set d in s :\ c2 | ord d c].
 apply/subsetP=> x; rewrite !inE; move/andP=> [H3] H4; apply/andP; split=> //.
 apply/andP; split=> //.
 apply/negP=> Heq; move: (eqP Heq) H4=> -> H4.
 by move: (@irr clause_ordType); move/(_ c2); rewrite H4.
 by move: (@trans clause_ordType); move/(_ c2 x c H4 Hord).
have H4: [set d in s | ord d c] = (c2 |: [set d in s :\ c2 | ord d c]).
 apply/eqP; rewrite eqEsubset; apply/andP; split.
 apply/subsetP=> x; rewrite !inE; move/andP=> [H4] H5.
 case Heq: (x == c2); first by apply/orP; left.
 by apply/orP; right; apply/andP.
 apply/subsetP=> x; rewrite !inE; move/orP; case.
 by move/eqP=> ->; apply/andP; split.
 by move/andP=> [H4] H5; move: {H4} (andP H4)=> [H4] H6; apply/andP; split.
by rewrite H4 in H1; move: (entailsT H2 H1); move: (setUidPl H3)=> ->.
(*c2 \in s /\ c2 >= c*)
have H1: [set d in s :\ c2 | ord d c] = [set d in s | ord d c].
 apply/eqP; rewrite eqEsubset; apply/andP; split.
 apply/subsetP=> x; rewrite !inE; move/andP=> [H1] H2.
 by move: {H1} (andP H1)=> [H3] H4; apply/andP.
 apply/subsetP=> x; rewrite !inE; move/andP=> [H1] H2.
 apply/andP; split=> //; apply/andP; split=> //.
 by apply/negP=> H3; move: (eqP H3) Hord=> <-; rewrite H2.
by rewrite H1.
(*c2 \notin s /\ c2 >= c*)
have H1: s :\ c2 = s.
 apply/eqP; rewrite eqEsubset; apply/andP; split.
 by apply/subsetP=> x; rewrite !inE; move/andP=> [H1] H2.
 apply/subsetP=> x; rewrite !inE=> H1; apply/andP; split=> //.
 by apply/negP=> H3; move: (eqP H3) H1=> ->; rewrite Hin.
by rewrite H1.
Qed.

Definition Trans := TRANS.Make entailsU redundU redundU2 redundD.

Notation trans := (Terminate.trans entails redund).

Lemma wf_trans : well_founded trans.
Proof. by apply: Terminate.wf_trans; apply: Trans. Qed.

End Ordered.


