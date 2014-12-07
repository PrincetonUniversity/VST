Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.
Unset Strict Implicit.

Require Import juicy_mem.
Require Import juicy_extspec.

Require Import pos.
Require Import core_semantics_tcs.

Require Import linking. 
Require Import compcert_linking.
Require Import wholeprog_simulations. Import Wholeprog_sim.

(** This file proves that the machine

  J1 >< J2 >< ... >< Jn

is simulated by

  D1 >< D2 >< ... >< Dn

where the Di are module semantics operating on CompCert memories. The
Ji are the `juicified' module semantics that result from lifting the
Di to operate on juicy memories. The lifting itself is done using
`jstep' and `juicy_core_sem', as defined in veric/juicy_extspec. *)

Section erasure.

Variable N : pos.

Variable plt : ident -> option 'I_N.

Variable sems_T : 'I_N -> Modsem.t.

(* The lifting to juicy memories:                                         *)

Definition sems_S (ix : 'I_N) :=
  match sems_T ix with
    Modsem.mk F V genv C s => 
    @linking.Modsem.mk juicy_mem F V genv C (juicy_core_sem s) 
  end.

Notation source := (linking.LinkerSem.coresem juicy_mem_ageable N sems_S plt).

Notation target := (LinkerSem.coresem N sems_T plt).

Lemma C_types_eq ix : linking.Modsem.C (sems_S ix) = Modsem.C (sems_T ix).
Proof. by rewrite /sems_S; case: (sems_T ix). Defined.

(* Beginning here is the definition of the match relation between         *)
(* runtime states of the (juicy and dry) machines.                        *)

Require Import cast.

Definition match_Cs i 
    (c1 : linking.Modsem.C (sems_S i)) (c2 : Modsem.C (sems_T i)) :=
  cast_ty (C_types_eq i) c1 = c2.  

Definition match_Cs' (i1 i2 : 'I_N) (pf : @eq 'I_N i1 i2)
    (c1 : linking.Modsem.C (sems_S i1)) (c2 : Modsem.C (sems_T i2)) :=
  match_Cs (cast (fun i => linking.Modsem.C (sems_S i)) pf c1) c2.

Definition match_cores (c1 : linking.Core.t sems_S) (c2 : Core.t sems_T) :=
  [/\ linking.Core.sg c1=Core.sg c2
    & exists pf : linking.Core.i c1=Core.i c2, 
        match_Cs' pf (linking.Core.c c1) (Core.c c2)].

Require Import stack.

Fixpoint match_stacks_rec 
         (s1 : Stack.t (linking.Core.t sems_S)) 
         (s2 : Stack.t (Core.t sems_T)) :=
  match s1, s2 with
    | nil, nil => True
    | c1 :: s1', c2 :: s2' => 
        [/\ match_cores c1 c2 & match_stacks_rec s1' s2']
    | _, _ => False
  end.

Definition match_stacks 
    (s1 : linking.CallStack.t sems_S) (s2 : CallStack.t sems_T) :=
  match_stacks_rec (linking.CallStack.callStack s1) (CallStack.callStack s2).

Record match_linked (c1 : linking.Linker.t _ sems_S) (c2 : Linker.t _ sems_T) : Type :=
  mk_match_linked
    { match_linked_fn_tbls : linking.Linker.fn_tbl c1=Linker.fn_tbl c2
    ; match_linked_stacks : match_stacks (linking.Linker.stack c1) (Linker.stack c2) }.

Require Import msl.Coqlib2.

Lemma initial_core_eq ix b vals c :
  initial_core (linking.Modsem.sem (sems_S ix)) (linking.Modsem.ge (sems_S ix))
    (Vptr b Integers.Int.zero) vals = Some c -> 
  initial_core (Modsem.sem (sems_T ix)) (Modsem.ge (sems_T ix))
    (Vptr b Integers.Int.zero) vals = Some (cast_ty (C_types_eq ix) c).
Proof.
rewrite /cast_ty; move: c; rewrite /C_types_eq /= /sems_S.
by case: (sems_T ix)=> /= F V ge c sem c0 ->.
Qed.

Lemma atext_eq a1 a2 :
  match_cores a1 a2 -> 
  at_external (linking.Modsem.sem (sems_S (linking.Core.i a1))) (linking.Core.c a1) =
  at_external (Modsem.sem (sems_T (Core.i a2))) (Core.c a2).
Proof.
case=> _ []Heq; move: a1 a2 Heq.
rewrite /match_Cs' /match_Cs=> a1 a2 Heq <- /=; rewrite <-Heq; clear Heq.
rewrite cast_ty_erefl /cast_ty /C_types_eq; move: (linking.Core.c a1); rewrite /sems_S. 
by case: (sems_T (linking.Core.i a1)).
Qed.

Lemma atExternal_eq a1 a2 :
  match_cores a1 a2 -> 
  linking.atExternal sems_S a1 -> 
  atExternal sems_T a2.
Proof.
case: a1; case: a2=> ? a1 ? ? a2 ? /=.
case at1: (at_external _ _)=> // [[[? ?] ?]].
case at2: (at_external _ _)=> // [[[? ?] ?]|] //.
by move/atext_eq; rewrite /= at1 at2.
Qed.

Lemma match_linked_handle ef id vals st1 st2 st1' : 
  match_linked st1 st2 -> 
  linking.LinkerSem.handle (ef_sig ef) id st1 vals = Some st1' -> 
  exists st2',
    LinkerSem.handle (ef_sig ef) id st2 vals = Some st2'
    /\ match_linked st1' st2'.
Proof.
move=> H; case/linking.LinkerSem.handleP=> 
 pf []ix []bf []c []Htbl1 Hfnd1 Hinit Heq.
have [c' [Hinit' HC]]: 
  exists c', 
    initCore sems_T (ef_sig ef) ix (Vptr bf Integers.Int.zero) vals = Some c'
    /\ match_cores c c'.
{ move: Hinit; rewrite /linking.initCore /initCore.
  case Hinit: (initial_core _ _ _ _)=> // [c']; case=> Heqcc'.
  move: (initial_core_eq Hinit)=> Hinit'.
  exists {| Core.i:=ix; 
            Core.c:=cast_ty (C_types_eq ix) c'; 
            Core.sg:=ef_sig ef|}.
  rewrite Hinit'; split=> //; split; first by rewrite -Heqcc'.
  by rewrite -Heqcc'; exists erefl. }
have pf': all (atExternal sems_T) (CallStack.callStack (Linker.stack st2)).
{ clear -pf H; case: H=> _; rewrite /match_stacks.
  case: st1 pf=> /= _; case=> stk /= _ H H2.
  case: st2 H2=> /= _; case=> stk2 /= _ H2.
  elim: stk stk2 H H2; first by case.
  move=> a1 l1 IH; case=> // a2 l2 /=; case/andP=> H H2 []H3 H4. 
  apply/andP; split; first by apply: (atExternal_eq H3 H).
  by apply: (IH _ H2). }
exists (pushCore st2 c' pf'); split.
apply/LinkerSem.handleP.
exists pf', ix, bf, c'; split=> //; first by case: H=> <- _.
by clear - Hfnd1; move: Hfnd1; rewrite /sems_S; case: (sems_T ix).
apply: mk_match_linked; first by case H; rewrite Heq.
by case: H; rewrite Heq /match_stacks /=; split.
Qed.

Lemma halted_eq a1 a2 :
  match_cores a1 a2 -> 
  halted (linking.Modsem.sem (sems_S (linking.Core.i a1))) (linking.Core.c a1) =
  halted (Modsem.sem (sems_T (Core.i a2))) (Core.c a2).
Proof.
case=> _ []Heq; move: a1 a2 Heq.
rewrite /match_Cs' /match_Cs=> a1 a2 Heq <- /=; rewrite <-Heq; clear Heq.
rewrite cast_ty_erefl /cast_ty /C_types_eq; move: (linking.Core.c a1); rewrite /sems_S. 
by case: (sems_T (linking.Core.i a1)).
Qed.

Lemma match_linked_atext st1 st2 :
  match_linked st1 st2 -> 
  linking.LinkerSem.at_external0 st1 = LinkerSem.at_external0 st2.
Proof.
case; rewrite /linking.LinkerSem.at_external0=> _.
case: st1=> ?; case; case=> //= a1 l1 ?.
case: st2=> ?; case; case=> //= a2 l2 ?.
rewrite /match_stacks /=; case=> Hh Ht.
by rewrite (atext_eq Hh).
Qed.

Lemma match_linked_halted st1 st2 :
  match_linked st1 st2 -> 
  linking.LinkerSem.halted0 st1 = LinkerSem.halted0 st2.
Proof.
case; rewrite /linking.LinkerSem.halted0 /LinkerSem.halted0=> _.
case: st1=> ?; case; case=> //= a1 l1 ?.
case: st2=> ?; case; case=> //= a2 l2 ?.
rewrite /match_stacks /=; case=> Hh Ht.
case Hhlt: (halted _ _)=> // [rv|].
rewrite (halted_eq Hh) in Hhlt; rewrite Hhlt.
by case: Hh=> -> _; case: (val_casted.val_has_type_func _ _).
by rewrite (halted_eq Hh) in Hhlt; rewrite Hhlt.
Qed.

Lemma match_linked_aft' rv a1 a2 a1' (pf : linking.Core.i a1=Core.i a2) :
  match_Cs' pf (linking.Core.c a1) (Core.c a2) ->
  after_external (linking.Modsem.sem (sems_S (linking.Core.i a1))) 
                 (Some rv) (linking.Core.c a1) = Some a1' -> 
  exists a2',
    after_external (Modsem.sem (sems_T (Core.i a2))) 
                   (Some rv) (Core.c a2) = Some a2'
    /\ match_Cs' pf a1' a2'.
Proof.
move: rv a1 a2 a1' pf.
rewrite /match_Cs' /match_Cs=> rv a1 a2 a1' pf <- /=; move: a1'.
rewrite <-pf; clear pf.
rewrite cast_ty_erefl /cast_ty /C_types_eq; move: (linking.Core.c a1). 
rewrite /sems_S /=; case: (sems_T (linking.Core.i a1))=> /= F V ge C sem. 
by move=> c a1' aft /=; rewrite /eq_rect_r /=; exists a1'.
Qed.

Lemma match_linked_aft st1 rv st1' st2 : 
  match_linked st1 st2 -> 
  linking.LinkerSem.after_external (Some rv) st1 = Some st1' -> 
  exists st2',
    LinkerSem.after_external (Some rv) st2 = Some st2' 
    /\ match_linked st1' st2'.
Proof.
case; rewrite /linking.LinkerSem.after_external /LinkerSem.after_external=> Htbl.
case: st1 Htbl=> ?; case; case=> //= a1 l1 ? Htbl.
case: st2 Htbl=> ?; case; case=> //= a2 l2 ? Htbl.
rewrite /match_stacks /=; case=> Hh Ht.
case Haft: (after_external _ _ _)=> // [a1'].
case: Hh=> Hsg []Heq Hc; case=> <-.
case: (match_linked_aft' Hc Haft)=> a2' []Haft' Hc'.
rewrite Haft'; eexists; split=> //; apply: mk_match_linked=> //.
rewrite /match_stacks /=; split=> //; split=> //=.
by exists Heq.
Qed.

Lemma match_stacks_rec_size_eq s1 s2 :
  match_stacks_rec s1 s2 -> size s1 = size s2.
Proof.
elim: s1 s2; case=> //.
by move=> ? ? ? ? IH; case=> // ? ? /= []H H2; rewrite (IH _ H2).
Qed.

Lemma match_stacks_size_eq s1 s2 :
  match_stacks (linking.Linker.stack s1) (Linker.stack s2) -> 
  linking.CallStack.callStackSize (linking.Linker.stack s1) 
= CallStack.callStackSize (Linker.stack s2).
Proof.
rewrite /match_stacks /CallStack.callStackSize.
by apply: match_stacks_rec_size_eq.
Qed.

Lemma match_linked_inContext st1 st2 :
  match_linked st1 st2 -> 
  linking.inContext st1 = inContext st2.
Proof.
by case=> _ H; rewrite /linking.inContext; rewrite (match_stacks_size_eq H).
Qed.

Lemma match_linked_popCore st1 st2 st1' :
  match_linked st1 st2 -> 
  linking.popCore st1 = Some st1' -> 
  exists st2', 
    popCore st2 = Some st2' 
    /\ match_linked st1' st2'.
Proof.
move=> H; case/linking.popCoreE=> Hwf []Hctx ->.
rewrite (match_linked_inContext H) in Hctx.
have Hwf': wf_callStack (STACK.pop (CallStack.callStack (Linker.stack st2))).
{ case: H=> _; rewrite /match_stacks; clear -Hwf.
  case: st1 Hwf=> /= _; case=> stk /= _; case: st2=> /= _; case=> s2 /= _ H. 
  case: stk s2 H=> // a1 l1; case=> // a2 l2 /= H []H2 H3.
  move: H; rewrite /wf_callStack; case/andP=> H H4; apply/andP; split.
  { clear -H H3; move: H. 
    have Hpop: match_stacks_rec (STACK.pop l1) (STACK.pop l2).
    { by case: l1 H3=> //; case: l2=> // ? ? ? ? /= []. }
    clear H3; move: Hpop.
    move: (STACK.pop l1)=> l1'.
    move: (STACK.pop l2)=> l2'.
    clear l1 l2.
    elim: l1' l2'; first by case.
    move=> a1 l1 /= IH; case=> // a2 l2 /= []H2 H3.
    case/andP=> H H4; apply/andP; split; first by apply: (atExternal_eq H2 H).
    by apply: IH. }
  by rewrite (match_stacks_rec_size_eq H3) in H4. }
exists (updStack st2 
  (CallStack.mk (STACK.pop (CallStack.callStack (Linker.stack st2))) Hwf')).
split; first by erewrite popCoreI; eauto.
case: H=> H H2; apply: mk_match_linked=> //=.
clear -H2; move: H2; rewrite /match_stacks.
case: st1 Hwf Hwf'=> /= _; case; case=> // a1 l1 /= _ _ _.
by case: st2=> /= _; case; case=> // a2 l2 /= _; case.
Qed.

Lemma erase_corestep ix c m c' m' :
  corestep (linking.Modsem.sem (sems_S ix)) 
           (linking.Modsem.ge (sems_S ix)) c m c' m' -> 
  corestep (Modsem.sem (sems_T ix)) (Modsem.ge (sems_T ix)) 
           (cast_ty (C_types_eq ix) c) (m_dry m) 
           (cast_ty (C_types_eq ix) c') (m_dry m').
Proof.
rewrite /cast_ty; move: c c'; rewrite /C_types_eq /= /sems_S.
by case: (sems_T ix)=> /= F V ge c sem c0 c'; case=> H _.
Qed.

Lemma depeq_corestep s1 m1 c' m1' s2 
      (Hmatch : match_cores (linking.peekCore s1) (peekCore s2))
      (Heq : linking.Core.i (linking.peekCore s1) = Core.i (peekCore s2)) :
  corestep (Modsem.sem (sems_T (linking.Core.i (linking.peekCore s1))))
           (Modsem.ge (sems_T (linking.Core.i (linking.peekCore s1))))
           (cast_ty (C_types_eq (linking.Core.i (linking.peekCore s1)))
                    (linking.Core.c (linking.peekCore s1))) (m_dry m1)
           c'
           (m_dry m1') -> 
  corestep (Modsem.sem (sems_T (Core.i (peekCore s2))))
           (Modsem.ge (sems_T (Core.i (peekCore s2)))) 
           (Core.c (peekCore s2)) (m_dry m1) 
           (cast (fun i : 'I_N => Modsem.C (sems_T i)) Heq c')
           (m_dry m1').
Proof.
set T := fun ix => Modsem.C (sems_T ix).
set P := fun ix (x : T ix) (y : T ix) => 
  corestep (Modsem.sem (sems_T ix)) (Modsem.ge (sems_T ix))
           x (m_dry m1) y (m_dry m1').
move=> H.
have: P (linking.Core.i (linking.peekCore s1)) 
        (cast_ty (C_types_eq (linking.Core.i (linking.peekCore s1))) 
                 (linking.Core.c (linking.peekCore s1))) 
        c'=> // H2.
have H3: (P (Core.i (peekCore s2)) (Core.c (peekCore s2)) (cast T Heq c')).
apply: cast_indnatdep2=> //.
have H3: 
  cast_ty (C_types_eq (linking.Core.i (linking.peekCore s1))) 
          (linking.Core.c (linking.peekCore s1))
= cast T (Logic.eq_sym Heq) (Core.c (peekCore s2)).
{ clear -Heq Hmatch; case: Hmatch=> _ []Hpf. 
  rewrite /match_Cs' /match_Cs=> <-.
  have Hpfeq: Hpf = Heq by apply: proof_irr. 
  rewrite Hpfeq; clear Hpf Hpfeq. 
  by rewrite /C_types_eq /cast_ty /T /=; clear T; rewrite <-Heq. }
by rewrite -H3.
by apply: H3.
Qed.

Lemma match_stacks_sg_eq s1 s2 :
  match_stacks (linking.Linker.stack s1) (Linker.stack s2) -> 
  linking.Core.sg (linking.peekCore s1) = Core.sg (peekCore s2).
Proof.
rewrite /match_stacks; case: s1=> /= _; case; case=> // a1 l1 /= _.
by case: s2=> /= _; case; case=> // a2 l2 /= _; case; case=> ->.
Qed.

Lemma match_stacks_rec_pop s1 s2 :
  match_stacks_rec (linking.CallStack.callStack (linking.Linker.stack s1))
                   (CallStack.callStack (Linker.stack s2)) -> 
  match_stacks_rec (STACK.pop (linking.CallStack.callStack (linking.Linker.stack s1)))
                   (STACK.pop (CallStack.callStack (Linker.stack s2))).
Proof.
case: s1=> ?; case; case=> // a1 l1 ?.
by case: s2=> ?; case; case=> // a2 l2 ? /=; case.
Qed.

Lemma corestep0_match s1 m1 s1' m1' s2 :
  match_linked s1 s2 -> 
  linking.LinkerSem.corestep0 s1 m1 s1' m1' ->
  exists s2', 
    LinkerSem.corestep0 s2 (m_dry m1) s2' (m_dry m1')
    /\ match_linked s1' s2'.
Proof.
rewrite /linking.LinkerSem.corestep0; case=> Hfn Hstk []c' [].
rewrite /LinkerSem.corestep0.
move/erase_corestep=> Hstep=> ->.
have Heq: linking.Core.i (linking.peekCore s1) = Core.i (peekCore s2). 
{ clear -Hstk; move: Hstk.
  case: s1=> /= _; case; case=> // a1 l1 ? /=.
  case: s2=> /= _; case; case=> // a2 l2 ? /=.                                   
  by rewrite /match_stacks /=; case; case=> _; case. }
set c'' := (cast (fun i => Modsem.C (sems_T i)) Heq 
           (cast_ty (C_types_eq (linking.Core.i (linking.peekCore s1))) c')).
exists (updCore s2 (Core.upd (peekCore s2) c'')); split.
exists c''; split=> //.
apply: depeq_corestep=> //.
{ clear -Hstk; case: s1 Hstk=> /= _; rewrite /match_stacks.
  case; case=> /= ?; case: s2=> /= _; case; case=> //.
  by move=> a1 l1 /= _ ? _ []. }
apply: mk_match_linked=> //; split=> //. 
split=> //; first by apply: match_stacks_sg_eq.
exists Heq; rewrite /match_Cs' /match_Cs /c''; clear -c'.
move: c'; rewrite /sems_S /= /C_types_eq /cast_ty /eq_rect_r /=.
rewrite <-Heq; clear Heq=> /=.
by case: (sems_T (linking.Core.i (linking.peekCore s1))).
by apply: match_stacks_rec_pop.
Qed.

(* The simulation proof proper:                                           *)

Lemma Juicy_linked_erasure ge main : 
  Wholeprog_sim source target ge ge main eq
    (fun _ g1 vs1 m1 g2 vs2 m2 => g1=g2 /\ vs1=vs2 /\ m_dry m1=m2)
    (fun _ g1 v1 m1 g2 v2 m2 => g1=g2 /\ v1=v2 /\ m_dry m1=m2).
Proof.
apply Build_Wholeprog_sim 
  with (core_data := unit)
       (core_ord := fun _ _ => False)
       (match_state := 
          fun (_:unit) _ c1 m1 c2 m2 => 
            m_dry m1=m2 /\
            match_linked c1 c2)=> //.

{ (* init *) 
move=> j c1 vals1 m1 vals2 m2 init []_ []<- <-.
exists (Build_SM_Injection xpred0 xpred0 xpred0 xpred0 (fun _ => None)
                           xpred0 xpred0 xpred0 xpred0 j).
exists tt; case: c1 init=> fn_tbl stk. 
rewrite /= /linking.LinkerSem.initial_core /LinkerSem.initial_core.
case: main=> // bf i. 
case Hint: (Integers.Int.eq i Integers.Int.zero)=> //.
case Hfind: (Genv.invert_symbol _ _)=> // [id].
case Hplt: (plt _)=> [ix|//].
case Hinit: (linking.initCore _ _ _ _)=> [c|//]; case=> eq1 eq2; subst.
move: Hinit; rewrite /linking.initCore /initCore. 
case Hinit: (initial_core _ _ _ _)=> [c0|//]; case=> eq; subst.
set (c1 := cast_ty (C_types_eq ix) c0).
set (d1 := Core.mk _ _ ix c1 LinkerSem.main_sig).
set (stk1 := CallStack.singl d1).
exists (Linker.mkLinker fn_tbl stk1); split.
by rewrite /as_inj /join /=; extensionality b0; case: (j b0)=> [[? ?]|//].
move: Hinit; move/initial_core_eq=> -> /=; split; first by f_equal.
split=> //; apply: mk_match_linked=> //=.
rewrite /match_stacks; split=> //; rewrite /match_cores; split=> //=.
by exists erefl; rewrite /match_Cs' cast_ty_erefl. 
}

{ (*step*)
move=> st1 m1 st1' m1' /= STEP _ st2 mu m2 []<- H.
case: STEP.
move/corestep0_match.
case/(_ _ H)=> st2' []STEP' MTCH; exists st2', (m_dry m1'), tt, mu.
split=> //; left; exists O=> /=; exists st2', (m_dry m1'); split=> //.
by left.
case=> Hag; case=> NSTEP; rewrite -(age_jm_dry Hag).
case Hat: (linking.LinkerSem.at_external0 st1)=> // [[[ef1 sg1] vals1]|].
case Hfun: (linking.LinkerSem.fun_id ef1)=> // [id].
case Hhdl: (linking.LinkerSem.handle _ _ _ _)=> // [st1''] ->.
case: (match_linked_handle H Hhdl)=> st2'' []Hhdl' H'.
exists st2'', (m_dry m1), tt, mu; split=> //; left.
exists O=> /=. exists st2'', (m_dry m1); split=> //; right.
split=> //; split.
move=> step; move: (LinkerSem.corestep_not_at_external0 step).
by rewrite (match_linked_atext H) in Hat; rewrite Hat; discriminate.
rewrite -(match_linked_atext H) Hat. 
rewrite /linking.LinkerSem.fun_id in Hfun. 
rewrite /LinkerSem.fun_id Hfun Hhdl' //.
case Hctx: (linking.inContext _)=> //.
case Hhlt: (linking.LinkerSem.halted0 _)=> // [rv].
case Hpop: (linking.popCore _)=> // [st1''].
case Haft: (linking.LinkerSem.after_external _ _)=> // [st1'''] ->.
rewrite (match_linked_atext H) in Hat.
rewrite (match_linked_halted H) in Hhlt.
case: (match_linked_popCore H Hpop)=> st2'' []Hpop' H'.
rewrite (match_linked_inContext H) in Hctx.
case: (match_linked_aft H' Haft)=> st2''' []Haft' H''.
exists st2''', (m_dry m1), tt, mu; split=> //; left.
exists O=> /=. exists st2''', (m_dry m1); split=> //; right.
split=> //; split.
move=> step; move: (LinkerSem.corestep_not_halted0' step).
by rewrite Hhlt; discriminate.
by rewrite Hat Hctx Hhlt Hpop' Haft'.
}

{ (*halted*)
move=> _ mu s1 m1 s2 m2 v []Hmeq H Hhlt; exists mu, v; split=> //.
move: Hhlt; rewrite /= /LinkerSem.halted /linking.LinkerSem.halted.
case Hctx: (linking.inContext s1)=> //=.
rewrite (match_linked_inContext H) in Hctx; rewrite Hctx=> /=.
case Hhlt: (linking.LinkerSem.halted0 _)=> // [rv]. 
by rewrite (match_linked_halted H) in Hhlt; rewrite Hhlt; case=> ->.
}
Qed.

End erasure.

