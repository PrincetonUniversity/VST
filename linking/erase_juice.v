Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.
Unset Strict Implicit.

Require Import juicy_mem.
Require Import juicy_extspec.

Require Import pos.
Require Import core_semantics_tcs.

Require Import linking. 
Require Import wholeprog_simulations. Import Wholeprog_sim.

Section erasure.

Variable N : pos.

Variable plt : ident -> option 'I_N.

Variable sems_T : 'I_N -> Modsem.t mem.

Definition sems_S (ix : 'I_N) :=
  match sems_T ix with
    Modsem.mk F V genv C s => 
    @Modsem.mk juicy_mem F V genv C (juicy_core_sem s) 
  end.

Notation source := (LinkerSem.coresem N sems_S plt).

Notation target := (LinkerSem.coresem N sems_T plt).

Lemma C_types_eq ix : Modsem.C (sems_S ix) = Modsem.C (sems_T ix).
Proof. by rewrite /sems_S; case: (sems_T ix). Qed.

(*

(* The types `linker N sems_S' and `linker N sems_T' are morally
   equal, but dependent types get in the way. Here I try to ease the
   pain somewhat. *)

Require Import stack.

Fixpoint stack_coerce (s : Stack.t (Core.t sems_S)) : Stack.t (Core.t sems_T).
case: s=> [|[ix c] sg s']; first by refine nil. 
apply: cons.
rewrite /sems_S in c.
apply: Core.mk.
refine ix.
move: c; case: (sems_T ix)=> /= F V ge C sem c.
refine c.
refine sg.
refine (stack_coerce s').
Defined.

Lemma stack_coerce_at_external 
    (s : Stack.t (Core.t sems_S)) (allAt : all (atExternal sems_S) s) :
  all (atExternal sems_T) (stack_coerce s).
Proof.
elim: s allAt=> // [[ix c] sg] s' IH /=.

case H: (at_external (Modsem.sem (sems_S ix)) c)=> [[[x y] z]|] H2.
move: (IH H2)=> H3; move: H. case: (sems_S ix). => F V ge C sem.


Lemma stack_coerce_wf (s : Stack.t (Core.t sems_S)) (wf : wf_callStack s) : 
  wf_callStack (stack_coerce s).
Proof.
case: s wf=> // [[ix c] sg] s'.
rewrite /wf_callStack; move/andP; case=> /= H H2; apply/andP; split=> //=.


Definition linker_coerce (l : linker _ sems_S) : linker _ sems_T.
case: l=> fn_tbl stk; apply: (Linker.mkLinker fn_tbl).
case: stk=> stk wf.

Lemma core_types_eq : Core.t sems_S = Core.t sems_T.
Admitted.

Lemma linker_types_eq : linker N sems_S = linker N sems_T.
Admitted.

Definition coerce_C ix (c : Modsem.C (sems_S ix)) : Modsem.C (sems_T ix).
rewrite -C_types_eq; refine c.
Defined.

Definition coerce_core (c : Core.t sems_S) : Core.t sems_T.
rewrite -core_types_eq; refine c.
Defined.

Definition coerce_linker (l : linker N sems_S) : linker N sems_T.
rewrite -linker_types_eq; refine l.
Defined.

Require Import cast.

Lemma initial_core_eq ge v vs : 
  initial_core source ge v vs 
= cast initial_core target ge v vs).
Proof.
rewrite /= /LinkerSem.initial_core.
case: v; try by move=> _; rewrite linker_types_eq; apply: JMeq_refl.
by rewrite linker_types_eq; apply: JMeq_refl.
move=> b _; case: (plt b); last by rewrite linker_types_eq; apply: JMeq_refl.
move=> ix; rewrite /initCore; case init: (initial_core _ _ _ _)=> [c|]. 
have [c' [init' jmeqcc']]: exists c', 
  [/\ initial_core (Modsem.sem (sems_T ix)) (Modsem.ge (sems_T ix))
                   (Vptr b Integers.Int.zero) vs = Some c'
    & JMeq c c'].
{ move: c init; rewrite /sems_S.
  by case: (sems_T ix)=> /= F V ge0 C sem c init; exists c. }
rewrite init'.
have eqcc': coerce_C c = c'.
{ clear -jmeqcc'; move: c c' jmeqcc'.
  rewrite /coerce_C /=.

clear -eqcc'; move: c c' eqcc'; move: (C_types_eq ix).
*)

Require Import cast.

Definition match_Cs i (c1 : Modsem.C (sems_S i)) (c2 : Modsem.C (sems_T i)) :=
  cast_ty (C_types_eq i) c1 = c2.  

Definition match_Cs' (i1 i2 : 'I_N) (pf : @eq 'I_N i1 i2)
    (c1 : Modsem.C (sems_S i1)) (c2 : Modsem.C (sems_T i2)) :=
  match_Cs (cast (fun i => Modsem.C (sems_S i)) pf c1) c2.

Definition match_cores (c1 : Core.t sems_S) (c2 : Core.t sems_T) :=
  [/\ Core.sg c1=Core.sg c2
    & exists pf : Core.i c1=Core.i c2, match_Cs' pf (Core.c c1) (Core.c c2)].

Require Import stack.

Fixpoint match_stacks_rec 
         (s1 : Stack.t (Core.t sems_S)) 
         (s2 : Stack.t (Core.t sems_T)) :=
  match s1, s2 with
    | nil, nil => True
    | c1 :: s1', c2 :: s2' => 
        [/\ match_cores c1 c2 & match_stacks_rec s1' s2']
    | _, _ => False
  end.

Definition match_stacks (s1 : CallStack.t sems_S) (s2 : CallStack.t sems_T) :=
  match_stacks_rec (CallStack.callStack s1) (CallStack.callStack s2).

Record match_linked (c1 : Linker.t _ sems_S) (c2 : Linker.t _ sems_T) : Type :=
  mk_match_linked
    { match_linked_fn_tbls : Linker.fn_tbl c1=Linker.fn_tbl c2
    ; match_linked_stacks : match_stacks (Linker.stack c1) (Linker.stack c2) }.

Require Import msl.Coqlib2.

Lemma initial_core_eq ix b vals c :
  initial_core (Modsem.sem (sems_S ix)) (Modsem.ge (sems_S ix))
    (Vptr b Integers.Int.zero) vals = Some c -> 
  initial_core (Modsem.sem (sems_T ix)) (Modsem.ge (sems_T ix))
    (Vptr b Integers.Int.zero) vals = Some (cast_ty (C_types_eq ix) c).
Proof.
Admitted.

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

(* init *)
{ 
move=> j c1 vals1 m1 vals2 m2 init []_ []<- <-.
exists (Build_SM_Injection xpred0 xpred0 xpred0 xpred0 (fun _ => None)
                           xpred0 xpred0 xpred0 xpred0 j).
exists tt; case: c1 init=> fn_tbl stk; rewrite /= /LinkerSem.initial_core.
case: main=> // b _; case Hplt: (plt _)=> [ix|//].
case Hinit: (initCore _ _ _ _)=> [c|//]; case=> eq1 eq2; subst.
move: Hinit; rewrite /initCore. 
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
admit.
}

{ (*halted*)
admit.
}
Qed.

End erasure.

