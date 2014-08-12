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
Proof. by rewrite /sems_S; case: (sems_T ix). Defined.

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
rewrite /cast_ty; move: c; rewrite /C_types_eq /= /sems_S.
by case: (sems_T ix)=> /= F V ge c sem c0 -> //.
Qed.

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
move=> st1 m1 st1' m1' /= STEP _ st2 _ m2 []<- H.
}

{ (*halted*)
admit.
}
Qed.

End erasure.

