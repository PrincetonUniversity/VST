Add LoadPath "..".
Require Import sepcomp.mem_lemmas.
Require Import sepcomp.core_semantics.
Require Import sepcomp.StructuredInjections.
Require Import sepcomp.effect_simulations.
Require Import sepcomp.effect_properties.

Require Import sepcomp.pos.
Require Import sepcomp.stack.
Require Import sepcomp.wf_lemmas.
Require Import sepcomp.core_semantics_lemmas.
Require Import sepcomp.linking.

Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.

Require Import compcert.common.AST.    (*for ident*)
Require Import compcert.common.Values.   
Require Import compcert.common.Globalenvs.   
Require Import compcert.common.Memory.   

(** * Linking simulation proof 

This file states and proves the main linking simulation result.

*)

Section linkingSimulation.

Import SM_simulation.
Import Linker.
Import Static.

Arguments core_data {F1 V1 C1 F2 V2 C2 Sem1 Sem2 ge1 ge2} _ _.
Arguments core_ord  {F1 V1 C1 F2 V2 C2 Sem1 Sem2 ge1 ge2 entry_points} _ _ _.
Arguments match_state {F1 V1 C1 F2 V2 C2 Sem1 Sem2 ge1 ge2 entry_points} _ _ _ _ _ _ _.

Variable N : pos.
Variable (cores_S cores_T : 'I_N -> Static.t). 
Variable fun_tbl : ident -> option 'I_N.
Variable entry_points : seq (val*val*signature).
Variable (sims : forall i : 'I_N, 
  let s := cores_S i in
  let t := cores_T i in
  SM_simulation_inject s.(coreSem) t.(coreSem) s.(ge) t.(ge) entry_points).
Variable my_ge : ge_ty.
Variable my_ge_S : forall (i : 'I_N), genvs_domain_eq my_ge (cores_S i).(ge).
Variable my_ge_T : forall (i : 'I_N), genvs_domain_eq my_ge (cores_T i).(ge).

Let types := fun i : 'I_N => (sims i).(core_data entry_points).
Let ords : forall i : 'I_N, types i -> types i -> Prop 
  := fun i : 'I_N => (sims i).(core_ord).

Variable wf_ords : forall i : 'I_N, well_founded (ords i).

Let linker_S := effsem N cores_S fun_tbl.
Let linker_T := effsem N cores_T fun_tbl.

Let ord := @Lex.ord N types ords.

Definition cast_ty (T1 T2: Type) (pf: T1=T2) (x : T1) : T2.
rewrite pf in x; refine x.
Defined. 

Lemma types_eq {c : Core.t cores_S} {d : Core.t cores_T} (pf : c.(Core.i)=d.(Core.i)) : 
  C (cores_T (Core.i d))=C (cores_T (Core.i c)).
Proof. by rewrite pf. Qed.

Notation cast pf x := (cast_ty (types_eq pf) x).

Section frame_inv.

Import Core.

Variables (c : t cores_S) (d : t cores_T). 
Variable  (pf : c.(i)=d.(i)).

Require Import compcert.lib.Coqlib. (*for Forall2*)

Record frame_inv cd0 mu0 mu m10 m1 e1 ef_sig1 vals1 m20 m2 e2 ef_sig2 vals2 : Type :=
  { (* local definitions *)
    pubSrc' := fun b => [&& locBlocksSrc mu0 b & REACH m10 (exportedSrc mu0 vals1) b] 
  ; pubTgt' := fun b => [&& locBlocksTgt mu0 b & REACH m20 (exportedTgt mu0 vals2) b] 
  ; nu0     := replace_locals mu0 pubSrc' pubTgt'

    (* invariants required to instantiate at_external *)
  ; frame_inj   : Mem.inject (as_inj mu0) m10 m20
  ; frame_match : (sims c.(i)).(match_state) cd0 mu0 c.(Core.c) m10 (cast pf d.(Core.c)) m20 
  ; frame_at1   : at_external (cores_S c.(i)).(coreSem) c.(Core.c) = Some (e1, ef_sig1, vals1) 
  ; frame_at2   : at_external (cores_T c.(i)).(coreSem) (cast pf d.(Core.c)) 
                    = Some (e2, ef_sig2, vals2) 
  ; frame_vinj  : Forall2 (val_inject (as_inj mu0)) vals1 vals2  

  ; frame_fwd1  : mem_forward m10 m1
  ; frame_fwd2  : mem_forward m20 m2

  ; frame_unch1 : Mem.unchanged_on [fun b ofs => [/\ locBlocksSrc nu0 b & pubBlocksSrc nu0 b]] m10 m1
  ; frame_unch2 : Mem.unchanged_on (local_out_of_reach nu0 m10) m20 m2 

  ; frame_incr : StructuredInjections.intern_incr mu0 mu
  ; frame_sep  : StructuredInjections.sm_inject_separated mu0 mu m10 m20 }.

End frame_inv.

Section head_inv.

Import Core.

Variables (c : t cores_S) (d : t cores_T). 
Variable  (pf : c.(i)=d.(i)).

Record head_inv cd mu m1 m2 : Type :=
  { head_match : (sims c.(i)).(match_state) cd mu c.(Core.c) m1 (cast pf d.(Core.c)) m2 }.

End head_inv.
    
Fixpoint tail_inv mu (s1 : Stack.t (Core.t cores_S)) (s2 : Stack.t (Core.t cores_T)) m1 m2 :=
  match s1, s2 with
    | c :: s1', d :: s2' => 
      [/\ exists (pf : c.(Core.i)=d.(Core.i)) cd0 mu0,
          exists m10 e1 ef_sig1 vals1,
          exists m20 e2 ef_sig2 vals2, 
            frame_inv c d pf cd0 mu0 mu m10 m1 e1 ef_sig1 vals1 m20 m2 e2 ef_sig2 vals2
        & tail_inv mu s1' s2' m1 m2]
    | _, _ => False
  end.

Section R.

Import CallStack.
Import Linker.

Record R (data : Lex.t types) mu (x1 : linker N cores_S) m1 (x2 : linker N cores_T) m2 := 
  { (* local defns. *)
    s1  := x1.(stack) 
  ; s2  := x2.(stack) 
  ; pf1 := CallStack.callStack_nonempty s1 
  ; pf2 := CallStack.callStack_nonempty s2 
  ; c   := stack.head _ pf1 
  ; d   := stack.head _ pf2 
    (* invariants *)
  ; R_head : exists (pf : c.(Core.i)=d.(Core.i)) cd, head_inv c d pf cd mu m1 m2 
  ; R_tail : tail_inv mu s1.(callStack) s2.(callStack) m1 m2 }.

End R.

Section R_defs.

Context data mu x1 m1 x2 m2 (pf : R data mu x1 m1 x2 m2).

Lemma R_wd : SM_wd mu.
Proof. 
move: (R_head pf)=> [A][B]; move/head_match.
by apply: (match_sm_wd _ _ _ _ _ (sims (Core.i (c pf)))).
Qed.

End R_defs.

Lemma link : SM_simulation_inject linker_S linker_T my_ge my_ge entry_points.
Proof.

eapply Build_SM_simulation_inject
  with (core_data   := Lex.t types)
       (core_ord    := ord)
       (match_state := R).

(* well_founded ord *)
- by apply: Lex.wf_ord.

(* match -> SM_wd mu *)
- by apply: R_wd. 

Admitted. (*WORK-IN-PROGRESS*)

End linkingSimulation.


