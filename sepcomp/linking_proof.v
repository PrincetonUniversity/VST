(* standard Coq libraries *)

Require Import JMeq.

(* msl imports *)

Require Import msl.Axioms. (*for proof_irr*)

(* sepcomp imports *)

Require Import sepcomp.mem_lemmas.
Require Import sepcomp.core_semantics.
Require Import sepcomp.StructuredInjections.
Require Import sepcomp.effect_semantics.
Require Import sepcomp.effect_simulations.
Require Import sepcomp.effect_properties.

Require Import sepcomp.pos.
Require Import sepcomp.stack.
Require Import sepcomp.cast.
Require Import sepcomp.pred_lemmas.
Require Import sepcomp.seq_lemmas.
Require Import sepcomp.wf_lemmas.
Require Import sepcomp.core_semantics_lemmas.
Require Import sepcomp.inj_lemmas.
Require Import sepcomp.compcert_linking.
Require Import sepcomp.linking_lemmas.
Require Import sepcomp.disjointness.
Require Import sepcomp.arguments.
Require Import sepcomp.rc_semantics.

(* compcert imports *)

Require Import compcert.common.AST.    (*for ident*)
Require Import compcert.common.Globalenvs.   
Require Import compcert.common.Memory.   

(* ssreflect *)

Require Import ssreflect ssrbool ssrfun seq fintype.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import compcert.common.Values.   

(* This file states and proves the main linking simulation result.        *)
(* Informally,                                                            *)
(*   - Assume a multi-module program with N translation units:            *)
(*                                                                        *)
(*       M_0, M_1, ..., M_{N-1}, and                                      *)
(*                                                                        *)
(*   - For each module M_i, we have an induced                            *)
(*       o Source effect semantics Source_i operating on source states    *)
(*         C_i of source language S_i                                     *)
(*       o Target effect semantics Target_i operating on target states    *)
(*         D_i of target language T_i                                     *)
(*     (Note that it's not required that S_i = S_j for i<>j.)             *)
(*                                                                        *)
(*   - Assume we also have, for each 0 <= i < N, a simulation relation    *)
(*     from S_i to T_i.                                                   *)
(*                                                                        *)
(* Then we can construct a simulation relation Sim between the source     *)
(* semantics                                                              *)
(*                                                                        *)
(*   S_0 >< S_1 >< ... >< S_{N-1}                                         *)
(*                                                                        *)
(* and target semantics                                                   *)
(*                                                                        *)
(*   T_0 >< T_1 >< ... >< T_{N-1}                                         *)
(*                                                                        *)
(* where >< denotes the semantic linking operation defined in             *)
(* compcert_linking.v.                                                    *)

Section linkingSimulation.

Import SM_simulation.
Import Linker.
Import Static.

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

Variable wf_ords : forall i : 'I_N, well_founded (@ords i).

Let linker_S := effsem N cores_S fun_tbl.
Let linker_T := effsem N cores_T fun_tbl.

Let ord := @Lex.ord N types ords.

Notation cast' pf x := (cast (C \o cores_T) pf x).

Notation cast pf x := (cast (C \o cores_T) (sym_eq pf) x).

Section frame_inv.

Import Core.

Variables (c : t cores_S) (d : t cores_T). 
Variable  pf : c.(i)=d.(i).

Require Import compcert.lib.Coqlib. (*for Forall2*)

Definition incr mu mu' :=
  inject_incr (as_inj mu) (as_inj mu') 
  /\ (forall b, DomSrc mu b=true -> DomSrc mu' b=true)
  /\ (forall b, DomTgt mu b=true -> DomTgt mu' b=true).

Lemma intern_incr_incr mu mu' : intern_incr mu mu' -> incr mu mu'.
Proof.
move=> []A []B []C []D []E []F []G []H []I J; split=> //.
rewrite/as_inj/join -B=> b b' delta; case: (extern_of mu b).
by move=> []b'' delta'; case=> <- <-.
by apply: A.
rewrite/DomSrc/DomTgt -I -J; split=> b/orP; case.
by move/(C _)=> ->.
by move=> ->; apply/orP; right.
by move/(D _)=> ->.
by move=> ->; apply/orP; right.
Qed.

Lemma incr_trans mu mu'' mu' : incr mu mu'' -> incr mu'' mu' -> incr mu mu'.
Proof.
case=> A []B C; case=> D []E F; split. 
by apply: (inject_incr_trans _ _ _ A D).
split=> b G; first by apply: (E _ (B _ G)).
by apply: (F _ (C _ G)).
Qed.

(* NOTE TO SELF:                                                          *)
(* Initial core asserts that we match w/ SM_injection                     *)
(*   initial_SM DomS DomT                                                 *)
(*     (REACH m1 (fun b => isGlobalBlock ge1 b || getBlocks vals1 b))     *)
(*     (REACH m2 (fun b => isGlobalBlock ge2 b || getBlocks vals2 b)) j)  *)
(* where the clauses beginning REACH... give frgnSrc/Tgt respectively.    *)
(*                                                                        *)
(* I.e., we establish initially that                                      *)
(*                                                                        *)
(*   (REACH m1 (fun b => isGlobalBlock ge1 b || getBlocks vals1 b))       *)
(*                                                                        *)
(* is a subset of the visible set for the injection of the initialized    *)
(* core.  TODO: We need to record this fact (really, a slight             *)
(* modification of the invariant that accounts for return values as well) *)
(* as an invariant of execution for both the head and tail cores. Then    *)
(* the guarantees we get from RC executions (that write effects are       *)
(* limited to blocks in the RC of initial args, rets, local blocks) will  *)
(* imply that effects are also a subset of the visible region for each    *)
(* core.                                                                  *)

Record frame_inv 
  cd0 mu0 m10 m1 e1 ef_sig1 vals1 m20 m2 e2 ef_sig2 vals2 : Prop :=
  { (* local definitions *)
    pubSrc := [predI (locBlocksSrc mu0) & REACH m10 (exportedSrc mu0 vals1)] 
  ; pubTgt := [predI (locBlocksTgt mu0) & REACH m20 (exportedTgt mu0 vals2)] 
  ; nu0    := replace_locals mu0 pubSrc pubTgt

    (* unary invariants on mu0,m10,m20 *)
  ; frame_inj0  : Mem.inject (as_inj mu0) m10 m20
  ; frame_valid : sm_valid mu0 m10 m20 
  ; frame_match : (sims c.(i)).(match_state) cd0 mu0 
                    (RC.core c.(Core.c)) m10 (cast pf (RC.core d.(Core.c))) m20 
  ; frame_at1   : at_external (cores_S c.(i)).(coreSem) (RC.core c.(Core.c))
                    = Some (e1, ef_sig1, vals1) 
  ; frame_at2   : at_external (cores_T c.(i)).(coreSem) (cast pf (RC.core d.(Core.c))) 
                    = Some (e2, ef_sig2, vals2) 
  ; frame_vinj  : Forall2 (val_inject (as_inj mu0)) vals1 vals2  

    (* invariants relating m10,m20 to active memories m1,m2*)
  ; frame_fwd1  : mem_forward m10 m1
  ; frame_fwd2  : mem_forward m20 m2
  ; frame_unch1 : Mem.unchanged_on [fun b ofs => 
                    [/\ locBlocksSrc nu0 b & pubBlocksSrc nu0 b=false]] m10 m1
  ; frame_unch2 : Mem.unchanged_on (local_out_of_reach nu0 m10) m20 m2 }.

End frame_inv.

Record rel_inv mu0 mu m10 m20 : Prop :=
  { (* invariants relating mu0,mu *)    
    frame_incr       : incr mu0 mu
  ; frame_sep        : sm_inject_separated mu0 mu m10 m20
  ; frame_disj       : disjinv mu0 mu }.

Record frame_pkg : Type := 
  { frame_mu0 :> Inj.t
  ; frame_m10 : Memory.mem
  ; frame_m20 : Memory.mem
  ; frame_val : sm_valid frame_mu0 frame_m10 frame_m20 }.

Definition rel_inv_pred mu pkg := 
  let mu0 := frame_mu0 pkg in
  let m10 := frame_m10 pkg in
  let m20 := frame_m20 pkg in
  rel_inv mu0 mu m10 m20.

Section head_inv.

Import Core.

Variables (c : t cores_S) (d : t cores_T). 
Variable  (pf : c.(i)=d.(i)).

Record head_inv cd mu mus m1 m2 : Type :=
  { head_match : (sims c.(i)).(match_state) cd mu 
                 (RC.core c.(Core.c)) m1 (cast pf (RC.core d.(Core.c))) m2 
  ; head_rel   : All2_aux rel_inv_pred mu mus }.

End head_inv.

Section head_inv_lems.

Context c d pf cd mu mus m1 m2 (inv : @head_inv c d pf cd mu mus m1 m2).

End head_inv_lems.

Import seq.

Fixpoint frame_all (mus : seq frame_pkg) m1 m2 s1 s2 :=
  match mus, s1, s2 with
    | Build_frame_pkg mu0 m10 m20 _ :: mus', c :: s1', d :: s2' => 
      [/\ exists (pf : c.(Core.i)=d.(Core.i)) cd0,
          exists e1 ef_sig1 vals1,
          exists e2 ef_sig2 vals2, 
            @frame_inv c d pf cd0 mu0 
            m10 m1 e1 ef_sig1 vals1 m20 m2 e2 ef_sig2 vals2
        & frame_all mus' m1 m2 s1' s2']
    | nil,nil,nil => True
    | _,_,_ => False
  end.

Definition tail_inv mus s1 s2 m1 m2 :=
  [/\ All2 (rel_inv_pred \o frame_mu0) mus & frame_all mus m1 m2 s1 s2].

Lemma all_wrt_callers_switch T P (a b : T) (l : seq T) :
  All2_aux P b l -> All2 P (a :: l) -> All2 P (b :: l).
Proof. by elim: l a b=> // a' l' IH a b /= []A B [][]C D []E F. Qed.

Definition restrict_sm_wd m1
  (mu : Inj.t) (X : block -> bool)
  (vis_pf : forall b : block, vis mu b -> X b)
  (rc_pf  : REACH_closed m1 X) : Inj.t :=
  Inj.mk (restrict_sm_WD _ (Inj_wd mu) X vis_pf).

Lemma frame_all_inv mu0 m10 m20 x mus m1 m2 s1 s2 :
  frame_all (@Build_frame_pkg mu0 m10 m20 x :: mus) m1 m2 s1 s2 -> 
  exists c s1' d s2',
    [/\ s1 = c :: s1'
      , s2 = d :: s2' 
      & exists (pf : c.(Core.i)=d.(Core.i)) cd0,
        exists e1 ef_sig1 vals1,
        exists e2 ef_sig2 vals2, 
          @frame_inv c d pf cd0 mu0 
          m10 m1 e1 ef_sig1 vals1 m20 m2 e2 ef_sig2 vals2
          /\ frame_all mus m1 m2 s1' s2'].
Proof.
case: s1=> // c s1'; case: s2=> // d s2' /=.
move=> [][]pf => [][]cd []ef1 []sig1 []vals1 []ef2 []sig2 []vals2 A B.
exists c, s1', d, s2'; split=> //.
by exists pf, cd, ef1, sig1, vals1, ef2, sig2, vals2; split.
Qed.

Lemma frame_all_match mu0 m10 m20 x mus m1 m2 s1 s2 :
  frame_all (@Build_frame_pkg mu0 m10 m20 x :: mus) m1 m2 s1 s2 -> 
  exists c s1' d s2',
    [/\ s1 = c :: s1'
      , s2 = d :: s2' 
      & exists (pf : c.(Core.i)=d.(Core.i)) cd0,
        (sims c.(Core.i)).(match_state) cd0 mu0 
          (RC.core c.(Core.c)) m10 (cast pf (RC.core d.(Core.c))) m20].
Proof.
case: s1=> // c s1'; case: s2=> // d s2' /=.
move=> [][]pf => [][]cd []ef1 []sig1 []vals1 []ef2 []sig2 []vals2 A B.
exists c, s1', d, s2'; split=> //.
by exists pf, cd; case: A.
Qed.

Lemma frame_all_globs mus m1 m2 s1 s2 : 
  frame_all mus m1 m2 s1 s2 -> 
  All (fun mu0 => forall b, isGlobalBlock my_ge b -> frgnBlocksSrc mu0 b)  
  $ map (Inj.mu \o frame_mu0) mus.
Proof.
move: m1 m2 s1 s2; elim: mus=> //; case=> mu' ? ? ? mus' IH m1 m2 s1 s2 A.
move: (frame_all_inv A)=> []c []s1' []d []s2' []_ _.
move=> []pf []cd []? []? []? []? []? []? []B C.
case: B=> ? ? ? ? ?; move/match_genv=> []_ D; split.
by rewrite (genvs_domain_eq_isGlobal _ _ (my_ge_S (Core.i c))); apply: D.
by apply: (IH _ _ _ _ C).
Qed.

Lemma frame_all_valid mus m1 m2 s1 s2 : 
  frame_all mus m1 m2 s1 s2 -> 
  All (fun mu0 => sm_valid (Inj.mu mu0) m1 m2) $ map frame_mu0 mus.
Proof.
move: m1 m2 s1 s2; elim: mus=> //; case=> mu' ? ? ? mus' IH m1 m2 s1 s2 A.
move: (frame_all_inv A)=> []c []s1' []d []s2' []_ _.
move=> []pf []cd []? []? []? []? []? []? []B C.
case: B=> ? ? ? ? val; move/match_genv=> []_ D; split=> /=.
by apply: (sm_valid_fwd val).
by apply: (IH _ _ _ _ C).
Qed.

Lemma tail_inv_inv mu0 m10 m20 x mus s1 s2 m1 m2 :
  tail_inv (@Build_frame_pkg mu0 m10 m20 x :: mus) s1 s2 m1 m2 -> 
  exists c s1' d s2',
    [/\ s1 = c :: s1'
      , s2 = d :: s2' 
      , (exists (pf : c.(Core.i)=d.(Core.i)) cd0,
         exists e1 ef_sig1 vals1,
         exists e2 ef_sig2 vals2, 
           @frame_inv c d pf cd0 mu0 
           m10 m1 e1 ef_sig1 vals1 m20 m2 e2 ef_sig2 vals2)
       & tail_inv mus (STACK.pop s1) (STACK.pop s2) m1 m2].
Proof.
case; case=> H1 H2; move/frame_all_inv=> []c []s1' []d []s2' []B C.
move=> []pf []cd []ef1 []sig1 []vals1 []ef2 []sig2 []vals2 []D E.
exists c,s1',d,s2'; split=> //.
by exists pf,cd,ef1,sig1,vals1,ef2,sig2,vals2.
by split=> //; rewrite B C.
Qed.

Lemma tail_inv_match mu0 m10 m20 x mus s1 s2 m1 m2 :
  tail_inv (@Build_frame_pkg mu0 m10 m20 x :: mus) s1 s2 m1 m2 -> 
  exists c s1' d s2',
    [/\ s1 = c :: s1'
      , s2 = d :: s2' 
      & exists (pf : c.(Core.i)=d.(Core.i)) cd0,
        (sims c.(Core.i)).(match_state) cd0 mu0 
          (RC.core c.(Core.c)) m10 (cast pf (RC.core d.(Core.c))) m20].
Proof. by move=> []_; move/frame_all_match. Qed.

Lemma tail_inv_preserves_globals mus s1 s2 m1 m2 :
  tail_inv mus s1 s2 m1 m2 -> 
  All (Events.meminj_preserves_globals my_ge \o extern_of \o Inj.mu)
    [seq frame_mu0 x | x <- mus].
Proof.
move: s1 s2; elim: mus=> // mu0 mus' IH s1 s2.
case: mu0=> ? ? ? ?; move/tail_inv_inv=> []c []? []d []? []-> ->.
move=> []? []? []? []? []? []? []? []? [] ? ? ? ? ?. 
move/match_genv=> [] /= X ? ? ? ? ? ? ? ? TL; split.
rewrite -meminj_preserves_genv2blocks; move: X.
rewrite (genvs_domain_eq_match_genvs (my_ge_S (Core.i c))).
by rewrite meminj_preserves_genv2blocks.
by apply: (IH _ _ TL).
Qed.

Lemma rel_inv_pred_step 
  pkg (mu : Inj.t) m1 m2
  (Esrc Etgt : Values.block -> BinNums.Z -> bool) 
  (mu' : Inj.t) m1' m2' :
  (forall b ofs, Esrc b ofs -> Mem.valid_block m1 b -> vis mu b) -> 
  Memory.Mem.unchanged_on (fun b ofs => Esrc b ofs = false) m1 m1' -> 
  Memory.Mem.unchanged_on (fun b ofs => Etgt b ofs = false) m2 m2' -> 
  (forall (b0 : block) (ofs : Z),
   Etgt b0 ofs = true ->
   Mem.valid_block m2 b0 /\
   (locBlocksTgt mu b0 = false ->
    exists (b1 : block) (delta1 : Z),
      foreign_of mu b1 = Some (b0, delta1) /\
      Esrc b1 (ofs - delta1) = true /\
      Mem.perm m1 b1 (ofs - delta1) Max Nonempty)) -> 
  intern_incr mu mu' -> 
  mem_forward pkg.(frame_m10) m1 -> 
  mem_forward pkg.(frame_m20) m2 -> 
  mem_forward m1 m1' -> 
  mem_forward m2 m2' ->   
  sm_inject_separated mu mu' m1 m2  -> 
  sm_valid mu m1 m2 -> 
  rel_inv_pred mu pkg -> 
  rel_inv_pred mu' pkg.
Proof.
move=> H1 H2 H3 H4 incr fwd10 fwd20 fwd1 fwd2 sep val []incr' sep' disj.
split; first by apply: (incr_trans incr' (intern_incr_incr incr)).
have incr'': inject_incr (as_inj mu) (as_inj mu').
  apply: intern_incr_as_inj=> /=; first by apply: incr.
  by generalize dependent mu'; case.
by apply: (sm_sep_step (frame_val pkg) sep' sep fwd10 fwd20 incr'').
by apply: (disjinv_intern_step disj incr fwd10 fwd20 sep' sep (frame_val pkg)).
Qed.

Lemma wrt_callers_step 
  mus (mu mu' : frame_pkg) m1' m2' s1 s2 m1 m2 
  (Esrc Etgt : Values.block -> BinNums.Z -> bool) :
  (forall b ofs, Esrc b ofs -> Mem.valid_block m1 b -> vis mu b) -> 
  Memory.Mem.unchanged_on (fun b ofs => Esrc b ofs = false) m1 m1' -> 
  Memory.Mem.unchanged_on (fun b ofs => Etgt b ofs = false) m2 m2' -> 
  (forall (b0 : block) (ofs : Z),
   Etgt b0 ofs = true ->
   Mem.valid_block m2 b0 /\
   (locBlocksTgt mu b0 = false ->
    exists (b1 : block) (delta1 : Z),
      foreign_of mu b1 = Some (b0, delta1) /\
      Esrc b1 (ofs - delta1) = true /\
      Mem.perm m1 b1 (ofs - delta1) Max Nonempty)) -> 
  intern_incr mu mu' -> 
  mem_forward m1 m1' -> 
  mem_forward m2 m2' ->   
  sm_inject_separated mu mu' m1 m2  -> 
  sm_valid mu m1 m2 -> 
  frame_all mus m1 m2 s1 s2 -> 
  All2_aux rel_inv_pred mu mus -> 
  All2_aux rel_inv_pred mu' mus.
Proof.
elim: mus mu mu' s1 s2=> // pkg mus' IH mu mu' s1' s2'.
move=> H1 H2 H3 H4 A B C D E F /= []G H.
move: F G; case: s1'=> //; first by case: s2'; case: pkg.
move=> a s1'; case: s2'; first by case: pkg.
move=> b s2'; case: pkg=> ? ? ? ? /= [].
move=> []eq_ab []cd0 []e1 []sig1 []vals1 []e2 []sig2 []vals2.
case=> ? ? ? ? ? frmatch ? ? ? fwd1 fwd2 ? ? ? ?; split.
by eapply rel_inv_pred_step; eauto.
by eapply IH; eauto.
Qed.

Lemma frame_all_step 
  mus (mu mu' : frame_pkg) m1' m2' s1 s2 m1 m2 
  (Esrc Etgt : Values.block -> BinNums.Z -> bool) :
  (forall b ofs, Esrc b ofs -> Mem.valid_block m1 b -> vis mu b) -> 
  Memory.Mem.unchanged_on (fun b ofs => Esrc b ofs = false) m1 m1' -> 
  Memory.Mem.unchanged_on (fun b ofs => Etgt b ofs = false) m2 m2' -> 
  (forall (b0 : block) (ofs : Z),
   Etgt b0 ofs = true ->
   Mem.valid_block m2 b0 /\
   (locBlocksTgt mu b0 = false ->
    exists (b1 : block) (delta1 : Z),
      foreign_of mu b1 = Some (b0, delta1) /\
      Esrc b1 (ofs - delta1) = true /\
      Mem.perm m1 b1 (ofs - delta1) Max Nonempty)) -> 
  mem_forward m1 m1' -> 
  mem_forward m2 m2' ->   
  sm_inject_separated mu mu' m1 m2  -> 
  sm_valid mu m1 m2 ->
  All2_aux rel_inv_pred mu mus -> 
  frame_all mus m1 m2 s1 s2 -> 
  frame_all mus m1' m2' s1 s2.
Proof.
elim: mus mu mu' s1 s2=> // pkg mus' IH mu mu' s1' s2'.
move=> H1 H2 H3 (*H4*) A B C D E.
case: s1'=> // a s1'; case: s2'=> // b s2'; case: pkg=> mu0 m10 m20 val. 
move=> /= []F G [][]eq_ab []cd0 []e1 []sig1 []vals1 []e2 []sig2 []vals2.
case=> ? ? ? ? val' frmatch ? ? ? fwd1 fwd2 ? ? ?; split.
exists eq_ab, cd0, e1, sig1, vals1, e2, sig2, vals2.

apply: Build_frame_inv=> //; first by apply: (mem_forward_trans _ _ _ fwd1 B).
by apply: (mem_forward_trans _ _ _ fwd2 C).

apply: (mem_lemmas.unchanged_on_trans m10 m1 m1')=> //.
set pubSrc' := [predI locBlocksSrc mu0 & REACH m10 (exportedSrc mu0 vals1)].
set pubTgt' := [predI locBlocksTgt mu0 & REACH m20 (exportedTgt mu0 vals2)].
set mu0'    := replace_locals mu0 pubSrc' pubTgt'.
have wd: SM_wd mu0' by apply: replace_reach_wd.
have J: disjinv mu0' mu by case: F=> /= ? ? ?; apply: disjinv_call.
apply: (@disjinv_unchanged_on_src (Inj.mk wd) mu Esrc)=> //.
move: (sm_valid_smvalid_src _ _ _ val)=> val''.
apply: smvalid_src_replace_locals=> //=.
by apply: (smvalid_src_fwd fwd1).

apply: (mem_lemmas.unchanged_on_trans m20 m2 m2')=> //.
set pubSrc' := [predI locBlocksSrc mu0 & REACH m10 (exportedSrc mu0 vals1)].
set pubTgt' := [predI locBlocksTgt mu0 & REACH m20 (exportedTgt mu0 vals2)].
set mu0'    := replace_locals mu0 pubSrc' pubTgt'.
have J: disjinv mu0' mu by case: F=> /= ? ? ?; apply: disjinv_call.
have wd: SM_wd mu0' by apply: replace_reach_wd.
apply: (@disjinv_unchanged_on_tgt (Inj.mk wd) mu Esrc Etgt 
  m10 m1 m2 m2' fwd1)=> //.
move=> b'; case: val'; move/(_ b')=> I _ Q; apply: I.
by rewrite replace_locals_DOM in Q.

by eapply IH; eauto.
Qed.

Lemma tail_inv_step 
  (Esrc Etgt : Values.block -> BinNums.Z -> bool) 
  mus (mu mu' : frame_pkg) m1' m2' s1 s2 m1 m2 :
  (forall b ofs, Esrc b ofs -> Mem.valid_block m1 b -> vis mu b) -> 
  Memory.Mem.unchanged_on (fun b ofs => Esrc b ofs = false) m1 m1' -> 
  Memory.Mem.unchanged_on (fun b ofs => Etgt b ofs = false) m2 m2' -> 
  (forall (b0 : block) (ofs : Z),
   Etgt b0 ofs = true ->
   Mem.valid_block m2 b0 /\
   (locBlocksTgt mu b0 = false ->
    exists (b1 : block) (delta1 : Z),
      foreign_of mu b1 = Some (b0, delta1) /\
      Esrc b1 (ofs - delta1) = true /\
      Mem.perm m1 b1 (ofs - delta1) Max Nonempty)) -> 
  mem_forward m1 m1' -> 
  mem_forward m2 m2' ->   
  sm_inject_separated mu mu' m1 m2  -> 
  sm_valid mu m1 m2 -> 
  All2_aux rel_inv_pred mu mus -> 
  tail_inv mus s1 s2 m1 m2 -> 
  tail_inv mus s1 s2 m1' m2'.
Proof.
move=> ? ? ? ? ? ? ? ? ? []A B; split=> //.
by eapply frame_all_step; eauto.
Qed.

Section R.

Import CallStack.
Import Linker.
Import STACK.

Record R (data : Lex.t types) (mu : SM_Injection)
         (x1 : linker N cores_S) m1 (x2 : linker N cores_T) m2 := 
  { (* local defns. *)
    s1  := x1.(stack) 
  ; s2  := x2.(stack) 
  ; pf1 := CallStack.callStack_nonempty s1 
  ; pf2 := CallStack.callStack_nonempty s2 
  ; c   := STACK.head _ pf1 
  ; d   := STACK.head _ pf2 

    (* invariant *)
  ; R_inv : 
    exists (pf : c.(Core.i)=d.(Core.i)) mu_trash mu_top mus, 
    let mu_tot := join_all (frame_mu0 mu_trash) $ map frame_mu0 (mu_top :: mus) in
    [/\ mu = restrict_sm mu_tot (vis mu_tot) 
      , REACH_closed m1 (vis mu)
      , Events.meminj_preserves_globals my_ge $ extern_of mu_trash
      , (forall b, isGlobalBlock my_ge b -> frgnBlocksSrc mu_trash b)
      , sm_valid mu_trash m1 m2
      , All2_aux DisjointLS mu_trash 
        $ map (Inj.mu \o frame_mu0) $ mu_top :: mus
      , All2_aux DisjointLT mu_trash 
        $ map (Inj.mu \o frame_mu0) $ mu_top :: mus
      , All2_aux Consistent mu_trash 
        $ map (Inj.mu \o frame_mu0) $ mu_top :: mus
      , @head_inv c d pf (Lex.get c.(Core.i) data) mu_top mus m1 m2 
      & tail_inv mus (pop s1) (pop s2) m1 m2] }.

End R.

Section R_lems.

Context data mu x1 m1 x2 m2 (pf : R data mu x1 m1 x2 m2).

Import CallStack.
Import Linker.

Lemma peek_ieq : Core.i (peekCore x1) = Core.i (peekCore x2).
Proof. by move: (R_inv pf); move=> []A _; apply: A. Qed.

Lemma peek_match :
  exists cd mu_top, 
  match_state (sims (Core.i (peekCore x1))) cd mu_top 
  (RC.core (Core.c (peekCore x1))) m1 
  (cast peek_ieq (RC.core (Core.c (peekCore x2)))) m2.
Proof.
move: (R_inv pf)=> []A []? []mu_top []? [] _ _ _ _ _ _ _ _. 
move/head_match=> MATCH ?.
have ->: (cast peek_ieq (RC.core (Core.c (peekCore x2))) 
         = cast A (RC.core (Core.c (peekCore x2))))
  by f_equal; f_equal; apply proof_irr.
by exists (Lex.get (Core.i (peekCore x1)) data), mu_top.
Qed.

Lemma R_match :
  exists (pf0 : (c pf).(Core.i)=(d pf).(Core.i)) mu_trash mu_top mus, 
  let mu_tot := join_all (frame_mu0 mu_trash) $ map frame_mu0 (mu_top :: mus) in
  [/\ mu = restrict_sm mu_tot (vis mu_tot) 
    , REACH_closed m1 (vis mu)
    , Events.meminj_preserves_globals my_ge $ extern_of mu_trash
    , (forall b, isGlobalBlock my_ge b -> frgnBlocksSrc mu_trash b)
    , sm_valid mu_trash m1 m2
    , All2_aux DisjointLS mu_trash $ map (Inj.mu \o frame_mu0) $ mu_top :: mus
    , All2_aux DisjointLT mu_trash $ map (Inj.mu \o frame_mu0) $ mu_top :: mus
    , All2_aux Consistent mu_trash $ map (Inj.mu \o frame_mu0) $ mu_top :: mus
    , @head_inv (c pf) (d pf) pf0 (Lex.get (c pf).(Core.i) data) mu_top mus m1 m2 
    & tail_inv mus (STACK.pop x1.(stack)) (STACK.pop x2.(stack)) m1 m2].
Proof.
case: (R_inv pf)=> pf0 []mu_trash []mu_top []mus []A B C D.
by exists pf0, mu_trash, mu_top, mus; split.
Qed.

Lemma R_match' :
  exists (pf0 : (c pf).(Core.i)=(d pf).(Core.i)) mu_top,
    match_state (sims (Core.i (c pf))) (Lex.get (c pf).(Core.i) data) mu_top
    (RC.core (Core.c (c pf))) m1 (cast pf0 (RC.core (Core.c (d pf)))) m2.
Proof.
case: R_match=> []pf0 []? []mu_top []? []A B _ _ _ _ _ _.  
by move/head_match=> C D; exists pf0, mu_top.
Qed.

Lemma R_AllDisjointS (mu_trash mu_top : frame_pkg) (mus : seq frame_pkg) :
  All2_aux DisjointLS mu_trash $ map (Inj.mu \o frame_mu0) $ mu_top :: mus -> 
  All2 (rel_inv_pred \o frame_mu0) (mu_top :: mus) -> 
  (AllDisjoint locBlocksSrc \o map (Inj.mu \o frame_mu0)) 
  $ mu_trash :: mu_top :: mus.
Proof.
set P := (rel_inv_pred \o _)=> A B.
have PC: forall mu mu', P mu mu' -> DisjointLS mu mu'.
  by move=> a b; rewrite/P; case=> _ _; case=> ? _ _ _ _ /=; rewrite DisjointC. 
(*why does Ssreflect apply fail here?*)
by move: (All2_sub B PC); split=> //; rewrite -All2_comp3.
Qed.

Lemma R_AllDisjointT (mu_trash mu_top : frame_pkg) (mus : seq frame_pkg) :
  All2_aux DisjointLT mu_trash $ map (Inj.mu \o frame_mu0) $ mu_top :: mus -> 
  All2 (rel_inv_pred \o frame_mu0) (mu_top :: mus) -> 
  (AllDisjoint locBlocksTgt \o map (Inj.mu \o frame_mu0)) 
  $ mu_trash :: mu_top :: mus.
Proof.
set P := (rel_inv_pred \o _)=> A B.
have PC: forall mu mu', P mu mu' -> DisjointLT mu mu'.
  by move=> a b; rewrite/P; case=> _ _; case=> _ ? _ _ _ /=; rewrite DisjointC. 
by move: (All2_sub B PC); split=> //; rewrite -All2_comp3.
Qed.

Lemma R_AllConsistent (mu_trash mu_top : frame_pkg) (mus : seq frame_pkg) :
  All2_aux Consistent mu_trash $ map (Inj.mu \o frame_mu0) $ mu_top :: mus -> 
  All2 (rel_inv_pred \o frame_mu0) (mu_top :: mus) -> 
  (AllConsistent \o map (Inj.mu \o frame_mu0)) 
  $ mu_trash :: mu_top :: mus.
Proof.
set P := (rel_inv_pred \o _)=> A B.
have PC: forall mu mu', P mu mu' -> Consistent mu mu'.
  move=> a b; rewrite/P; case=> _ _; case=> _ _ _ _ ? /=. 
  by apply: consistentC.
by move: (All2_sub B PC); split=> //; rewrite -All2_comp3.
Qed.

Lemma R_wd : SM_wd mu.
Proof.
move: (R_inv pf)=> []A []mu_trash []mu_top []mus []B _ _ _ _ C D E []F G []H I.
have J: All2 (rel_inv_pred \o (fun f : frame_pkg => f)) $ mu_top :: mus.
  by split=> //; rewrite -All2_aux_comp2.
rewrite B; apply: restrict_sm_WD=> //; apply: join_all_wd. 
by move: (R_AllDisjointS C J)=> /=; rewrite map_comp.
by move: (R_AllDisjointT D J)=> /=; rewrite map_comp.
by move: (R_AllConsistent E J)=> /=; rewrite map_comp.
Qed.

Arguments genvs_domain_eq_match_genvs {_ _ _ _ _ _} _.

Lemma R_isGlob b : isGlobalBlock my_ge b -> frgnBlocksSrc mu b.
Proof.
move: (R_inv pf)=> []A []mu_trash []mu_top []mus []B _ _ ? _ X Y Z []W V []U M.
rewrite B restrict_sm_frgnBlocksSrc; apply: join_all_isGlob=> //; split.
move=> b0; rewrite (genvs_domain_eq_isGlobal _ _ (my_ge_S (Core.i (c pf)))).
by case: (match_genv W)=> _ H4; apply/(H4 _).
by move: (frame_all_globs M); rewrite map_comp.
Qed.

Lemma R_pres_globs : Events.meminj_preserves_globals my_ge (extern_of mu).
Proof. 
move: (R_inv pf)=> []A []mu_trash []mu_top []mus []B _ ? _ _ X Y Z []W V []U M.
have J: All2 (rel_inv_pred \o (fun f : frame_pkg => f)) $ mu_top :: mus.
  by split=> //; rewrite -All2_aux_comp2.
rewrite B.
apply: restrict_sm_preserves_globals'=> //.
apply: join_all_preserves_globals=> //.
by move: (R_AllDisjointS X J)=> /=; rewrite map_comp.
by move: (R_AllDisjointT Y J)=> /=; rewrite map_comp.
by move: (R_AllConsistent Z J)=> /=; rewrite map_comp.
split=> //.
case: (match_genv W); rewrite -meminj_preserves_genv2blocks.
rewrite -(genvs_domain_eq_match_genvs (my_ge_S (Core.i (c pf)))).
by rewrite meminj_preserves_genv2blocks.
by apply: (tail_inv_preserves_globals (conj U M)).
move=> b; move/R_isGlob; rewrite B restrict_sm_frgnBlocksSrc. 
by apply: frgnBlocksSrc_vis.
Qed.

Lemma R_match_genv :
  Events.meminj_preserves_globals my_ge (extern_of mu) /\
  forall b : block, isGlobalBlock my_ge b -> frgnBlocksSrc mu b.
Proof. 
split; first by apply: R_pres_globs. 
by apply: R_isGlob. 
Qed.

Lemma R_match_visible : REACH_closed m1 (vis mu).
Proof.
by move: (R_inv pf)=> []A []mu_trash []mu_top []mus []B H.
Qed.

Lemma R_match_restrict (X : block -> bool) 
  (vis : forall b : block, vis mu b -> X b)
  (reach : REACH_closed m1 X) :
  R data (@restrict_sm_wd  _ (Inj.mk R_wd) _ vis reach) x1 m1 x2 m2.
Proof.
move: (R_inv pf)=> []A []mu_trash []mu_top []mus []B _ ? _ _ X0 Y Z []W V []U M.
simpl.
rewrite B.
rewrite restrict_sm_com.
rewrite restrict_sm_nest.
by rewrite -B.
move: vis.
rewrite B.
by rewrite vis_restrict_sm.
Qed.

Lemma R_match_validblocks : sm_valid mu m1 m2.
Proof. 
move: (R_inv pf)=> []A []mu_trash []mu_top []mus []B ? ? ? H X Y Z []W V []U M.
rewrite B /sm_valid /DOM restrict_sm_DomSrc /RNG restrict_sm_DomTgt.
apply: join_all_valid=> //=; split. 
by apply: (match_validblocks _ W).
by apply: (frame_all_valid M). 
Qed.

End R_lems.

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

(* genvs_domain_eq *)
- by apply: genvs_domain_eq_refl.

(* match_genv *)
- by move=> data mu c1 m1 c2 m2; apply: R_match_genv.

(* match_visible *)
- by apply: R_match_visible.

(* match_restrict *)
- by move=> data mu c1 m1 c2 m2 X H; apply: (R_match_restrict H).

(* match_validblocks *)
- by apply: R_match_validblocks.

(* core_initial *)
- by admit. (* TODO *)

(* NOT NEEDED diagram1 *)
- by admit.

(* real diagram *)
- move=> st1 m1 st1' m1' U1 STEP data st2 mu m2 U1_DEF INV.
case: STEP=> STEP STEP_EFFSTEP.
case: STEP.
 (* Case: corestep0 *)
 + move=> STEP. 
 set c1 := peekCore st1.
 have [c1' [STEP0 ST1']]: 
         exists c' : C (cores_S (Core.i c1)), 
         Coresem.corestep 
            (t := Effectsem.instance (coreSem (cores_S (Core.i c1)))) 
            (ge (cores_S (Core.i c1))) (RC.core (Core.c c1)) m1 c' m1' 
         /\ st1' = updCore st1 (Core.updC c1 c').
  { by move: STEP; rewrite/LinkerSem.corestep0=> [][]c' []B C; exists c'; split. }

 have EFFSTEP: 
        effect_semantics.effstep (coreSem (cores_S (Core.i c1))) 
        (ge (cores_S (Core.i c1))) U1 (RC.core (Core.c c1)) m1 c1' m1'.
  { move: (STEP_EFFSTEP STEP); rewrite/effstep0=> [][] c1'' [] STEP0' ST1''.
    by rewrite ST1'' in ST1'; rewrite -(updCore_inj_updC ST1'). }

 (* specialize core diagram at module (Core.i c1) *)
 move: (effcore_diagram _ _ _ _ _ (sims (Core.i c1))).  
 move/(_ _ _ _ _ _ EFFSTEP).

(*HERE: must introduce per-core effect tracking in lieue of U1_DEF*)
 move/(_ _ _ _ _ U1_DEF).
 move: (peek_match INV)=> []cd []mu_top MATCH.
 rewrite/c1.
 move/(_ _ _ _ MATCH).
 move=> []c2' []m2' []cd' []mu'.
 move=> []INCR []SEP []LOCALLOC []MATCH' []U2 []STEP' PERM.

 (* instantiate existentials *)
 set c2''  := cast' (peek_ieq INV) c2'.
 set st2'  := updCore st2 (Core.upd (peekCore st2) c2'').
 set data' := Lex.set (Core.i c1) cd' data.
 exists st2', m2', data', mu'; do 4 split=> //.

 (* re-establish invariant *)
 apply: Build_R; rewrite ST1'; rewrite /st2' /=.

 (* head_inv *)
 + exists (peek_ieq INV); apply: Build_head_inv. 
   have ->: cast (peek_ieq INV) (cast' (peek_ieq INV) c2') = c2' 
     by apply: cast_cast_eq.
   by rewrite Lex.gss; apply: MATCH'. 

 (* tail_inv *)
 + move: (R_tail INV); rewrite/s1/s2/st2'; generalize dependent st1.
   case=> ?; case; case=> //; case=> ai a l1 pf1. 
   case: st2=> ?; case; case=> //; case=> bi b l2 pf2 /= INV A B c1' D EQ.
   move: EQ A B D=> -> /= STEP_EFFSTEP STEP0.
   move=> STEP EFFSTEP cd MATCH c2' cd' MATCH' STEP_ORD. 
   move=> tlinv.
   have mu_wd: SM_wd mu by apply: match_sm_wd MATCH.
   have mu'_wd: SM_wd mu' by apply: match_sm_wd MATCH'.
   have H: tail_inv (Inj.mk mu'_wd) l1 l2 m1' m2'.
   apply: (@tail_inv_step (Inj.mk mu_wd) _ _ m1 m2 U1 U2)=> //=.
   by case: (effect_semantics.effax1 EFFSTEP)=> _ ?.
   case: STEP_ORD.
   - by case=> n; apply: effect_semantics.effstepN_unchanged.
   - case; case=> n=> EFFSTEPN _. 
     by apply: (effect_semantics.effstepN_unchanged EFFSTEPN).
   by apply: (corestep_fwd STEP).
   case: STEP_ORD.
   - by case=> n; apply: effect_semantics.effstepN_fwd.
   - case; case=> n=> EFFSTEPN _.
     by apply: (effect_semantics.effstepN_fwd EFFSTEPN).   
   by apply: (match_validblocks (sims ai) MATCH).
   by apply: H.

 (* matching execution *)
 + exists U2; split=> //; case: STEP'=> STEP'. 
   left; apply: stepPLUS_STEPPLUS=> //.
   set T := C \o cores_T.
   set P := fun ix (x : T ix) (y : T ix) => 
               effect_semantics.effstep_plus 
               (coreSem (cores_T ix)) (ge (cores_T ix)) U2 x m2 y m2'.
   set c2 := peekCore st2.
   change (P (Core.i c2) (Core.c c2) (cast.cast T (peek_ieq INV) c2')).
   by apply: cast_indnatdep2.

   case: STEP'=> [][]n EFFSTEPN ORD; right; split=> //. 
   exists n; apply: stepN_STEPN=> //.
   set T := C \o cores_T.
   set P := fun ix (x : T ix) (y : T ix) => 
               effect_semantics.effstepN
               (coreSem (cores_T ix)) (ge (cores_T ix)) n U2 x m2 y m2'.
   set c2 := peekCore st2.
   change (P (Core.i c2) (Core.c c2) (cast.cast T (peek_ieq INV) c2')).
   by apply: cast_indnatdep2.

   apply: Lex.ord_upd; admit. (*FIXME: tail_inv cannot existentially quant. cd's*)

- case=> <-; case=> NSTEP.
case CTX: (inContext st1)=> //.
case AT0: (Sem.at_external0 st1)=> [[[ef sig] args]|].
case FID: (Sem.fun_id ef)=> // [f].
case HDL: (Sem.handle f st1 args)=> // [st1''] EQ; subst st1''.
Arguments core_at_external 
  {F1 V1 C1 F2 V2 C2 Sem1 Sem2 ge1 ge2 entry_points s cd mu c1 m1 c2 m2 e vals1 ef_sig} _ _.
move: (R_head INV)=> []pf; move/head_match=> MATCH.
case: (core_at_external MATCH AT0)=> tinj []targs []tvinj TATEXT0.
have [st2' H]: (exists st2', Sem.handle f st2 targs = Some st2').
  admit.
exists st2', m2, data.

Admitted. (*WORK-IN-PROGRESS*)

End linkingSimulation.


