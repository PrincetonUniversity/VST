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
Require Import sepcomp.step_lemmas.
Require Import sepcomp.extspec.

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

Variable tZ : Type.
Variable espec_S : ext_spec tZ.
Variable N : pos.
Variable (cores_S cores_T : 'I_N -> Static.t). 
Variable fun_tbl : ident -> option 'I_N.
Variable entry_points : seq (val*val*signature).
Variable sims : forall i : 'I_N, 
  let s := cores_S i in
  let t := cores_T i in
  SM_simulation_inject s.(coreSem) t.(coreSem) s.(ge) t.(ge) entry_points.
Variable dets_S : forall i : 'I_N, effstep_fun (cores_S i).(coreSem).
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

Notation cast'' pf x := (cast (C \o cores_T) (sym_eq pf) x).

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

(* Initial core asserts that we match w/ SM_injection                     *)
(*   initial_SM DomS DomT                                                 *)
(*     (REACH m1 (fun b => isGlobalBlock ge1 b || getBlocks vals1 b))     *)
(*     (REACH m2 (fun b => isGlobalBlock ge2 b || getBlocks vals2 b)) j)  *)
(* where the clauses beginning REACH... give frgnSrc/Tgt respectively.    *)
(*                                                                        *)
(* I.e., we establish initially that                                      *)
(*                                                                        *)
(*   fun b => isGlobalBlock ge1 b || getBlocks vals1 b                    *)
(*                                                                        *)
(* is a subset of the visible set for the injection of the initialized    *)
(* core.  TODO: We need to record this fact (really, a slight             *)
(* modification of the invariant that accounts for return values as well) *)
(* as an invariant of execution for both the head and tail cores. Then    *)
(* the guarantees we get from RC executions (that write effects are       *)
(* limited to blocks in the RC of initial args, rets, local blocks) will  *)
(* imply that effects are also a subset of the visible region for each    *)
(* core.                                                                  *)

Section vis_inv.

Import Core.

Record vis_inv (c : t cores_S) mu : Type :=
  { vis_sup : {subset (RC.reach_basis my_ge c) <= vis mu} }.

End vis_inv.

Record frame_inv 
  cd0 mu0 z m10 m1 e1 ef_sig1 vals1 m20 m2 e2 ef_sig2 vals2 : Prop :=
  { (* local definitions *)
    pubSrc := [predI (locBlocksSrc mu0) & REACH m10 (exportedSrc mu0 vals1)] 
  ; pubTgt := [predI (locBlocksTgt mu0) & REACH m20 (exportedTgt mu0 vals2)] 
  ; nu0    := replace_locals mu0 pubSrc pubTgt

    (* unary invariants on mu0,m10,m20 *)
  ; frame_inj0  : Mem.inject (as_inj mu0) m10 m20
  ; frame_valid : sm_valid mu0 m10 m20 
  ; frame_match : (sims c.(i)).(match_state) cd0 mu0 
                    (RC.core c.(Core.c)) m10 (cast'' pf (RC.core d.(Core.c))) m20 
  ; frame_at1   : at_external (cores_S c.(i)).(coreSem) (RC.core c.(Core.c))
                    = Some (e1, ef_sig1, vals1) 
  ; frame_at2   : at_external (cores_T c.(i)).(coreSem) (cast'' pf (RC.core d.(Core.c))) 
                    = Some (e2, ef_sig2, vals2) 
  ; frame_vinj  : Forall2 (val_inject (as_inj mu0)) vals1 vals2  

    (* source state invariants *)
  ; frame_vis   : vis_inv c mu0
  ; frame_safe  : forall n, 
                  safeN (RC.effsem (cores_S c.(i)).(coreSem)) 
                  espec_S (cores_S c.(i)).(ge) n z c m10 

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

Section rel_inv_pred_lems.

Context mu pkg (rinv : rel_inv_pred mu pkg).

Lemma relinv_DisjointLS : DisjointLS mu (frame_mu0 pkg).
Proof. by case: rinv=> _ _; case; move/DisjointC. Qed.

Lemma relinv_DisjointLT : DisjointLT mu (frame_mu0 pkg).
Proof. by case: rinv=> _ _; case=> _; move/DisjointC. Qed.

Lemma relinv_consistent : consistent (extern_of mu) (extern_of (frame_mu0 pkg)).
Proof. by case: rinv=> _ _; case=> _ _ _ _; move/consistentC. Qed.

End rel_inv_pred_lems.

Section rel_inv_pred_all_lems.

Context mu mus (all_rinv : All (rel_inv_pred mu) mus).

Lemma relinv_AllDisjointLS : 
  All [eta DisjointLS mu] $ map (Inj.mu \o frame_mu0) mus.
Proof.
move: all_rinv; elim: mus=> // mu0 mus' IH /= => [][]A B; split.
by apply: (relinv_DisjointLS A).
by apply: IH.
Qed.

Lemma relinv_AllDisjointLT : 
  All [eta DisjointLT mu] $ map (Inj.mu \o frame_mu0) mus.
Proof.
move: all_rinv; elim: mus=> // mu0 mus' IH /= => [][]A B; split.
by apply: (relinv_DisjointLT A).
by apply: IH.
Qed.

Lemma relinv_All_consistent :
  All (fun mu2 => consistent (extern_of mu) (extern_of mu2)) 
  $ map (Inj.mu \o frame_mu0) mus.
Proof.
move: all_rinv; elim: mus=> // mu0 mus' IH /= => [][]A B; split.
by apply: (relinv_consistent A).
by apply: IH.
Qed.

End rel_inv_pred_all_lems.

Section rel_inv_pred_all2_lems.

Context mus 
  (all_rinv : All2 (fun mu1 mu2 => 
   rel_inv_pred (Inj.mu \o frame_mu0 $ mu1) mu2) mus).

Lemma relinv_All2DisjointLS : 
  All2 DisjointLS $ map (Inj.mu \o frame_mu0) mus.
Proof.
move: all_rinv; elim: mus=> // mu0 mus' IH /= => [][]A B; split.
by apply: (relinv_AllDisjointLS A).
by apply: IH.
Qed.

Lemma relinv_All2DisjointLT : 
  All2 DisjointLT $ map (Inj.mu \o frame_mu0) mus.
Proof.
move: all_rinv; elim: mus=> // mu0 mus' IH /= => [][]A B; split.
by apply: (relinv_AllDisjointLT A).
by apply: IH.
Qed.

Lemma relinv_AllConsistent :
  AllConsistent $ map (Inj.mu \o frame_mu0) mus.
Proof.
move: all_rinv; elim: mus=> // mu0 mus' IH /= => [][]A B; split.
by apply: (relinv_All_consistent A).
by apply: IH.
Qed.

End rel_inv_pred_all2_lems.

Section trash_inv.

Record trash_inv mu_trash mu_top mus m1 m2 : Type :=
  { trash_presglob : Events.meminj_preserves_globals my_ge $ extern_of mu_trash
  ; trash_isglob   : (forall b, isGlobalBlock my_ge b -> frgnBlocksSrc mu_trash b)
  ; trash_valid    : sm_valid mu_trash m1 m2
  ; trash_disj_S   : All (DisjointLS mu_trash) $ map (Inj.mu \o frame_mu0) $ mu_top :: mus
  ; trash_disj_T   : All (DisjointLT mu_trash) $ map (Inj.mu \o frame_mu0) $ mu_top :: mus
  ; trash_consist  : All (Consistent mu_trash) $ map (Inj.mu \o frame_mu0) $ mu_top :: mus }.

End trash_inv.

Section head_inv.

Import Core.

Variables (c : t cores_S) (d : t cores_T). 
Variable  (pf : c.(i)=d.(i)).

Record head_inv cd mu mus z m1 m2 : Type :=
  { head_match : (sims c.(i)).(match_state) cd mu 
                 (RC.core c.(Core.c)) m1 (cast'' pf (RC.core d.(Core.c))) m2 
  ; head_rel   : All (rel_inv_pred mu) mus 
  ; head_vis   : vis_inv c mu 
  ; head_safe  : forall n, 
                 safeN (RC.effsem (cores_S c.(i)).(coreSem)) 
                 espec_S (cores_S c.(i)).(ge) n z c m1 }.

End head_inv.

Section head_inv_lems.

Context c d pf cd mu mus z m1 m2 (inv : @head_inv c d pf cd mu mus z m1 m2).

Lemma head_AllDisjointLS : 
  All (DisjointLS mu) \o map (Inj.mu \o frame_mu0) $ mus.
Proof.
move: (head_rel inv); elim: mus=> // mu0 mus' IH /= []A B; split.
by apply: (relinv_DisjointLS A).
by apply: IH.
Qed.

Lemma head_AllDisjointLT : 
  All (DisjointLT mu) \o map (Inj.mu \o frame_mu0) $ mus.
Proof.
move: (head_rel inv); elim: mus=> // mu0 mus' IH /= []A B; split.
by apply: (relinv_DisjointLT A).
by apply: IH.
Qed.

Lemma head_AllConsistent : 
  All (fun mu2 => consistent (extern_of mu) (extern_of mu2)) 
      \o map (Inj.mu \o frame_mu0) 
  $ mus.
Proof.
move: (head_rel inv); elim: mus=> // mu0 mus' IH /= []A B; split.
by apply: (relinv_consistent A).
by apply: IH.
Qed.

Lemma head_globs b : isGlobalBlock my_ge b -> frgnBlocksSrc mu b.
Proof.
case: (match_genv $ head_match inv)=> A; move/(_ b).
by rewrite (genvs_domain_eq_isGlobal _ _ (my_ge_S (Core.i c))).
Qed.

Lemma head_presglobs : Events.meminj_preserves_globals my_ge (extern_of mu).
Proof.
case: (match_genv $ head_match inv)=> A.
rewrite -meminj_preserves_genv2blocks.
rewrite (genvs_domain_eq_match_genvs (my_ge_S (Core.i c))).
by rewrite meminj_preserves_genv2blocks.
Qed.

Lemma head_valid : sm_valid mu m1 m2.
Proof.
by case: inv=> // A _ _ _; apply: (match_validblocks _ A).
Qed.

End head_inv_lems.

Import seq.

Fixpoint frame_all (mus : seq frame_pkg) (z : tZ) m1 m2 s1 s2 :=
  match mus, s1, s2 with
    | Build_frame_pkg mu0 m10 m20 _ :: mus', c :: s1', d :: s2' => 
      [/\ exists (pf : c.(Core.i)=d.(Core.i)) cd0,
          exists e1 ef_sig1 vals1,
          exists e2 ef_sig2 vals2, 
            @frame_inv c d pf cd0 mu0 z
            m10 m1 e1 ef_sig1 vals1 m20 m2 e2 ef_sig2 vals2
        & frame_all mus' z m1 m2 s1' s2']
    | nil,nil,nil => True
    | _,_,_ => False
  end.

Definition tail_inv mus (z : tZ) s1 s2 m1 m2 :=
  [/\ All2 (rel_inv_pred \o frame_mu0) mus & frame_all mus z m1 m2 s1 s2].

Lemma frame_all_inv mu0 z m10 m20 x mus m1 m2 s1 s2 :
  frame_all (@Build_frame_pkg mu0 m10 m20 x :: mus) z m1 m2 s1 s2 -> 
  exists c s1' d s2',
    [/\ s1 = c :: s1'
      , s2 = d :: s2' 
      & exists (pf : c.(Core.i)=d.(Core.i)) cd0,
        exists e1 ef_sig1 vals1,
        exists e2 ef_sig2 vals2, 
          @frame_inv c d pf cd0 mu0 z
          m10 m1 e1 ef_sig1 vals1 m20 m2 e2 ef_sig2 vals2
          /\ frame_all mus z m1 m2 s1' s2'].
Proof.
case: s1=> // c s1'; case: s2=> // d s2' /=.
move=> [][]pf => [][]cd []ef1 []sig1 []vals1 []ef2 []sig2 []vals2 A B.
exists c, s1', d, s2'; split=> //.
by exists pf, cd, ef1, sig1, vals1, ef2, sig2, vals2; split.
Qed.

Lemma frame_all_match mu0 m10 m20 x mus z m1 m2 s1 s2 :
  frame_all (@Build_frame_pkg mu0 m10 m20 x :: mus) z m1 m2 s1 s2 -> 
  exists c s1' d s2',
    [/\ s1 = c :: s1'
      , s2 = d :: s2' 
      & exists (pf : c.(Core.i)=d.(Core.i)) cd0,
        (sims c.(Core.i)).(match_state) cd0 mu0 
          (RC.core c.(Core.c)) m10 (cast'' pf (RC.core d.(Core.c))) m20].
Proof.
case: s1=> // c s1'; case: s2=> // d s2' /=.
move=> [][]pf => [][]cd []ef1 []sig1 []vals1 []ef2 []sig2 []vals2 A B.
exists c, s1', d, s2'; split=> //.
by exists pf, cd; case: A.
Qed.

Lemma frame_all_fwd1 pkg mus z m1 m2 s1 s2 :
  frame_all (pkg :: mus) z m1 m2 s1 s2 -> 
  mem_forward pkg.(frame_m10) m1.
Proof.
case: pkg=> ? ? ? ?.
move/frame_all_inv=> []? []? []? []? []? ? []? []? []? []? []? []? []? []? [].
by case.
Qed.

Lemma frame_all_fwd2 pkg mus z m1 m2 s1 s2 :
  frame_all (pkg :: mus) z m1 m2 s1 s2 -> 
  mem_forward pkg.(frame_m20) m2.
Proof.
case: pkg=> ? ? ? ?.
move/frame_all_inv=> []? []? []? []? []? ? []? []? []? []? []? []? []? []? [].
by case.
Qed.

Lemma frame_all_tail pkg mus z m1 m2 s1 s2 :
  frame_all (pkg :: mus) z m1 m2 s1 s2 -> 
  frame_all mus z m1 m2 (STACK.pop s1) (STACK.pop s2).
Proof.
case: pkg=> ? ? ? ?.
move/frame_all_inv=> []? []? []? []? []-> ->. 
by move=> []? []? []? []? []? []? []? []? [] _.
Qed.

Section frame_all_lems.

Context mus z m1 m2 s1 s2 (frameall : frame_all mus z m1 m2 s1 s2).

Lemma frame_all_globs :
  All (fun mu0 => forall b, isGlobalBlock my_ge b -> frgnBlocksSrc mu0 b)  
    $ map (Inj.mu \o frame_mu0) mus.
Proof.
move: frameall.
move: m1 m2 s1 s2; elim: mus=> //; case=> mu' ? ? ? mus' IH m1' m2' s1' s2' A.
move: (frame_all_inv A)=> []c []s1'' []d []s2'' []_ _.
move=> []pf []cd []? []? []? []? []? []? []B C.
case: B=> ? ? ? ? ?; move/match_genv=> []_ D; split.
by rewrite (genvs_domain_eq_isGlobal _ _ (my_ge_S (Core.i c))); apply: D.
by apply: (IH _ _ _ _ C).
Qed.

Lemma frame_all_presglobs :
  All (fun mu0 => Events.meminj_preserves_globals my_ge (extern_of mu0))
    $ map (Inj.mu \o frame_mu0) mus.
Proof.
move: frameall.
move: m1 m2 s1 s2; elim: mus=> //; case=> mu' ? ? ? mus' IH m1' m2' s1' s2' A.
move: (frame_all_inv A)=> []c []s1'' []d []s2'' []_ _.
move=> []pf []cd []? []? []? []? []? []? []B C.
case: B=> ? ? ? ? ?; move/match_genv=> []D _; split=> /=.
rewrite -meminj_preserves_genv2blocks.
rewrite (genvs_domain_eq_match_genvs (my_ge_S (Core.i c))).
by rewrite meminj_preserves_genv2blocks.
by apply: (IH _ _ _ _ C).
Qed.

Lemma frame_all_valid :
  All (fun mu0 => sm_valid (Inj.mu mu0) m1 m2) $ map frame_mu0 mus.
Proof.
move: frameall.
move: m1 m2 s1 s2; elim: mus=> //; case=> mu' ? ? ? mus' IH m1' m2' s1' s2' A.
move: (frame_all_inv A)=> []c []s1'' []d []s2'' []_ _.
move=> []pf []cd []? []? []? []? []? []? []B C.
case: B=> ? ? ? ? val; move/match_genv=> []_ D; split=> /=.
by apply: (sm_valid_fwd val).
by apply: (IH _ _ _ _ C).
Qed.

End frame_all_lems.

Lemma tail_inv_inv mu0 m10 m20 (z : tZ) x mus s1 s2 m1 m2 :
  tail_inv (@Build_frame_pkg mu0 m10 m20 x :: mus) z s1 s2 m1 m2 -> 
  exists c s1' d s2',
    [/\ s1 = c :: s1'
      , s2 = d :: s2' 
      , (exists (pf : c.(Core.i)=d.(Core.i)) cd0,
         exists e1 ef_sig1 vals1,
         exists e2 ef_sig2 vals2, 
           @frame_inv c d pf cd0 mu0 z
           m10 m1 e1 ef_sig1 vals1 m20 m2 e2 ef_sig2 vals2)
       & tail_inv mus z (STACK.pop s1) (STACK.pop s2) m1 m2].
Proof.
case; case=> H1 H2; move/frame_all_inv=> []c []s1' []d []s2' []B C.
move=> []pf []cd []ef1 []sig1 []vals1 []ef2 []sig2 []vals2 []D E.
exists c,s1',d,s2'; split=> //.
by exists pf,cd,ef1,sig1,vals1,ef2,sig2,vals2.
by split=> //; rewrite B C.
Qed.

Lemma tail_inv_match mu0 m10 m20 z x mus s1 s2 m1 m2 :
  tail_inv (@Build_frame_pkg mu0 m10 m20 x :: mus) z s1 s2 m1 m2 -> 
  exists c s1' d s2',
    [/\ s1 = c :: s1'
      , s2 = d :: s2' 
      & exists (pf : c.(Core.i)=d.(Core.i)) cd0,
        (sims c.(Core.i)).(match_state) cd0 mu0 
          (RC.core c.(Core.c)) m10 (cast'' pf (RC.core d.(Core.c))) m20].
Proof. by move=> []_; move/frame_all_match. Qed.

Section tail_inv_lems.

Context mus z s1 s2 m1 m2 (tlinv : tail_inv mus z s1 s2 m1 m2).

Lemma tail_AllDisjointLS : 
  AllDisjoint locBlocksSrc $ map (Inj.mu \o frame_mu0) $ mus.
Proof. by case: tlinv; move/relinv_All2DisjointLS. Qed.

Lemma tail_AllDisjointLT : 
  AllDisjoint locBlocksTgt $ map (Inj.mu \o frame_mu0) $ mus.
Proof. by case: tlinv; move/relinv_All2DisjointLT. Qed.

Lemma tail_AllConsistent :
  AllConsistent $ map (Inj.mu \o frame_mu0) $ mus.
Proof. by case: tlinv; move/relinv_AllConsistent. Qed.

Lemma tail_globs :
  All (fun mu0 => forall b, isGlobalBlock my_ge b -> frgnBlocksSrc mu0 b)  
    [seq Inj.mu x | x <- [seq frame_mu0 x | x <- mus]].
Proof. case: tlinv=> _; move/frame_all_globs; by rewrite map_comp. Qed.

Lemma tail_presglobs :
  All (Events.meminj_preserves_globals my_ge \o extern_of)
    [seq Inj.mu x | x <- [seq frame_mu0 x | x <- mus]].
Proof. 
case: tlinv=> _; move/frame_all_presglobs.
by rewrite map_comp.
Qed.

Lemma tail_valid :
  All (fun mu0 => sm_valid mu0 m1 m2)
    [seq Inj.mu x | x <- [seq frame_mu0 x | x <- mus]].
Proof.  by case: tlinv=> _; move/frame_all_valid; rewrite -!All_comp. Qed.

End tail_inv_lems.

Lemma all_wrt_callers_switch T P (a b : T) (l : seq T) :
  All (P b) l -> All2 P (a :: l) -> All2 P (b :: l).
Proof. by elim: l a b=> // a' l' IH a b /= []A B [][]C D []E F. Qed.

Definition restrict_sm_wd m1
  (mu : Inj.t) (X : block -> bool)
  (vis_pf : forall b : block, vis mu b -> X b)
  (rc_pf  : REACH_closed m1 X) : Inj.t :=
  Inj.mk (restrict_sm_WD _ (Inj_wd mu) X vis_pf).

Section step_lems.

Context
(mu : Inj.t) m1 m2
(Esrc Etgt : Values.block -> BinNums.Z -> bool) 
(mu' : Inj.t) m1' m2'
(unch1 : Memory.Mem.unchanged_on (fun b ofs => Esrc b ofs = false) m1 m1')
(unch2 : Memory.Mem.unchanged_on (fun b ofs => Etgt b ofs = false) m2 m2')
(fwd1 : mem_forward m1 m1')
(fwd2 : mem_forward m2 m2')
(val : forall b ofs, Esrc b ofs -> Mem.valid_block m1 b -> vis mu b) 
(effs : 
   (forall (b0 : block) (ofs : Z),
   Etgt b0 ofs = true ->
   Mem.valid_block m2 b0 /\
   (locBlocksTgt mu b0 = false ->
    exists (b1 : block) (delta1 : Z),
      foreign_of mu b1 = Some (b0, delta1) /\
      Esrc b1 (ofs - delta1) = true /\
      Mem.perm m1 b1 (ofs - delta1) Max Nonempty)))
(valid : sm_valid mu m1 m2)
(incr : intern_incr mu mu')
(sep : sm_inject_separated mu mu' m1 m2).

Lemma rel_inv_pred_step pkg 
  (fwd10 : mem_forward pkg.(frame_m10) m1)
  (fwd20 : mem_forward pkg.(frame_m20) m2) :
  rel_inv_pred mu pkg -> rel_inv_pred mu' pkg.
Proof.
move=> []incr' sep' disj.
split; first by apply: (incr_trans incr' (intern_incr_incr incr)).
have incr'': inject_incr (as_inj mu) (as_inj mu').
  apply: intern_incr_as_inj=> /=; first by apply: incr.
  by generalize dependent mu'; case.
by apply: (sm_sep_step (frame_val pkg) sep' sep fwd10 fwd20 incr'').
by apply: (disjinv_intern_step disj incr fwd10 fwd20 sep' sep (frame_val pkg)).
Qed.

Lemma all_relinv_step mus z s1 s2 :
  frame_all mus z m1 m2 s1 s2 -> 
  All (rel_inv_pred mu) mus -> 
  All (rel_inv_pred mu') mus.
Proof.
elim: mus s1 s2=> // pkg mus' IH s1 s2 A /= => [][] B C.
move: (rel_inv_pred_step (frame_all_fwd1 A) (frame_all_fwd2 A) B)=> D.
by split=> //; last by apply: (IH _ _ (frame_all_tail A) C).
Qed.

Lemma frame_all_step mus z s1 s2 :
  All (rel_inv_pred mu) mus -> 
  frame_all mus z m1 m2 s1 s2 -> 
  frame_all mus z m1' m2' s1 s2.
Proof.
elim: mus s1 s2=> // pkg mus' IH s1' s2' E.
simpl in E; case: E=> E F.
case: pkg E=> mu0 m10 m20 val' E.

move/frame_all_inv.
move=> []c []s1'' []d []s2'' []-> ->.
move=> []pf []cd []e1 []sig1 []vals1 []e2 []sig2 []vals2.
move=> []inv all /=.

split.
exists pf,cd,e1,sig1,vals1,e2,sig2,vals2.

case: inv=> ? ? ? ? val'' frmatch ? ? ? visinv safe fwd1' fwd2' ? ?. 
apply: Build_frame_inv=> //.

by apply: (mem_forward_trans _ _ _ fwd1' fwd1). 
by apply: (mem_forward_trans _ _ _ fwd2' fwd2). 

apply: (mem_lemmas.unchanged_on_trans m10 m1 m1')=> //.
set pubSrc' := [predI locBlocksSrc mu0 & REACH m10 (exportedSrc mu0 vals1)].
set pubTgt' := [predI locBlocksTgt mu0 & REACH m20 (exportedTgt mu0 vals2)].
set mu0'    := replace_locals mu0 pubSrc' pubTgt'.
have wd: SM_wd mu0' by apply: replace_reach_wd.
have J: disjinv mu0' mu by case: E=> /= ? ? ?; apply: disjinv_call.
apply: (@disjinv_unchanged_on_src (Inj.mk wd) mu Esrc)=> //.
move: (sm_valid_smvalid_src _ _ _ val')=> ?.
apply: smvalid_src_replace_locals=> //=.
by apply: (smvalid_src_fwd fwd1').

apply: (mem_lemmas.unchanged_on_trans m20 m2 m2')=> //.
set pubSrc' := [predI locBlocksSrc mu0 & REACH m10 (exportedSrc mu0 vals1)].
set pubTgt' := [predI locBlocksTgt mu0 & REACH m20 (exportedTgt mu0 vals2)].
set mu0'    := replace_locals mu0 pubSrc' pubTgt'.
have J: disjinv mu0' mu by case: E=> /= ? ? ?; apply: disjinv_call.
have wd: SM_wd mu0' by apply: replace_reach_wd.
apply: (@disjinv_unchanged_on_tgt (Inj.mk wd) mu Esrc Etgt 
  m10 m1 m2 m2' fwd1')=> //.
move=> b'; case: val''; move/(_ b')=> I _ Q; apply: I.
by rewrite replace_locals_DOM in Q.

by eapply IH; eauto.
Qed.

Lemma tail_inv_step mus z s1 s2 :
  All (rel_inv_pred mu) mus -> 
  tail_inv mus z s1 s2 m1 m2 -> 
  tail_inv mus z s1 s2 m1' m2'.
Proof. 
by move=> A []B C; split=> //; last by apply: frame_all_step. 
Qed.

Lemma vis_inv_step c c' :
  vis_inv c mu -> 
  RC.args (Core.c c)=RC.args (Core.c c') -> 
  RC.rets (Core.c c)=RC.rets (Core.c c') -> 
  (forall b, 
   RC.locs (Core.c c) b=false -> 
   RC.locs (Core.c c') b -> 
   locBlocksSrc mu' b) -> 
  vis_inv c' mu'.
Proof.
move=> E A B C; move: E.
case=> E; apply: Build_vis_inv=> b F; move: {E}(E b)=> E.
move: E F; rewrite/RC.reach_basis/in_mem/= => E.
move/orP=> [|F].
rewrite -A -B=> F. 
by apply: (intern_incr_vis _ _ incr); apply: E; apply/orP; left.
case G: (RC.locs (Core.c c) b). 
by apply: (intern_incr_vis _ _ incr); apply: E; apply/orP; right.
by move: (C _ G F)=> H; rewrite/vis H.
Qed.

Lemma core_upd_args (c : Core.t cores_S) c' : 
  RC.args (Core.c c) = RC.args (Core.c (Core.updC c c')).
Proof.
by rewrite/Core.updC/RC.updC; case: (Core.c c)=> ? ? ? ?.
Qed.

Lemma core_upd_rets (c : Core.t cores_S) c' : 
  RC.rets (Core.c c) = RC.rets (Core.c (Core.updC c c')).
Proof.
by rewrite/Core.updC/RC.updC; case: (Core.c c)=> ? ? ? ?.
Qed.

Lemma head_inv_step 
    c d (pf : Core.i c=Core.i d) c' (d' : RC.state (C (cores_T (Core.i d))))
    cd cd' mus z s1 s2 U :
  head_inv pf cd mu mus z m1 m2 -> 
  frame_all mus z m1 m2 s1 s2 -> 
  RC.args (Core.c c)=RC.args c' -> 
  RC.rets (Core.c c)=RC.rets c' -> 
  RC.locs c' = (fun b => RC.locs (Core.c c) b || RC.newBlocks m1 m1' b) ->
  effect_semantics.effstep 
    (coreSem (cores_S (Core.i c))) (ge (cores_S (Core.i c))) U 
    (RC.core (Core.c c)) m1 (RC.core c') m1' -> 
  match_state (sims (Core.i (Core.upd c c'))) cd' mu'
    (RC.core (Core.c (Core.upd c c'))) m1'
    (cast'' pf (RC.core (Core.c (Core.upd d d')))) m2' -> 
  (forall b : block,
   RC.locs (Core.c c) b = false ->
   RC.locs c' b -> locBlocksSrc mu' b) -> 
  @head_inv (Core.upd c c') (Core.upd d d') pf cd' mu' mus z m1' m2'.
Proof.
move=> hdinv frame args rets mylocs effstep mtch locs.
apply: Build_head_inv=> //.
by apply: (all_relinv_step frame); apply: (head_rel hdinv).
by case: hdinv=> ? ? A _; apply: (vis_inv_step A)=> //.
case: hdinv=> ? ? _ A; move: (effax1 effstep)=> []step _. 
move=> n; move: (A (S n))=> /=; rewrite/RC.at_external/RC.halted.
rewrite (corestep_not_at_external _ _ _ _ _ _ step).
rewrite (corestep_not_halted _ _ _ _ _ _ step).
move=> []c1'' []m1'' [][]U1' []effstep' []SUB []eq1 []eq2 eq3 SAFE'. 
case: (dets_S effstep effstep')=> []eqU []eq4 eq5; move: SAFE'.
have ->: c1'' = c'.
  case: c1'' effstep' eq1 eq2 eq3 eq4. 
  case: c' cd' mtch args rets effstep locs mylocs step=> /= ? ? ? ? ? ? -> ->.
  move=> ? ? -> ? ? ? ? ? ? -> -> -> <-.
  by rewrite eq5.
by rewrite eq5.
Qed.

End step_lems.

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
    exists (pf : c.(Core.i)=d.(Core.i)) mu_trash mu_top mus z, 
    let mu_tot := join_all (frame_mu0 mu_trash) $ map frame_mu0 (mu_top :: mus) in
    [/\ mu = restrict_sm mu_tot (vis mu_tot) 
      , REACH_closed m1 (vis mu)
      , trash_inv mu_trash mu_top mus m1 m2
      , @head_inv c d pf (Lex.get c.(Core.i) data) mu_top mus z m1 m2 
      & tail_inv mus z (pop s1) (pop s2) m1 m2] }.

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
  (cast'' peek_ieq (RC.core (Core.c (peekCore x2)))) m2.
Proof.
move: (R_inv pf)=> []A []? []mu_top []? []? []? _ _. 
move/head_match=> MATCH ?.
have ->: (cast'' peek_ieq (RC.core (Core.c (peekCore x2))) 
         = cast'' A (RC.core (Core.c (peekCore x2))))
  by f_equal; f_equal; apply proof_irr.
by exists (Lex.get (Core.i (peekCore x1)) data), mu_top.
Qed.

Lemma R_AllDisjointS 
    (mu_trash mu_top : frame_pkg) (mus : seq frame_pkg) 
    c d (eq : Core.i c=Core.i d) cd z s1 s2 :
  trash_inv mu_trash mu_top mus m1 m2 -> 
  head_inv eq cd mu_top mus z m1 m2 -> 
  tail_inv mus z s1 s2 m1 m2 -> 
  AllDisjoint locBlocksSrc \o map (Inj.mu \o frame_mu0) 
    $ mu_trash :: mu_top :: mus.
Proof.
move=> /= A B C; split; first by move: (trash_disj_S A); move=> /= [].
move: (head_AllDisjointLS B)=> D; split=> //. 
by apply: (tail_AllDisjointLS C).
Qed.

Lemma R_AllDisjointT
    (mu_trash mu_top : frame_pkg) (mus : seq frame_pkg) 
    c d (eq : Core.i c=Core.i d) cd z s1 s2 :
  trash_inv mu_trash mu_top mus m1 m2 -> 
  head_inv eq cd mu_top mus z m1 m2 -> 
  tail_inv mus z s1 s2 m1 m2 -> 
  AllDisjoint locBlocksTgt \o map (Inj.mu \o frame_mu0) 
    $ mu_trash :: mu_top :: mus.
Proof.
move=> /= A B C; split; first by move: (trash_disj_T A); move=> /= [].
move: (head_AllDisjointLT B)=> D; split=> //. 
by apply: (tail_AllDisjointLT C).
Qed.

Lemma R_AllConsistent 
    (mu_trash mu_top : frame_pkg) (mus : seq frame_pkg) 
    c d (eq : Core.i c=Core.i d) cd z s1 s2 :
  trash_inv mu_trash mu_top mus m1 m2 -> 
  head_inv eq cd mu_top mus z m1 m2 -> 
  tail_inv mus z s1 s2 m1 m2 -> 
  AllConsistent \o map (Inj.mu \o frame_mu0) 
    $ mu_trash :: mu_top :: mus.
Proof.
move=> /= A B C; split; first by move: (trash_consist A); move=> /= [].
move: (head_AllConsistent B)=> D; split=> //. 
by apply: (tail_AllConsistent C).
Qed.

Lemma R_wd : SM_wd mu.
Proof.
move: (R_inv pf)=> []A []mu_trash []mu_top []mus []z []B C D E F.
rewrite B; apply: restrict_sm_WD=> //; apply: join_all_wd.
by move: (R_AllDisjointS D E F)=> /=; rewrite map_comp.
by move: (R_AllDisjointT D E F)=> /=; rewrite map_comp.
by move: (R_AllConsistent D E F)=> /=; rewrite map_comp.
Qed.

Lemma R_isGlob b : isGlobalBlock my_ge b -> frgnBlocksSrc mu b.
Proof.
move: (R_inv pf)=> []A []mu_trash []mu_top []mus []z []B ? X Y Z.
rewrite B restrict_sm_frgnBlocksSrc; apply: join_all_isGlob.
by apply: (trash_isglob X).
split; first by apply: (head_globs Y). 
by apply: (tail_globs Z).
Qed.

Lemma R_presglobs : Events.meminj_preserves_globals my_ge (extern_of mu).
Proof. 
move: (R_inv pf)=> []A []mu_trash []mu_top []mus []z []B ? X Y Z.
rewrite B. 
apply: restrict_sm_preserves_globals'.
apply: join_all_preserves_globals.
by apply: (trash_presglob X).
by move: (R_AllDisjointS X Y Z)=> /=; rewrite map_comp.
by move: (R_AllDisjointT X Y Z)=> /=; rewrite map_comp.
by move: (R_AllConsistent X Y Z)=> /=; rewrite map_comp.
split; first by apply: (head_presglobs Y).
by move: (tail_presglobs Z); rewrite !All_comp.
move=> b; move/R_isGlob; rewrite B restrict_sm_frgnBlocksSrc. 
by apply: frgnBlocksSrc_vis.
Qed.

Lemma R_match_genv :
  Events.meminj_preserves_globals my_ge (extern_of mu) /\
  forall b : block, isGlobalBlock my_ge b -> frgnBlocksSrc mu b.
Proof. 
split; first by apply: R_presglobs.
by apply: R_isGlob. 
Qed.

Lemma R_match_visible : REACH_closed m1 (vis mu).
Proof.
by move: (R_inv pf)=> []A []mu_trash []mu_top []mus []z []B H.
Qed.

Lemma R_match_restrict (X : block -> bool) 
  (vis : forall b : block, vis mu b -> X b)
  (reach : REACH_closed m1 X) :
  R data (@restrict_sm_wd  _ (Inj.mk R_wd) _ vis reach) x1 m1 x2 m2.
Proof.
move: (R_inv pf)=> []A []mu_trash []mu_top []mus []z []B ? Y Z W /=.
rewrite B restrict_sm_com restrict_sm_nest; first by rewrite -B.
by move: vis; rewrite B vis_restrict_sm.
Qed.

Lemma R_match_validblocks : sm_valid mu m1 m2.
Proof. 
move: (R_inv pf)=> []A []mu_trash []mu_top []mus []z []B ? X Y Z.
rewrite B /sm_valid /DOM restrict_sm_DomSrc /RNG restrict_sm_DomTgt.
apply: join_all_valid=> //=; first by apply: (trash_valid X).
split; first by apply: (head_valid Y).
by move: (tail_valid Z); rewrite -!All_comp.
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
 set c2 := peekCore st2.

 have [c1' [STEP0 [U1'_EQ ST1']]]:
   exists c1',
       Coresem.corestep 
         (t := RC.effsem (coreSem (cores_S (Core.i c1)))) 
         (ge (cores_S (Core.i c1))) (Core.c c1) m1 c1' m1' 
   /\ (forall b ofs, U1 b ofs -> 
       RC.reach_set (ge (cores_S (Core.i c1))) (Core.c c1) m1 b)
   /\ st1' = updCore st1 (Core.upd c1 c1').

  { move: (STEP_EFFSTEP STEP)=> EFFSTEP.
    move: STEP; rewrite/LinkerSem.corestep0=> [][]c' []B C. 
    exists c'; split=> //; split=> //.
    case: (R_inv INV)=> pf []pkg []mu_top []mus []z []E ? trinv hdinv tlinv.
    move: (head_safe hdinv); move/(_ (S O)); rewrite/safeN.
    rewrite (corestep_not_at_external _ _ _ _ _ _ B).
    rewrite (corestep_not_halted _ _ _ _ _ _ B).
    move=> []c1'' []m1'' [][]U1' []EFFSTEP' []SUB []eq1 []eq2 eq3 _. 
    move: SUB; cut (U1=U1'); first by move=> ->.
    move: EFFSTEP EFFSTEP'; rewrite/effstep0. 
    move=> []c1' []/=; rewrite/RC.effstep=> [][]EFFSTEP _ _.
    generalize dependent INV; move=> INV.
    have ->: c INV = c1.
      generalize dependent INV.
      by rewrite/c/peekCore; case=> /=; rewrite/s1/pf1; intros; f_equal.
    by intros; case: (dets_S EFFSTEP EFFSTEP'). }

 have EFFSTEP: 
    effect_semantics.effstep (coreSem (cores_S (Core.i c1))) 
    (ge (cores_S (Core.i c1))) U1 (RC.core (Core.c c1)) m1 (RC.core c1') m1'.

  { move: (STEP_EFFSTEP STEP); rewrite/effstep0=> [][] c1'' [] STEP0' ST1''.
    rewrite ST1'' in ST1'; rewrite -(updCore_inj_upd ST1'). 
    by move: STEP0'=> /=; rewrite/RC.effstep/= => [][]. }

 (* specialize core diagram at module (Core.i c1) *)
 move: (effcore_diagram _ _ _ _ _ (sims (Core.i c1))).  
 move/(_ _ _ _ _ _ EFFSTEP).
 case: (R_inv INV)=> pf []mu_trash []mupkg []mus []z []mu_eq.
 move=> rclosed trinv hdinv tlinv.

 have U1_DEF': forall b ofs, U1 b ofs -> vis mupkg b. admit.

 move: (head_match hdinv)=> MATCH.
 move/(_ _ _ _ _ U1_DEF' MATCH).
 move=> []c2' []m2' []cd' []mu_top0.
 move=> []INCR []SEP []LOCALLOC []MATCH' []U2 []STEP' PERM.

 have mu_top'_wd: SM_wd mu_top0. admit.
 set mu_top'   := Inj.mk mu_top'_wd.
 have mu_top'_valid: sm_valid mu_top' m1' m2'
   by apply: (match_validblocks _ MATCH').
 set mupkg' := Build_frame_pkg mu_top'_valid.

 (* instantiate existentials *)
 set c2_3   := cast' (peek_ieq INV) c2'.
 set c2''   := RC.upd_locs 
                 (fun b => RC.locs (Core.c c2) b || RC.newBlocks m2 m2' b)
                 (RC.updC c2_3 (Core.c c2)).
 set st2'   := updCore st2 (Core.upd c2 c2'').
 set data'  := Lex.set (Core.i c1) cd' data.
 set mu'    := restrict_sm 
                (join_all mu_trash $ mu_top' :: map frame_mu0 mus)
                (vis (join_all mu_trash $ mu_top' :: map frame_mu0 mus)).

 exists st2', m2', data', mu'. 

 split. admit. (*incr*)
 split. admit. (*sep*)
 split. admit. (*loc-alloc*)

 split.

 (* re-establish invariant *)
 apply: Build_R; rewrite ST1'; rewrite /st2'.

 exists pf, mu_trash, mupkg', mus, z; split=> //.

 admit. (*rc vis mu' - tricky*)
 admit. (*trinv - easy*)

(*HERE*)
 
 + apply: head_inv_step.
   (@head_inv_step mupkg m1 m2 mu_top' m1' m2'
                   (head_valid hdinv)
                   INCR 
                   SEP
                   (c INV) (d INV) pf c1' c2'').
                   (Lex.get (Core.i (c INV)) data) cd' mus z
                   (CallStack.callStack (s1 INV)) 
                   (CallStack.callStack (s2 INV)) 
                   U1).
                   frameall).


 + case: tlinv=> allrel frameall. Set Printing Implicit.

                   
                   _ _ _ _ _ _ _ _ _ _ _ _ _ _ frameall).
mu_top'_valid               
     intern_incr).


 + eapply head_inv_step; eauto.
   by apply: (corestep_fwd STEP0).
   case: STEP'=> A; first by apply: (effstep_plus_fwd _ _ _ _ _ _ _ A). 
   by case: A=> A _; apply: (effstep_star_fwd _ _ _ _ _ _ _ A).
   by apply: (match_validblocks _ MATCH).
   move: MATCH'; rewrite/data' Lex.gss /c2''.
   have ->: peek_ieq INV = pf by apply: proof_irr.
   have ->: cast pf (RC.core (Core.c (d INV))) = c2'.
     rewrite/RC.updC; case: (Core.c _)=> ? ? ? ? /=.
     by rewrite (@cast_cast_eq _ (fun i => C (cores_T i)) _ _ pf c2').
   by rewrite/RC.core/RC.updC/=; case: (Core.c c1).

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


