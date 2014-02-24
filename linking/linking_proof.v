(* standard Coq libraries *)

Require Import JMeq.

(* msl imports *)

Require Import msl.Axioms. (*for proof_irr*)

(* sepcomp imports *)

Require Import sepcomp.mem_lemmas.
Require Import sepcomp.core_semantics.
Require Import sepcomp.StructuredInjections.
Require Import sepcomp.effect_semantics.
Require Import sepcomp.reach. 
Require Import sepcomp.effect_simulations. 
Require Import sepcomp.effect_properties.
Require Import sepcomp.step_lemmas.
Require Import sepcomp.extspec.

Require Import sepcomp.arguments.

Require Import linking.pos.
Require Import linking.stack.
Require Import linking.cast.
Require Import linking.pred_lemmas.
Require Import linking.seq_lemmas.
Require Import linking.wf_lemmas.
Require Import linking.core_semantics_lemmas.
Require Import linking.inj_lemmas.
Require Import linking.reach_lemmas.
Require Import linking.compcert_linking.
Require Import linking.compcert_linking_lemmas.
Require Import linking.disjointness.
Require Import linking.rc_semantics.

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
  SM_simulation_inject 
  (RC.effsem s.(coreSem)) (RC.effsem t.(coreSem)) s.(ge) t.(ge) entry_points.
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

Notation rc_cast' pf x := (cast (RC.state \o C \o cores_T) pf x).

Notation rc_cast'' pf x := (cast (RC.state \o C \o cores_T) (sym_eq pf) x).

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
                   c.(Core.c) m10 (rc_cast'' pf d.(Core.c)) m20 
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
  ; trash_disj_S   : All (DisjointLS mu_trash) 
                       [seq (Inj.mu \o frame_mu0) x | x <- mu_top :: mus]
  ; trash_disj_T   : All (DisjointLT mu_trash) 
                       [seq (Inj.mu \o frame_mu0) x | x <-  mu_top :: mus]
  ; trash_consist  : All (Consistent mu_trash) 
                       [seq (Inj.mu \o frame_mu0) x | x <- mu_top :: mus] }.

End trash_inv.

Definition frgn_contained mu_trash mu mus :=
  forall b, 
    frgnBlocksSrc mu b -> 
    let mu_rest := join_all mu_trash (map frame_mu0 mus) 
    in locBlocksSrc mu_rest b || frgnBlocksSrc mu_rest b.

Section head_inv.

Import Core.

Variables (c : t cores_S) (d : t cores_T). 
Variable  (pf : c.(i)=d.(i)).

Record head_inv cd mu_trash mu mus z m1 m2 : Type :=
  { head_match : (sims c.(i)).(match_state) cd mu 
                 c.(Core.c) m1 (rc_cast'' pf d.(Core.c)) m2 
  ; head_rel   : All (rel_inv_pred mu) mus 
  ; head_vis   : vis_inv c mu 
  ; head_safe  : forall n, 
                 safeN (RC.effsem (cores_S c.(i)).(coreSem)) 
                 espec_S (cores_S c.(i)).(ge) n z c m1 
  ; head_ctned : frgn_contained mu_trash mu mus }.

End head_inv.

Section head_inv_lems.

Context c d pf cd mu_trash mu mus z m1 m2 
        (inv : @head_inv c d pf cd mu_trash mu mus z m1 m2).

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
by case: inv=> // A _ _ _ _; apply: (match_validblocks _ A).
Qed.

End head_inv_lems.

Import seq.

Fixpoint frame_all mu_trash (mus : seq frame_pkg) (z : tZ) m1 m2 s1 s2 :=
  match mus, s1, s2 with
    | Build_frame_pkg mu0 m10 m20 _ :: mus', c :: s1', d :: s2' => 
      [/\ exists (pf : c.(Core.i)=d.(Core.i)) cd0,
          exists e1 ef_sig1 vals1,
          exists e2 ef_sig2 vals2, 
            [/\ @frame_inv c d pf cd0 mu0 z
                  m10 m1 e1 ef_sig1 vals1 m20 m2 e2 ef_sig2 vals2
              & (forall b, 
                 frgnBlocksSrc mu0 b -> 
                 let mu_rest := join_all mu_trash (map frame_mu0 mus') 
                 in locBlocksSrc mu_rest b || frgnBlocksSrc mu_rest b)]
        & frame_all mu_trash mus' z m1 m2 s1' s2']
    | nil,nil,nil => True
    | _,_,_ => False
  end.

Definition tail_inv mu_trash mus (z : tZ) s1 s2 m1 m2 :=
  [/\ All2 (rel_inv_pred \o frame_mu0) mus 
    & frame_all mu_trash mus z m1 m2 s1 s2].

Lemma frame_all_inv mu_trash mu0 z m10 m20 x mus m1 m2 s1 s2 :
  frame_all mu_trash (@Build_frame_pkg mu0 m10 m20 x :: mus) 
            z m1 m2 s1 s2 -> 
  exists c s1' d s2',
    [/\ s1 = c :: s1'
      , s2 = d :: s2' 
      & exists (pf : c.(Core.i)=d.(Core.i)) cd0,
        exists e1 ef_sig1 vals1,
        exists e2 ef_sig2 vals2, 
          [/\ @frame_inv c d pf cd0 mu0 z
                m10 m1 e1 ef_sig1 vals1 m20 m2 e2 ef_sig2 vals2
            , (forall b, 
               frgnBlocksSrc mu0 b -> 
               let mu_rest := join_all mu_trash (map frame_mu0 mus) 
               in locBlocksSrc mu_rest b || frgnBlocksSrc mu_rest b)
            & frame_all mu_trash mus z m1 m2 s1' s2']].
Proof.
case: s1=> // c s1'; case: s2=> // d s2' /=.
move=> [][]pf => [][]cd []ef1 []sig1 []vals1 []ef2 []sig2 []vals2 []A B C.
exists c, s1', d, s2'; split=> //.
by exists pf, cd, ef1, sig1, vals1, ef2, sig2, vals2; split.
Qed.

Lemma frame_all_match mu_trash mu0 m10 m20 x mus z m1 m2 s1 s2 :
  frame_all mu_trash (@Build_frame_pkg mu0 m10 m20 x :: mus) 
            z m1 m2 s1 s2 -> 
  exists c s1' d s2',
    [/\ s1 = c :: s1'
      , s2 = d :: s2' 
      & exists (pf : c.(Core.i)=d.(Core.i)) cd0,
        (sims c.(Core.i)).(match_state) cd0 mu0 
        c.(Core.c) m10 (rc_cast'' pf d.(Core.c)) m20].
Proof.
case: s1=> // c s1'; case: s2=> // d s2' /=.
move=> [][]pf => [][]cd []ef1 []sig1 []vals1 []ef2 []sig2 []vals2 []A B C.
exists c, s1', d, s2'; split=> //.
by exists pf, cd; case: A.
Qed.

Lemma frame_all_fwd1 mu_trash pkg mus z m1 m2 s1 s2 :
  frame_all mu_trash (pkg :: mus) z m1 m2 s1 s2 -> 
  mem_forward pkg.(frame_m10) m1.
Proof.
case: pkg=> ? ? ? ?.
move/frame_all_inv=> []? []? []? []? []? ? []? []? []? []? []? []? []? []? [].
by case.
Qed.

Lemma frame_all_fwd2 mu_trash pkg mus z m1 m2 s1 s2 :
  frame_all mu_trash (pkg :: mus) z m1 m2 s1 s2 -> 
  mem_forward pkg.(frame_m20) m2.
Proof.
case: pkg=> ? ? ? ?.
move/frame_all_inv=> []? []? []? []? []? ? []? []? []? []? []? []? []? []? [].
by case.
Qed.

Lemma frame_all_tail mu_trash pkg mus z m1 m2 s1 s2 :
  frame_all mu_trash (pkg :: mus) z m1 m2 s1 s2 -> 
  frame_all mu_trash mus z m1 m2 (STACK.pop s1) (STACK.pop s2).
Proof.
case: pkg=> ? ? ? ?.
move/frame_all_inv=> []? []? []? []? []-> ->. 
by move=> []? []? []? []? []? []? []? []? [] _.
Qed.

Section frame_all_lems.

Context mu_trash mus z m1 m2 s1 s2 
        (frameall : frame_all mu_trash mus z m1 m2 s1 s2).

Lemma frame_all_globs :
  All (fun mu0 => forall b, isGlobalBlock my_ge b -> frgnBlocksSrc mu0 b)  
    $ map (Inj.mu \o frame_mu0) mus.
Proof.
move: frameall.
move: m1 m2 s1 s2; elim: mus=> //; case=> mu' ? ? ? mus' IH m1' m2' s1' s2' A.
move: (frame_all_inv A)=> []c []s1'' []d []s2'' []_ _.
move=> []pf []cd []? []? []? []? []? []? []B X C.
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
move=> []pf []cd []? []? []? []? []? []? []B X C.
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
move=> []pf []cd []? []? []? []? []? []? []B X C.
case: B=> ? ? ? ? val; move/match_genv=> []_ D; split=> /=.
by apply: (sm_valid_fwd val).
by apply: (IH _ _ _ _ C).
Qed.

End frame_all_lems.

Lemma tail_inv_inv mu_trash mu0 m10 m20 (z : tZ) x mus s1 s2 m1 m2 :
  tail_inv mu_trash (@Build_frame_pkg mu0 m10 m20 x :: mus) 
           z s1 s2 m1 m2 -> 
  exists c s1' d s2',
    [/\ s1 = c :: s1'
      , s2 = d :: s2' 
      , (exists (pf : c.(Core.i)=d.(Core.i)) cd0,
         exists e1 ef_sig1 vals1,
         exists e2 ef_sig2 vals2, 
           @frame_inv c d pf cd0 mu0 z
           m10 m1 e1 ef_sig1 vals1 m20 m2 e2 ef_sig2 vals2)
       & tail_inv mu_trash mus z (STACK.pop s1) (STACK.pop s2) m1 m2].
Proof.
case; case=> H1 H2; move/frame_all_inv=> []c []s1' []d []s2' []B C.
move=> []pf []cd []ef1 []sig1 []vals1 []ef2 []sig2 []vals2 []D E.
exists c,s1',d,s2'; split=> //.
by exists pf,cd,ef1,sig1,vals1,ef2,sig2,vals2.
by split=> //; rewrite B C.
Qed.

Lemma tail_inv_match mu_trash mu0 m10 m20 z x mus s1 s2 m1 m2 :
  tail_inv mu_trash (@Build_frame_pkg mu0 m10 m20 x :: mus) 
           z s1 s2 m1 m2 -> 
  exists c s1' d s2',
    [/\ s1 = c :: s1'
      , s2 = d :: s2' 
      & exists (pf : c.(Core.i)=d.(Core.i)) cd0,
        (sims c.(Core.i)).(match_state) cd0 mu0 
        c.(Core.c) m10 (rc_cast'' pf d.(Core.c)) m20].
Proof. by move=> []_; move/frame_all_match. Qed.

Section tail_inv_lems.

Context mu_trash mus z s1 s2 m1 m2 
        (tlinv : tail_inv mu_trash mus z s1 s2 m1 m2).

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
Proof. by case: tlinv=> _; move/frame_all_valid; rewrite -!All_comp. Qed.

Lemma tail_valid_src :
  All (fun mu0 => smvalid_src mu0 m1)
    [seq Inj.mu x | x <- [seq frame_mu0 x | x <- mus]].
Proof. 
case: tlinv=> _; move/frame_all_valid; rewrite -!All_comp=> H. 
by apply: (All_sub H)=> pkg /=; apply: sm_valid_smvalid_src.
Qed.

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

Lemma all_relinv_step mu_trash mus z s1 s2 :
  frame_all mu_trash mus z m1 m2 s1 s2 -> 
  All (rel_inv_pred mu) mus -> 
  All (rel_inv_pred mu') mus.
Proof.
elim: mus s1 s2=> // pkg mus' IH s1 s2 A /= => [][] B C.
move: (rel_inv_pred_step (frame_all_fwd1 A) (frame_all_fwd2 A) B)=> D.
by split=> //; last by apply: (IH _ _ (frame_all_tail A) C).
Qed.

Lemma frame_all_step mu_trash mus z s1 s2 :
  All (rel_inv_pred mu) mus -> 
  frame_all mu_trash mus z m1 m2 s1 s2 -> 
  frame_all mu_trash mus z m1' m2' s1 s2.
Proof.
elim: mus s1 s2=> // pkg mus' IH s1' s2' E.
simpl in E; case: E=> E F.
case: pkg E=> mu0 m10 m20 val' E.

move/frame_all_inv.
move=> []c []s1'' []d []s2'' []-> ->.
move=> []pf []cd []e1 []sig1 []vals1 []e2 []sig2 []vals2.
move=> []inv contain all /=.

split.
exists pf,cd,e1,sig1,vals1,e2,sig2,vals2.

split.
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

by apply: contain.

by eapply IH; eauto.
Qed.

Lemma tail_inv_step mu_trash mus z s1 s2 :
  All (rel_inv_pred mu) mus -> 
  tail_inv mu_trash mus z s1 s2 m1 m2 -> 
  tail_inv mu_trash mus z s1 s2 m1' m2'.
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
    cd cd' mu_trash mus z s1 s2 U :
  head_inv pf cd mu_trash mu mus z m1 m2 -> 
  frame_all mu_trash mus z m1 m2 s1 s2 -> 
  RC.args (Core.c c)=RC.args c' -> 
  RC.rets (Core.c c)=RC.rets c' -> 
  RC.locs c' = (fun b => RC.locs (Core.c c) b || freshloc m1 m1' b) ->
  effect_semantics.effstep 
    (coreSem (cores_S (Core.i c))) (ge (cores_S (Core.i c))) U 
    (RC.core (Core.c c)) m1 (RC.core c') m1' -> 
  match_state (sims (Core.i (Core.upd c c'))) cd' mu'
    (Core.c (Core.upd c c')) m1'
    (rc_cast'' pf (Core.c (Core.upd d d'))) m2' -> 
  (forall b : block,
   RC.locs (Core.c c) b = false ->
   RC.locs c' b -> locBlocksSrc mu' b) -> 
  @head_inv (Core.upd c c') (Core.upd d d') pf cd' mu_trash mu' mus z m1' m2'.
Proof.
move=> hdinv frame args rets mylocs effstep mtch locs.
apply: Build_head_inv=> //.
by apply: (all_relinv_step frame); apply: (head_rel hdinv).
by case: hdinv=> ? ? A _ _; apply: (vis_inv_step A)=> //.
case: hdinv=> ? ? _ A _; move: (effax1 effstep)=> []step _. 
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
case: hdinv=> ? ? _ _ A; rewrite/frgn_contained -(intern_incr_frgnsrc incr).
by apply: A.
Qed.

Lemma trash_inv_step mu_trash mupkg mupkg' (mus : seq frame_pkg) : 
  frame_mu0 mupkg=mu -> 
  frame_mu0 mupkg'=mu' -> 
  trash_inv mu_trash mupkg mus m1 m2 -> 
  trash_inv mu_trash mupkg' mus m1' m2'.
Proof.
move=> A B; case=> C D E /= []F G []H I []K L; apply: Build_trash_inv=> //=.
by apply: (sm_valid_fwd E fwd1 fwd2).
split=> //.
rewrite B; eapply DisjointLS_intern_step; eauto.
by move: F; rewrite A.
split=> //.
eapply DisjointLT_intern_step; eauto; first by move: H; rewrite A.
by move: incr; rewrite B.
by move: sep; rewrite B.
split=> //. 
by case: incr; move: K; rewrite A B=> K _ []<-.
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
      , @head_inv c d pf (Lex.get c.(Core.i) data) mu_trash mu_top mus z m1 m2 
      & tail_inv mu_trash mus z (pop s1) (pop s2) m1 m2] }.

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
  (Core.c (peekCore x1)) m1 
  (rc_cast'' peek_ieq (Core.c (peekCore x2))) m2.
Proof.
move: (R_inv pf)=> []A []? []mu_top []? []? []? _ _. 
move/head_match=> MATCH ?.
have ->: (rc_cast'' peek_ieq (Core.c (peekCore x2)) 
         = rc_cast'' A (Core.c (peekCore x2)))
  by f_equal; f_equal; apply proof_irr.
by exists (Lex.get (Core.i (peekCore x1)) data), mu_top.
Qed.

Lemma R_AllDisjointS 
    (mu_trash mu_top : frame_pkg) (mus : seq frame_pkg) 
    c d (eq : Core.i c=Core.i d) cd z s1 s2 :
  trash_inv mu_trash mu_top mus m1 m2 -> 
  head_inv eq cd mu_trash mu_top mus z m1 m2 -> 
  tail_inv mu_trash mus z s1 s2 m1 m2 -> 
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
  head_inv eq cd mu_trash mu_top mus z m1 m2 -> 
  tail_inv mu_trash mus z s1 s2 m1 m2 -> 
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
  head_inv eq cd mu_trash mu_top mus z m1 m2 -> 
  tail_inv mu_trash mus z s1 s2 m1 m2 -> 
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

- by admit. (* NOT NEEDED diagram1 *)

(* real diagram *)
- move=> st1 m1 st1' m1' U1 STEP data st2 mu m2 U1_DEF INV.
case: STEP=> STEP STEP_EFFSTEP.
case: STEP.

(* Case: corestep0 *)
 + move=> STEP. 

 set c1 := peekCore st1.
 set c2 := peekCore st2.

 have [c1' [STEP0 [U1'_EQ [c1_args [c1_rets [c1_locs ST1']]]]]]:
   exists c1',
       Coresem.corestep 
         (t := RC.effsem (coreSem (cores_S (Core.i c1)))) 
         (ge (cores_S (Core.i c1))) (Core.c c1) m1 c1' m1' 
   /\ (forall b ofs, U1 b ofs -> 
       RC.reach_set (ge (cores_S (Core.i c1))) (Core.c c1) m1 b)
   /\ RC.args (Core.c (c INV)) = RC.args c1'
   /\ RC.rets (Core.c (c INV)) = RC.rets c1'
   /\ RC.locs c1' 
      = (fun b => RC.locs (Core.c (c INV)) b || freshloc m1 m1' b)
   /\ st1' = updCore st1 (Core.upd c1 c1').

  { move: (STEP_EFFSTEP STEP)=> EFFSTEP.
    move: STEP; rewrite/LinkerSem.corestep0=> [][]c1' []B C. 
    move: EFFSTEP; rewrite/effstep0.
    move=> []? []/=; rewrite/RC.effstep=> [][]EFFSTEP []u1 []args []rets locs D.
    exists c1'. split=> //. split=> //.
    by move: C D=> ->; move/updCore_inj_upd=> ->; split. }

 have EFFSTEP: 
    effect_semantics.effstep 
    (RC.effsem (coreSem (cores_S (Core.i c1))))
    (ge (cores_S (Core.i c1))) U1 (Core.c c1) m1 c1' m1'.

  { move: (STEP_EFFSTEP STEP); rewrite/effstep0=> [][] c1'' [] STEP0' ST1''. 
    by rewrite ST1'' in ST1'; rewrite -(updCore_inj_upd ST1'). }

 (* specialize core diagram at module (Core.i c1) *)
 move: (effcore_diagram _ _ _ _ _ (sims (Core.i c1))).  
 move/(_ _ _ _ _ _ EFFSTEP).
 case: (R_inv INV)=> pf []mu_trash []mupkg []mus []z []mu_eq.
 move=> rclosed trinv hdinv tlinv.

 have U1_DEF': forall b ofs, U1 b ofs -> vis mupkg b. 

   { case: hdinv=> mtch ?; case=> visinv _ _ b ofs A; move: (U1'_EQ _ _ A).
     rewrite/RC.reach_set=> B; apply match_visible in mtch; apply: mtch.
     move: B; apply REACH_mono with (B1 := RC.reach_basis _ _)=> b'=> B.
     apply: (visinv b'); move: B; apply: RC.reach_basis_domains_eq.
     by apply: genvs_domain_eq_sym; apply: (my_ge_S (Core.i c1)). }

 move: (head_match hdinv)=> MATCH.
 move/(_ _ _ _ _ U1_DEF' MATCH).
 move=> []c2' []m2' []cd' []mu_top0.
 move=> []INCR []SEP []LOCALLOC []MATCH' []U2 []STEP' PERM.

 have mu_top'_wd: SM_wd mu_top0 by move: MATCH'; apply: match_sm_wd.
 set mu_top' := Inj.mk mu_top'_wd.
 have mu_top'_valid: sm_valid mu_top' m1' m2'
   by apply: (match_validblocks _ MATCH').
 set mupkg' := Build_frame_pkg mu_top'_valid.

 (* instantiate existentials *)
 set c2''   := rc_cast' (peek_ieq INV) c2'.
 set st2'   := updCore st2 (Core.upd c2 c2'').
 set data'  := Lex.set (Core.i c1) cd' data.
 set mu'    := restrict_sm 
               (join_all mu_trash $ mu_top' :: map frame_mu0 mus)
               (vis (join_all mu_trash $ mu_top' :: map frame_mu0 mus)).

 exists st2', m2', data', mu'. 

 split. 

 (*incr*)
 rewrite mu_eq; apply join_all_restrict_incr with (m1 := m1) (m2 := m2)=> //.
 move: (head_AllDisjointLS hdinv); rewrite All_comp2=> A.
 move: (tail_valid tlinv); rewrite -map_comp=> B.
 move: (AllDisjointLS_incr A INCR SEP LOCALLOC B).
 rewrite -All_comp3=> C; rewrite -All_comp; apply (All_sub C). 
 by move=> pkg D; apply: DisjointLS_disjoint.
 by move: (trash_disj_S trinv)=> /= []; rewrite map_comp.
 by move: (trash_disj_T trinv)=> /= []; rewrite map_comp.
 by move: (trash_consist trinv)=> /= []; rewrite map_comp.
 apply: DisjointLS_disjoint.
 have A: DisjointLS mupkg mu_trash. 
   by move: (trash_disj_S trinv)=> /= []; rewrite DisjointC.
 by apply: (DisjointLS_incr A INCR SEP LOCALLOC (trash_valid trinv)).
 by move: (tail_AllDisjointLS tlinv); rewrite All2_comp2 map_comp.
 by move: (tail_AllDisjointLT tlinv); rewrite All2_comp2 map_comp.
 by move: (tail_AllConsistent tlinv); rewrite All2_comp2 map_comp. 
 by move: (tail_valid tlinv); rewrite -All_comp3.
 by apply: (trash_valid trinv).

 split. 

 (*sep*)
 rewrite mu_eq. apply join_all_restrict_sep 
   with (m1 := m1) (m2 := m2) (m1' := m1') (m2' := m2')=> //.
 by move: (head_AllConsistent hdinv); rewrite All_comp2 {1}map_comp.
 by move: (tail_valid tlinv); rewrite -All_comp3.
 by move: (trash_consist trinv)=> /= []; rewrite map_comp; move/consistentC.
 by apply: (trash_valid trinv).
 by apply: (match_validblocks _ MATCH).
 apply: join_all_valid=> /=; first by apply: (trash_valid trinv).
 split; first by apply: (head_valid hdinv).
 by move: (tail_valid tlinv); rewrite -All_comp3.
 change (SM_wd (join_all mu_trash [seq (frame_mu0 i) | i <- mus])).
 apply: join_all_wd.
 split; first by move: (trash_disj_S trinv); rewrite -map_comp; case.
 by move: (tail_AllDisjointLS tlinv); rewrite -map_comp.
 split; first by move: (trash_disj_T trinv); rewrite -map_comp; case.
 by move: (tail_AllDisjointLT tlinv); rewrite -map_comp.
 split; first by move: (trash_consist trinv); rewrite -map_comp; case.
 by move: (tail_AllConsistent tlinv); rewrite -map_comp.
 change (SM_wd (join_all mu_trash [seq (frame_mu0 i) | i <- mupkg :: mus])).
 apply: join_all_wd.
 by move: (R_AllDisjointS trinv hdinv tlinv); rewrite All2_comp2 map_comp.
 by move: (R_AllDisjointT trinv hdinv tlinv); rewrite All2_comp2 map_comp.
 by move: (R_AllConsistent trinv hdinv tlinv); rewrite All2_comp2 map_comp.

 (*loc_alloc*)
 split; first by rewrite mu_eq; apply: join_all_locally_allocated.

 split.

 (* re-establish invariant *)
 apply: Build_R; rewrite ST1'; rewrite /st2'.

 exists pf, mu_trash, mupkg', mus, z; split=> //.

 (*rc m1' (vis mu')*)
 apply: (join_all_REACH_closed (mu := mupkg) (m1 := m1))=> //.
 by move: (trash_disj_S trinv)=> /= []; rewrite DisjointC.
 by move: (head_AllDisjointLS hdinv); rewrite -map_comp.
 apply mem_unchanged_on_sub with (Q := fun b ofs => U1 b ofs=false).
 by apply effstep_unchanged in EFFSTEP; apply: EFFSTEP.
 move=> b ofs X; move: (U1_DEF' b ofs); rewrite X=> Y.
 by case W: (U1 b ofs)=> //; rewrite W in Y; rewrite Y.  
 by case: hdinv=> _ _ _ _; apply.
 by move: (trash_valid trinv); apply/sm_valid_smvalid_src.
 by move: (tail_valid_src tlinv); rewrite -All_comp3. 
 by move: rclosed; rewrite mu_eq vis_restrict_sm.
 by eapply match_visible; eauto.

 (*trash_inv*)
 apply trash_inv_step 
   with (m1 := m1) (m2 := m2)
        (mu := mupkg) (mu' := mu_top') (mupkg := mupkg)=> //.
  by apply: (effstep_fwd _ _ _ _ _ _ _ EFFSTEP).
  case: STEP'=> [STEP'|[STEP' _]]. 
  by apply: (effstep_plus_fwd _ _ _ _ _ _ _ STEP').
  by apply: (effstep_star_fwd _ _ _ _ _ _ _ STEP').
  by apply: (head_valid hdinv).

 (* head_inv *)
 + case: tlinv=> allrel frameall.
   apply: (@head_inv_step 
     mupkg m1 m2 mu_top' m1' m2' (head_valid hdinv) INCR SEP
     (c INV) (d INV) pf c1' c2'' (Lex.get (Core.i (c INV)) data) _ _ mus z
     (STACK.pop (CallStack.callStack (s1 INV))) 
     (STACK.pop (CallStack.callStack (s2 INV))) U1 hdinv frameall)=> //=.
   by case: EFFSTEP.
   have ->: rc_cast'' pf c2'' = c2' by apply: cast_cast_eq'.
   by rewrite Lex.gss.
   rewrite c1_locs=> b -> /=; move: (LOCALLOC). 
   rewrite sm_locally_allocatedChar; case=> _ []_ []-> _ A.
   by apply/orP; right.

 (* tail_inv *)
 + eapply tail_inv_step with (Etgt := U2); eauto.
   by apply: (effstep_unchanged _ _ _ _ _ _ _ EFFSTEP).
   case: STEP'.
   - by case=> n; apply: effect_semantics.effstepN_unchanged.
   - case; case=> n=> EFFSTEPN _. 
     by apply: (effect_semantics.effstepN_unchanged EFFSTEPN).
   by move: (effax1 EFFSTEP)=> []; move/corestep_fwd.
   case: STEP'.
   - by case=> n; apply: effect_semantics.effstepN_fwd.
   - case; case=> n=> EFFSTEPN _.
     by apply: (effect_semantics.effstepN_fwd EFFSTEPN).   
   move=> ? ? X; move: (PERM _ _ X)=> []Y Z; split=> //.
   have [n STEPN]: 
     exists n, effstepN (RC.effsem (coreSem (cores_T (Core.i c1))))
               (ge (cores_T (Core.i c1))) n U2 
               (rc_cast'' pf (Core.c (d INV))) m2 c2' m2'.
     case: STEP'; first by move=> []n ?; exists (S n). 
     by move=> [][]n ? _; exists n.
   by eapply effstepN_valid in STEPN; eauto.
   by apply: (head_rel hdinv).

 (* matching execution *)
 + exists U2; split=> //; case: STEP'=> STEP'.

   have STEP'': 
     effstep_plus (RC.effsem (coreSem (cores_T (Core.i c2))))
     (ge (cores_T (Core.i c2))) U2 (Core.c (d INV)) m2 c2'' m2'. 

   { set T := RC.state \o C \o cores_T.
     set P := fun ix (x : T ix) (y : T ix) => 
               effstep_plus (RC.effsem (coreSem (cores_T ix)))
               (ge (cores_T ix)) U2 x m2 y m2'.
     change (P (Core.i c2) (Core.c c2) c2''); apply: cast_indnatdep2.
     by move: STEP'; have ->: pf = peek_ieq INV by apply: proof_irr. }

   by left; move: STEP''; apply: stepPLUS_STEPPLUS.

   have STEP'': 
     effstep_star (RC.effsem (coreSem (cores_T (Core.i c2))))
     (ge (cores_T (Core.i c2))) U2 (Core.c c2) m2 c2'' m2'. 

   { set T := RC.state \o C \o cores_T.
     set P := fun ix (x : T ix) (y : T ix) => 
               effstep_star (RC.effsem (coreSem (cores_T ix)))
               (ge (cores_T ix)) U2 x m2 y m2'.
     change (P (Core.i c2) (Core.c c2) c2''); apply: cast_indnatdep2.
     by case: STEP'; have ->: pf = peek_ieq INV by apply: proof_irr; by []. }

   right; split; first by move: STEP''; apply: stepSTAR_STEPSTAR.
   apply: Lex.ord_upd; admit. (*FIXME: tail_inv cannot existentially quant. cd's*)

 

Admitted. (*WORK-IN-PROGRESS*)

End linkingSimulation.


