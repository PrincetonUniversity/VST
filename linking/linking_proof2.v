(* standard Coq libraries *)

Require Import JMeq.

(* msl imports *)

Require Import msl.Axioms. (*for proof_irr*)

(* sepcomp imports *)

Require Import linking.sepcomp. Import SepComp. 
Require Import sepcomp.arguments.

Require Import linking.pos.
Require Import linking.stack.
Require Import linking.cast.
Require Import linking.pred_lemmas.
Require Import linking.seq_lemmas.
Require Import linking.wf_lemmas.
Require Import linking.reestablish.
Require Import linking.core_semantics_lemmas.
Require Import linking.inj_lemmas.
Require Import linking.join_sm.
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

Require Import ssreflect ssrbool ssrfun seq eqtype fintype.
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
(*   Source_0 >< Source_1 >< ... >< Source_{N-1}                          *)
(*                                                                        *)
(* and target semantics                                                   *)
(*                                                                        *)
(*   Target_0 >< Target_1 >< ... >< Target_{N-1}                          *)
(*                                                                        *)
(* where >< denotes the semantic linking operation defined in             *)
(* compcert_linking.v.                                                    *)

Section linkingSimulation.

Import Wholeprog_simulation.
Import SM_simulation.
Import Linker.
Import Modsem.

Variable N : pos.
Variable (cores_S' cores_T : 'I_N -> Modsem.t). 

Let cores_S (ix : 'I_N) := 
  Modsem.mk (cores_S' ix).(ge) (RC.effsem (cores_S' ix).(coreSem)).

Variable fun_tbl : ident -> option 'I_N.
Variable sims : forall i : 'I_N, 
  let s := cores_S i in
  let t := cores_T i in
  SM_simulation_inject s.(coreSem) t.(coreSem) s.(ge) t.(ge).
Variable my_ge : ge_ty.
Variable my_ge_S : forall (i : 'I_N), genvs_domain_eq my_ge (cores_S i).(ge).
Variable my_ge_T : forall (i : 'I_N), genvs_domain_eq my_ge (cores_T i).(ge).

Let types := fun i : 'I_N => (sims i).(core_data).
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
(* core.                                                                  *)
(*                                                                        *)
(* We record this fact (really, a slight modification of the invariant    *)
(* that accounts for return values as well) as an invariant of execution  *)
(* for both the head and tail cores. Then the guarantees we get from RC   *)
(* executions (that write effects are limited to blocks in the RC of      *)
(* initial args, rets, local blocks) imply that effects are also a        *)
(* subset of the visible region for each core.                            *)

Section glob_lems.

Lemma invSym_findSymS ix id b :
  Genv.invert_symbol my_ge b = Some id -> 
  exists id', Genv.find_symbol (ge (cores_S ix)) id' = Some b.
Proof.
case: (my_ge_S ix)=> H1 H2.
rewrite /genv2blocks /= in H1.
case: {H1}(H1 b)=> H1 H3.
move/Genv.invert_find_symbol=> H4.
case: H1; first by exists id.
by move=> x H5; exists x.
Qed.

Lemma invSym_findSymT ix id b :
  Genv.invert_symbol my_ge b = Some id -> 
  exists id', Genv.find_symbol (ge (cores_T ix)) id' = Some b.
Proof.
case: (my_ge_T ix)=> H1 H2.
rewrite /genv2blocks /= in H1.
case: {H1}(H1 b)=> H1 H3.
move/Genv.invert_find_symbol=> H4.
case: H1; first by exists id.
by move=> x H5; exists x.
Qed.

Lemma invSym_findSymS_None ix b :
  Genv.invert_symbol my_ge b = None -> 
  forall id, Genv.find_symbol (ge (cores_S ix)) id = Some b -> False.
Proof.
case: (my_ge_S ix)=> H1 H2.
rewrite /genv2blocks /= in H1.
move=> H3 id H4.
case: (H1 b)=> H5 H6.
case: H6; first by exists id.
by move=> x; move/Genv.find_invert_symbol; rewrite H3.
Qed.

Lemma invSym_findSymT_None ix b :
  Genv.invert_symbol my_ge b = None -> 
  forall id, Genv.find_symbol (ge (cores_T ix)) id = Some b -> False.
Proof.
case: (my_ge_T ix)=> H1 H2.
rewrite /genv2blocks /= in H1.
move=> H3 id H4.
case: (H1 b)=> H5 H6.
case: H6; first by exists id.
by move=> x; move/Genv.find_invert_symbol; rewrite H3.
Qed.

Lemma findVar_findSymS ix inf b :
  Genv.find_var_info my_ge b = Some inf -> 
  exists inf', Genv.find_var_info (ge (cores_S ix)) b = Some inf'.
Proof.
case: (my_ge_S ix)=> H1 H2.
rewrite /genv2blocks /= in H2.
case: {H2}(H2 b)=> H2 H3 H4.
case: H2; first by exists inf.
by move=> x H5; exists x.
Qed.

Lemma findVar_findSymT ix inf b :
  Genv.find_var_info my_ge b = Some inf -> 
  exists inf', Genv.find_var_info (ge (cores_T ix)) b = Some inf'.
Proof.
case: (my_ge_T ix)=> H1 H2.
rewrite /genv2blocks /= in H2.
case: {H2}(H2 b)=> H2 H3 H4.
case: H2; first by exists inf.
by move=> x H5; exists x.
Qed.

Lemma findVar_findSymS_None ix b :
  Genv.find_var_info my_ge b = None -> 
  Genv.find_var_info (ge (cores_S ix)) b = None.
Proof.
case: (my_ge_S ix)=> H1 H2.
rewrite /genv2blocks /= in H2.
case: {H2}(H2 b)=> H2 H3 H4.
case g: (Genv.find_var_info _ _)=> //[gv].
case: H3; first by exists gv.
by move=> x; rewrite H4.
Qed.

Lemma findVar_findSymT_None ix b :
  Genv.find_var_info my_ge b = None -> 
  Genv.find_var_info (ge (cores_T ix)) b = None.
Proof.
case: (my_ge_T ix)=> H1 H2.
rewrite /genv2blocks /= in H2.
case: {H2}(H2 b)=> H2 H3 H4.
case g: (Genv.find_var_info _ _)=> //[gv].
case: H3; first by exists gv.
by move=> x; rewrite H4.
Qed.

Lemma isGlob_iffS ix b : 
  isGlobalBlock my_ge b <-> isGlobalBlock (ge (cores_S ix)) b.
Proof.
rewrite /isGlobalBlock /genv2blocksBool /=.
case i: (Genv.invert_symbol _ _)=> [id|].
case: (invSym_findSymS ix i)=> x fnd.
rewrite (Genv.find_invert_symbol _ _ fnd).
by split.
case j: (Genv.find_var_info my_ge b)=> [inf|].
case: (findVar_findSymS ix j)=> x=> ->; split=> //=.
by move=> _; apply/orP; right.
move: (@invSym_findSymS_None ix _ i)=> H1.
case k: (Genv.invert_symbol _ _)=> [id|].
move: (Genv.invert_find_symbol _ _ k)=> H2. 
by elimtype False; apply: (H1 _ H2).
case l: (Genv.find_var_info _ _)=> [inf|].
by rewrite (findVar_findSymS_None _ j) in l.
by [].
Qed.

Lemma isGlob_iffT ix b : 
  isGlobalBlock my_ge b <-> isGlobalBlock (ge (cores_T ix)) b.
Proof.
rewrite /isGlobalBlock /genv2blocksBool /=.
case i: (Genv.invert_symbol _ _)=> [id|].
case: (invSym_findSymT ix i)=> x fnd.
rewrite (Genv.find_invert_symbol _ _ fnd).
by split.
case j: (Genv.find_var_info my_ge b)=> [inf|].
case: (findVar_findSymT ix j)=> x=> ->; split=> //=.
by move=> _; apply/orP; right.
move: (@invSym_findSymT_None ix _ i)=> H1.
case k: (Genv.invert_symbol _ _)=> [id|].
move: (Genv.invert_find_symbol _ _ k)=> H2. 
by elimtype False; apply: (H1 _ H2).
case l: (Genv.find_var_info _ _)=> [inf|].
by rewrite (findVar_findSymT_None _ j) in l.
by [].
Qed.

Lemma isGlob_iffS' ix1 ix2 b :
  isGlobalBlock (ge (cores_S ix1)) b <-> isGlobalBlock (ge (cores_S ix2)) b. 
Proof. by split; rewrite -!isGlob_iffS. Qed.

Lemma isGlob_iffT' ix1 ix2 b :
  isGlobalBlock (ge (cores_T ix1)) b <-> isGlobalBlock (ge (cores_T ix2)) b. 
Proof. by split; rewrite -!isGlob_iffT. Qed.

Lemma isGlob_iffST' ix1 ix2 b :
  isGlobalBlock (ge (cores_S ix1)) b <-> isGlobalBlock (ge (cores_T ix2)) b. 
Proof. by split; rewrite -isGlob_iffS -isGlob_iffT. Qed.

End glob_lems.

Section vis_inv.

Import Core.

Record vis_inv (c : t cores_S) mu : Type :=
  { vis_sup : {subset (RC.reach_basis my_ge c.(Core.c)) <= vis mu} }.

End vis_inv.

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
                   c.(Core.c) m10 (cast'' pf d.(Core.c)) m20 
  ; frame_at1   : at_external (cores_S c.(i)).(coreSem) c.(Core.c)
                    = Some (e1, ef_sig1, vals1) 
  ; frame_at2   : at_external (cores_T c.(i)).(coreSem) (cast'' pf d.(Core.c)) 
                    = Some (e2, ef_sig2, vals2) 
  ; frame_vinj  : Forall2 (val_inject (restrict (as_inj mu0) (vis mu0))) vals1 vals2  

    (* source state invariants *)
  ; frame_vis   : vis_inv c mu0

    (* invariants relating m10,m20 to active memories m1,m2*)
  ; frame_fwd1  : mem_forward m10 m1
  ; frame_fwd2  : mem_forward m20 m2
  ; frame_unch1 : Mem.unchanged_on [fun b ofs => 
                    [/\ locBlocksSrc nu0 b & pubBlocksSrc nu0 b=false]] m10 m1
  ; frame_unch2 : Mem.unchanged_on (local_out_of_reach nu0 m10) m20 m2 }.

End frame_inv.

Record rel_inv mu0 mu m10 m20 m1 : Prop :=
  { (* invariants relating mu0,mu *)    
    frame_incr       : incr mu0 mu
  ; frame_sep        : sm_inject_separated mu0 mu m10 m20
  ; frame_disj       : disjinv mu0 mu 
  ; frame_rc         : {subset [predI REACH m1 (vis mu) & locBlocksSrc mu0]
                       <= pubBlocksSrc mu0}
  }.

Record frame_pkg : Type := 
  { frame_mu0 :> Inj.t
  ; frame_m10 : Memory.mem
  ; frame_m20 : Memory.mem
  ; frame_val : sm_valid frame_mu0 frame_m10 frame_m20 }.

Definition rel_inv_pred m1 mu pkg := 
  let mu0 := frame_mu0 pkg in
  let m10 := frame_m10 pkg in
  let m20 := frame_m20 pkg in
  rel_inv mu0 mu m10 m20 m1.

Section rel_inv_pred_lems.

Context mu pkg m1 (rinv : rel_inv_pred m1 mu pkg).

Lemma relinv_DisjointLS : DisjointLS mu (frame_mu0 pkg).
Proof. by case: rinv=> _ _; case; move/DisjointC. Qed.

Lemma relinv_DisjointLT : DisjointLT mu (frame_mu0 pkg).
Proof. by case: rinv=> _ _; case=> _; move/DisjointC. Qed.

Lemma relinv_consistent : Consistent mu (frame_mu0 pkg).
Proof. by case: rinv=> _ _; case=> _ _ _ _; move/consistentC. Qed.

End rel_inv_pred_lems.

Section rel_inv_pred_all_lems.

Context m1 mu mus (all_rinv : All (rel_inv_pred m1 mu) mus).

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
  All (fun mu2 => Consistent mu mu2) $ map (Inj.mu \o frame_mu0) mus.
Proof.
move: all_rinv; elim: mus=> // mu0 mus' IH /= => [][]A B; split.
by apply: (relinv_consistent A).
by apply: IH.
Qed.

End rel_inv_pred_all_lems.

Section rel_inv_pred_all2_lems.

Context m1 mus 
  (all_rinv : All2 (fun mu1 mu2 => 
   rel_inv_pred m1 (Inj.mu \o frame_mu0 $ mu1) mu2) mus).

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

Lemma All_listsub (T : Type) (P : T -> Prop) (l l' : seq.seq T) :
  (forall a, In a l' -> In a l) -> 
  All P l -> 
  All P l'.
Proof.
move=> IN A; elim: l' IN=> // a l' /= IH IN; split.
move: (IN _ (or_introl erefl))=> IN'.
clear - A IN'; elim: l A IN'=> // a0 l' IH /= []H I; case; first by move=> <-.
by apply: IH.
by apply: IH=> a0 IN0; apply: IN; right.
Qed.

Section head_inv.

Import Core.

Variables (c : t cores_S) (d : t cores_T). 
Variable  (pf : c.(i)=d.(i)).

Record head_inv cd (mu : Inj.t) mus m1 m2 : Type :=
  { head_match : (sims c.(i)).(match_state) cd mu 
                 c.(Core.c) m1 (cast'' pf d.(Core.c)) m2 
  ; head_rel   : All (rel_inv_pred m1 mu) mus 
  ; head_vis   : vis_inv c mu }.

End head_inv.

Lemma getBlocks_restrict j X args1 args2 b : 
  Forall2 (val_inject (restrict j X)) args1 args2 -> 
  getBlocks args1 b -> X b.
Proof.
move=> vinj H1; case: (getBlocks_inject _ _ _ vinj b H1)=> b' []d' []res get2.
by case: (restrictD_Some _ _ _ _ _ res)=> asInj.
Qed.

Section contain_lems.

Variable mu : Inj.t.

Variables args1 args2 : list val.

Let j := as_inj mu.

Variable vinj : Forall2 (val_inject (restrict j (sharedSrc mu))) args1 args2.

Variable defs : vals_def args1.

Lemma getBlocks_frgnpubS b :
  getBlocks args1 b -> 
  [\/ pubBlocksSrc mu b | frgnBlocksSrc mu b].
Proof.
move=> H1; case: (getBlocks_inject _ _ _ vinj b H1)=> b' []d' []res get2.
case: (restrictD_Some _ _ _ _ _ res)=> asInj.
rewrite sharedSrc_iff_frgnpub; last by apply: Inj_wd.
case/orP=> //.
by move=> ->; right.
by move=> ->; left. 
Qed.

Lemma getBlocks_frgnpubT b :
  getBlocks args2 b -> 
  [\/ pubBlocksTgt mu b | frgnBlocksTgt mu b].
Proof.
move=> H1.
have [b0 [d [H2 H3]]]: 
  exists b0 d, 
  [/\ getBlocks args1 b0 
    & j b0 = Some (b,d)]. 
{ move: (forall_inject_val_list_inject _ _ _ vinj)=> vinj'.
  case: (vals_def_getBlocksTS vinj' defs H1)=> x []y []? res.
  exists x,y; split=> //; last by case: (restrictD_Some _ _ _ _ _ res). }
case: (getBlocks_frgnpubS H2).
case/pubSrcAx; first by apply: Inj_wd.
move=> b' []d' []lOf pT.
move: (local_in_all _ (Inj_wd _) _ _ _ lOf).
by rewrite /j in H3; rewrite H3; case=> -> _; left.
move=> H4; case: (frgnSrc _ (Inj_wd _) _ H4)=> []? []? []fOf H5.
move: (foreign_in_all _ _ _ _ fOf).
by rewrite /j in H3; rewrite H3; case=> -> _; right.
Qed.

Lemma getBlocks_locpubS b : 
  locBlocksSrc mu b -> 
  getBlocks args1 b -> 
  pubBlocksSrc mu b.
Proof.
move=> H1 H2; case: (getBlocks_frgnpubS H2)=> //.
by rewrite (locBlocksSrc_frgnBlocksSrc _ _ _ H1); last by apply: Inj_wd. 
Qed.

Lemma getBlocks_locpubT b : 
  locBlocksTgt mu b -> 
  getBlocks args2 b -> 
  pubBlocksTgt mu b.
Proof.
move=> H1 H2; case: (getBlocks_frgnpubT H2)=> //.
by rewrite (locBlocksTgt_frgnBlocksTgt _ _ _ H1); last by apply: Inj_wd. 
Qed.

End contain_lems.

Section head_inv_lems.

Context c d pf cd mu mus m1 m2 
        (inv : @head_inv c d pf cd mu mus m1 m2).

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
  All (fun mu2 => Consistent mu mu2) \o map (Inj.mu \o frame_mu0) $ mus.
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
by case: inv=> // A _ _; apply: (match_validblocks _ A).
Qed.

Lemma head_atext_inj ef sig args : 
  at_external (coreSem (cores_S (Core.i c))) (Core.c c) 
    = Some (ef,sig,args) -> 
  Mem.inject (as_inj mu) m1 m2.
Proof.
move=> atext; move: (head_match inv)=> mtch.
by case: (core_at_external (sims (Core.i c)) _ _ _ _ _ _ mtch atext).
Qed.

End head_inv_lems.

Lemma initial_SM_DomSrc dS dT fS fT j : DomSrc (initial_SM dS dT fS fT j) = dS.
Proof. by []. Qed.

Lemma initial_SM_DomTgt dS dT fS fT j : DomTgt (initial_SM dS dT fS fT j) = dT.
Proof. by []. Qed.

Lemma foreign_ofI b1 b2 d (mu : Inj.t) :
  as_inj mu b1 = Some (b2,d) -> 
  frgnBlocksSrc mu b1 -> 
  foreign_of mu b1 = Some (b2,d).
Proof.
case: mu; case=> /= lS lT pS pT lOf eS eT fS fT eOf wd. 
rewrite /as_inj /join /=.
move=> H f; move: H.
case e: (eOf _)=> [[x y]|//]; first by case=> -> ->; rewrite f.
move=> l; rewrite f.
by case: wd=> /= _ _ _ _ _; case/(_ _ f)=> ? []? []; rewrite e.
Qed.

Lemma consistent_refl j : consistent j j.
Proof. by move=> b1 b2 b2' d2 d2' ->; case=> -> ->. Qed.

Section head_inv_leakout.

Context c d pf cd mu mus m1 m2 
        (inv : @head_inv c d pf cd mu mus m1 m2).

Context pubS' pubT' vals1 vals2
        (inj : Mem.inject (as_inj mu) m1 m2)
        (vinj : Forall2 (val_inject (restrict (as_inj mu) (vis mu))) vals1 vals2)
        (eq1 : pubS' = fun b => locBlocksSrc mu b && REACH m1 (exportedSrc mu vals1) b)
        (eq2 : pubT' = fun b => locBlocksTgt mu b && REACH m2 (exportedTgt mu vals2) b).

Lemma vinj' : Forall2 (val_inject (as_inj mu)) vals1 vals2.
Proof. by move: vinj; apply: forall_vals_inject_restrictD. Qed.

Variable new_ix : 'I_N.

Let frgnS := REACH m1 (fun b => 
  isGlobalBlock (ge (cores_S new_ix)) b || getBlocks vals1 b).
Let frgnT := REACH m2 (fun b => 
  isGlobalBlock (ge (cores_T new_ix)) b || getBlocks vals2 b).

Let j := as_inj mu.
Let domS := DomSrc mu.
Let domT := DomTgt mu.

Let init_mu := initial_SM domS domT frgnS frgnT j.

Variable vis_rc : REACH_closed m1 (vis mu).

Lemma globs_in_frgn :
  {subset isGlobalBlock (ge (cores_S new_ix)) <= frgnBlocksSrc mu}.
Proof.
move: (head_match inv)=> mtch; apply match_genv in mtch.
move=> b H; case: mtch=> _; move/(_ b); apply.
by move: H; rewrite -(@isGlob_iffS' (Core.i c)).
Qed.

Lemma globs_in_vis :
  {subset isGlobalBlock (ge (cores_S new_ix)) <= vis mu}.
Proof. by move=> b; move/globs_in_frgn; apply: frgnBlocksSrc_vis. Qed.

Lemma blocks_in_vis : {subset getBlocks vals1 <= vis mu}.
Proof. by move=> b H2; apply: (getBlocks_restrict vinj H2). Qed.

Lemma globs_blocks_in_vis :
  {subset [predU isGlobalBlock (ge (cores_S new_ix)) & getBlocks vals1]
  <= vis mu}.
Proof. move=> b; case/orP; [by apply: globs_in_vis|by apply: blocks_in_vis]. Qed.

Lemma frgnS_sub_vis : {subset frgnS <= vis mu}.
Proof.
move=> b H; apply: vis_rc.
apply: (REACH_mono
  (fun b : block =>
    isGlobalBlock (ge (cores_S new_ix)) b || getBlocks vals1 b))=> //.
by apply: globs_blocks_in_vis.
Qed.

Lemma init_rel_inv_rest : All (rel_inv_pred m1 init_mu) mus.
Proof.
move: (head_rel inv) (head_match inv). 
elim: mus=> // a mus' IH /= []rel rall mtch; split=> //.
apply: Build_rel_inv.
case: rel; case=> H []H2 H3; split.
by rewrite initial_SM_as_inj.
split=> b H4; first by apply: (H2 _).
rewrite /DomTgt /= /domT.
by apply: H3.
case: rel=> _; case=> H []H2 H3.
split; first by rewrite initial_SM_as_inj.
split; first by rewrite initial_SM_DomSrc.
by [].
apply: Build_disjinv.
by rewrite predI01.
by rewrite predI01.
move=> b; move/andP=> /= []fS lS.
case: rel=> _ _; case=> d1 d2; move/(_ b)=> H _ _ _; apply: H.
apply/andP; split=> //=.
move: (frgnS_sub_vis fS); case/orP=> H.
move: d1; move/DisjointP; move/(_ b); rewrite H.
by move: lS; rewrite /in_mem /= => ->; case.
by [].
move=> b1 b2 d0; rewrite /foreign_of /=.
case: rel=> _ _; case=> d1 d2 _ H _ _.
case fS: (frgnS _)=> // J or; apply: H=> //. 
move: (frgnS_sub_vis fS); case/orP=> H.
have H2: locBlocksTgt mu b2.
+ by rewrite -(@as_inj_locBlocks mu _ _ _ (Inj_wd _) J).
case: (orP or)=> H3.
move: d1; move/DisjointP; move/(_ b1); rewrite H.
by move: H3; rewrite /in_mem /= => ->; case.
move: d2; move/DisjointP; move/(_ b2); rewrite H2.
by move: H3; rewrite /in_mem /= => ->; case.
by apply: foreign_ofI.
case: rel=> _ _; case=> _ _ _ _.
by rewrite /Consistent /= initial_SM_as_inj.
move=> b; case/andP=> /= H H2.
have H3: b \in vis mu.
{ apply match_visible in mtch; apply mtch.
  apply: (REACH_mono (vis init_mu))=> // b0; case/orP=> //= H3; apply: mtch.
  apply: (REACH_mono (fun b : block =>
    isGlobalBlock (ge (cores_S new_ix)) b || getBlocks vals1 b))=> //.
  move=> b1; case/orP=> H4.
  apply/orP; right; move: (head_match inv)=> mtch; apply match_genv in mtch.
  case: mtch=> _; move/(_ b1); apply.
  by move: H4; rewrite -(@isGlob_iffS' (Core.i c)).
  move: H4; case/(getBlocks_inject _ _ _ vinj _)=> b' []ofs' [].
  by move/restrictD_Some=> []_ H5. }
case: rel=> _ _; case=> d1 _ p1 _ _ _; apply: p1; apply/andP; split=> //.
case: (orP H3)=> // H4; move: d1; move/DisjointP; move/(_ b).
by move: H2 H4; rewrite /in_mem /= => -> ->; case.
by apply: IH.
Qed.

Let lo' := replace_locals mu pubS' pubT'.

Lemma lo_wd : SM_wd lo'.
move: vinj'=> H.
exploit eff_after_check1; eauto.
by move: (head_match inv); apply/match_sm_wd.
by move: (head_match inv); apply/match_validblocks.
by case=> wd.
Qed.

Let lo := Inj.mk lo_wd.

Lemma lo_valid : sm_valid lo m1 m2.
Proof.
move: vinj'=> H.
exploit eff_after_check1; eauto.
by move: (head_match inv); apply/match_sm_wd.
by move: (head_match inv); apply/match_validblocks.
by case=> _; case.
Qed.

Lemma init_rel_inv_mu : rel_inv_pred m1 init_mu $ Build_frame_pkg lo_valid.
Proof.
apply: Build_rel_inv.
split=> /=.
by rewrite replace_locals_as_inj initial_SM_as_inj; apply: inject_incr_refl.
split=> b.
by rewrite replace_locals_DomSrc initial_SM_DomSrc.
by rewrite replace_locals_DomTgt initial_SM_DomTgt.
split=> /=.
by rewrite replace_locals_as_inj initial_SM_as_inj /j => ? ? ? ->.
split=> b.
by rewrite replace_locals_DomSrc initial_SM_DomSrc /domS=> ->.
by rewrite replace_locals_DomTgt initial_SM_DomTgt /domT=> ->.
apply: Build_disjinv=> /=.
by rewrite predI01.
by rewrite predI01.
move=> b; move/andP=> /= []fS lS.
rewrite replace_locals_pubBlocksSrc eq1.
rewrite replace_locals_locBlocksSrc in lS.
apply/andP; split=> //.
apply: (REACH_mono 
  (fun b0 : block =>
    isGlobalBlock (ge (cores_S' new_ix)) b0 || getBlocks vals1 b0))=> //.
move=> b0; case/orP.
by move/globs_in_frgn; apply: frgnsrc_sub_exportedsrc.
by move=> get; apply/orP; left.
move=> b1 b2 d0.
case fS: (frgnS b1)=> // J or.
rewrite replace_locals_pub.
have lS: locBlocksSrc lo' b1.
{ case: (orP or)=> //.
  have J': as_inj lo' b1 = Some (b2,d0).
  + by rewrite replace_locals_as_inj.
  by rewrite /in_mem /= -(@as_inj_locBlocks lo' _ _ _ lo_wd J'). }
have ->: pubS' b1.
{ rewrite eq1; apply/andP; split. 
  by rewrite replace_locals_locBlocksSrc in lS.
  apply: (REACH_mono 
  (fun b0 : block =>
    isGlobalBlock (ge (cores_S' new_ix)) b0 || getBlocks vals1 b0))=> //.
  move=> b0; case/orP.
  by move/globs_in_frgn; apply: frgnsrc_sub_exportedsrc.
  by move=> get; apply/orP; left. }
rewrite -locBlocksSrc_as_inj_local=> //.
by apply: Inj_wd.
by rewrite replace_locals_locBlocksSrc in lS.
rewrite replace_locals_as_inj initial_SM_as_inj /j.
by apply: consistent_refl.
move=> b; move/andP=> /= []R. 
rewrite replace_locals_locBlocksSrc replace_locals_pubBlocksSrc eq1=> L.
apply/andP; split=> //.
apply: (REACH_mono (fun b : block =>
  isGlobalBlock (ge (cores_S new_ix)) b || getBlocks vals1 b)).
move=> b0; case/orP=> H. 
apply/orP; right; rewrite sharedSrc_iff_frgnpub. 
apply/orP; left. 
move: (head_match inv)=> mtch; apply match_genv in mtch.
case: mtch=> _; move/(_ b0); apply.
by move: H; rewrite -(@isGlob_iffS' (Core.i c)).
by apply: Inj_wd.
by apply/orP; left.
by move: R; apply: REACH_is_closed.
Qed.

Context (lo_mtch : 
           match_state (sims (Core.i c)) cd lo' (Core.c c) m1 
           (cast'' pf (Core.c d)) m2).

Lemma lo_inj : Mem.inject (as_inj (replace_locals mu pubS' pubT')) m1 m2.
Proof.
move: vinj'=> H.
exploit eff_after_check1; eauto.
by move: (head_match inv); apply/match_sm_wd.
by move: (head_match inv); apply/match_validblocks.
by case=> _; case=> _; case.
Qed.

Lemma lo_vinj : 
  Forall2 (val_inject (as_inj (replace_locals mu pubS' pubT'))) vals1 vals2.
Proof.
move: vinj'=> H.
exploit eff_after_check1; eauto.
by move: (head_match inv); apply/match_sm_wd.
by move: (head_match inv); apply/match_validblocks.
by case=> _; case=> _; case.
Qed.

Lemma lo_DomSrc : DomSrc lo' = DomSrc mu.
Proof.
by rewrite /DomSrc replace_locals_locBlocksSrc replace_locals_extBlocksSrc.
Qed.

Lemma lo_DomTgt : DomTgt lo' = DomTgt mu.
Proof.
by rewrite /DomTgt replace_locals_locBlocksTgt replace_locals_extBlocksTgt.
Qed.

Lemma lo_vis : vis lo' = vis mu.
Proof.
by rewrite /vis replace_locals_locBlocksSrc replace_locals_frgnBlocksSrc.
Qed.

Lemma lo_head_inv : @head_inv c d pf cd lo mus m1 m2.
Proof.
case: inv=> mtch all vis.
apply: Build_head_inv=> //.
clear - all; elim: mus all=> // mu0 mus' IH /= []rel rall.
split; last by apply: IH.
apply: Build_rel_inv.
split; first by rewrite replace_locals_as_inj; case: rel; case.
split=> b H; move: H.
rewrite lo_DomSrc; case: rel; case=> _; case; move/(_ b)=> H _ _ _ H2.
by apply: H.
rewrite lo_DomTgt; case: rel; case=> _; case=> _; move/(_ b)=> H _ _ H2.
by apply: H.
case: rel=> _; case=> H []H2 H3 _.
split; first by rewrite replace_locals_as_inj.
split; first by rewrite lo_DomSrc.
by rewrite lo_DomTgt.
case: rel=> _ _; case=> d1 d2 p1 p2 cons rc.
apply: Build_disjinv.
by rewrite replace_locals_locBlocksSrc.
by rewrite replace_locals_locBlocksTgt.
by rewrite replace_locals_frgnBlocksSrc.
by rewrite replace_locals_foreign.
by rewrite /Consistent /= replace_locals_as_inj.
case: rel=> _ _ _ H b; case/andP=> /= H2 H3; apply: H. 
by apply/andP; split=> //=; move: H2; rewrite lo_vis.
by case: vis=> rvis; apply: Build_vis_inv; rewrite lo_vis.
Qed.

End head_inv_leakout.

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
  [/\ All2 (rel_inv_pred m1 \o frame_mu0) mus 
    & frame_all mus m1 m2 s1 s2].

Lemma frame_all_inv mu0 m10 m20 x mus m1 m2 s1 s2 :
  frame_all (@Build_frame_pkg mu0 m10 m20 x :: mus) m1 m2 s1 s2 -> 
  exists c s1' d s2',
    [/\ s1 = c :: s1'
      , s2 = d :: s2' 
      & exists (pf : c.(Core.i)=d.(Core.i)) cd0,
        exists e1 ef_sig1 vals1,
        exists e2 ef_sig2 vals2, 
          [/\ @frame_inv c d pf cd0 mu0 
                m10 m1 e1 ef_sig1 vals1 m20 m2 e2 ef_sig2 vals2
            & frame_all mus m1 m2 s1' s2']].
Proof.
case: s1=> // c s1'; case: s2=> // d s2' /=.
move=> [][]pf => [][]cd []ef1 []sig1 []vals1 []ef2 []sig2 []vals2. 
case=> A B C D E F.
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
        c.(Core.c) m10 (cast'' pf d.(Core.c)) m20].
Proof.
case: s1=> // c s1'; case: s2=> // d s2' /=.
move=> [][]pf => [][]cd []ef1 []sig1 []vals1 []ef2 []sig2 []vals2 []A B C.
exists c, s1', d, s2'; split=> //.
by exists pf, cd. 
Qed.

Lemma frame_all_fwd1 pkg mus m1 m2 s1 s2 :
  frame_all (pkg :: mus) m1 m2 s1 s2 -> 
  mem_forward pkg.(frame_m10) m1.
Proof.
case: pkg=> ? ? ? ?.
move/frame_all_inv=> []? []? []? []? []? ? []? []? []? []? []? []? []? []? [].
by case.
Qed.

Lemma frame_all_fwd2 pkg mus m1 m2 s1 s2 :
  frame_all (pkg :: mus) m1 m2 s1 s2 -> 
  mem_forward pkg.(frame_m20) m2.
Proof.
case: pkg=> ? ? ? ?.
move/frame_all_inv=> []? []? []? []? []? ? []? []? []? []? []? []? []? []? [].
by case.
Qed.

Lemma frame_all_tail pkg mus m1 m2 s1 s2 :
  frame_all (pkg :: mus) m1 m2 s1 s2 -> 
  frame_all mus m1 m2 (STACK.pop s1) (STACK.pop s2).
Proof.
case: pkg=> ? ? ? ?.
move/frame_all_inv=> []? []? []? []? []-> ->. 
by move=> []? []? []? []? []? []? []? []? [] _.
Qed.

Section frame_all_lems.

Context mus m1 m2 s1 s2 
        (frameall : frame_all mus m1 m2 s1 s2).

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

Lemma frame_all_size_eq : size s1 = size s2.
Proof.
elim: mus s1 s2 m1 m2 frameall=> //; first by case=> //; case.
case=> ? ? ? ? mus' IH; case=> // a s1'; case=> // b s2' ? ?.
by move/frame_all_tail=> /= H; f_equal; apply: (IH _ _ _ _ H).
Qed.

End frame_all_lems.

Lemma tail_inv_inv mu0 m10 m20 x mus s1 s2 m1 m2 :
  tail_inv (@Build_frame_pkg mu0 m10 m20 x :: mus) 
           s1 s2 m1 m2 -> 
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
  tail_inv (@Build_frame_pkg mu0 m10 m20 x :: mus) 
           s1 s2 m1 m2 -> 
  exists c s1' d s2',
    [/\ s1 = c :: s1'
      , s2 = d :: s2' 
      & exists (pf : c.(Core.i)=d.(Core.i)) cd0,
        (sims c.(Core.i)).(match_state) cd0 mu0 
        c.(Core.c) m10 (cast'' pf d.(Core.c)) m20].
Proof. by move=> []_; move/frame_all_match. Qed.

Section tail_inv_lems.

Context mus s1 s2 m1 m2 
        (tlinv : tail_inv mus s1 s2 m1 m2).

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

Lemma tail_size_eq : size s1 = size s2.
Proof.
by case: tlinv=> _; move/frame_all_size_eq.
Qed.

Lemma head_tail_inv c d pf cd (mu : frame_pkg) e sig args1 args2
  (val : sm_valid mu m1 m2)
  (atext1 : at_external (coreSem (cores_S (Core.i c))) (Core.c c) 
            = Some (e,sig,args1))
  (atext2 : at_external (coreSem (cores_T (Core.i c))) 
            (cast'' pf (Core.c d)) = Some (e,sig,args2))
  (inj : Mem.inject (as_inj mu) m1 m2)
  (vals_inj : Forall2 (val_inject (restrict (as_inj mu) (vis mu))) args1 args2) 
  (inv : @head_inv c d pf cd mu mus m1 m2) :
  tail_inv [:: Build_frame_pkg val & mus] [:: c & s1] [:: d & s2] m1 m2.
Proof.
split=> /=.
split; first by apply: (head_rel inv).
by case: tlinv.
split. 
exists pf,cd,e,sig,args1,e,sig,args2; split=> //.
by apply: (head_match inv).
by apply: (head_vis inv).
by case: tlinv.
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

Lemma intern_incr_sharedSrc mu mu' : 
  intern_incr mu mu' -> 
  {subset (sharedSrc mu) <= sharedSrc mu'}.
Proof.
case. 
rewrite/sharedSrc/shared_of/join/foreign_of.
case: mu=> /=; case: mu'=> /= ? ? ? ? ? ? ? ? ? ?. 
move=> loc ? pub ? loc_of ? ? frgn ? ext.
move=> incr []<- []_ []_ []<- []_ []<- []_ _ b; rewrite/in_mem/=.
case: (frgn b)=> //. 
case: (ext b)=> //.
case: (pub b)=> //.
rewrite/inject_incr in incr.
case A: (loc_of b)=> [[? ?]|//]; first by move=> _; rewrite (incr _ _ _ A).
case: (pub b)=> //.
case A: (loc_of b)=> [[? ?]|//]; first by move=> _; rewrite (incr _ _ _ A).
Qed.

Lemma intern_incr_sharedTgt mu mu' : 
  intern_incr mu mu' -> 
  {subset (sharedTgt mu) <= sharedTgt mu'}.
Proof.
case. 
rewrite/sharedTgt/shared_of/join/foreign_of.
case: mu=> /=; case: mu'=> /= ? ? ? ? ? ? ? ? ? ?. 
move=> loc ? pub ? loc_of ? ? frgn ? ext.
by move=> incr []? []? []? []? []<- []? []<- _.
Qed.

Lemma foreign_of_extern_of mu b b' d' : 
  foreign_of mu b = Some (b',d') -> 
  extern_of mu b = Some (b',d').
Proof.
rewrite /foreign_of; case: mu=> ??????????.
by case: (_ b).
Qed.

Lemma mapped_frgnS_frgnT (mu : Inj.t) b b' d' : 
  as_inj mu b = Some (b',d') -> 
  vis mu b -> 
  (frgnBlocksSrc mu b <-> frgnBlocksTgt mu b').
Proof.
rewrite /as_inj /join; case E: (extern_of _ _)=> [[b'' d'']|].
case=> <- _ A; split=> B.
move: (frgnSrc _ (Inj_wd _) _ B)=> []b''' []d''' []C D.
have ->: b''=b''' by move: (foreign_of_extern_of C); rewrite E; case=> ->.
by apply: D.
case F: (frgnBlocksSrc mu b)=> //.
have G: unknown_of mu b = Some (b'',d'').
  have H: locBlocksSrc mu b=false. 
    case: (extern_DomRng _ (Inj_wd _) _ _ _ E).
    by move/(extBlocksSrc_locBlocksSrc _ (Inj_wd _) _)=> ->.
  rewrite/unknown_of; move: A E F H. 
  by case: (Inj.mu _)=> ??????????? /= -> -> ->.
move: (unknown_DomRng _ (Inj_wd _) _ _ _ G)=> []_ []_ []H _.
by move: A; rewrite /vis H /= F.
move/(local_DomRng _ (Inj_wd _) _)=> [].
move/(locBlocksSrc_frgnBlocksSrc _ (Inj_wd _))=> ->.
by move/(locBlocksTgt_frgnBlocksTgt _ (Inj_wd _))=> ->.
Qed.

Lemma intern_incr_as_inj_eq (mu mu' : Inj.t) b1 b2 b2' d2 d2' :
  intern_incr mu mu' -> 
  as_inj mu b1 = Some (b2,d2) -> 
  as_inj mu' b1 = Some (b2',d2') -> 
  b2=b2' /\ d2=d2'.
Proof.
rewrite /as_inj /join.
case e1: (extern_of mu b1)=> [[x y]|].
case e2: (extern_of _ _)=> [[x' y']|].
move=> incr; case=> <- <-; case=> <- <-.
case: incr=> _; case=> eq.
by rewrite eq in e1; rewrite e1 in e2; case: e2=> -> ->.
move=> incr; case=> <- <- L.
case: incr=> _; case=> eq.
by rewrite eq in e1; rewrite e1 in e2.
move=> incr L.
case e: (extern_of mu' b1)=> [[x y]|].
case: incr=> _; case=> eq.
by rewrite eq in e1; rewrite e1 in e.
by case: incr; move/(_ _ _ _ L)=> -> _; case=> -> ->.
Qed.

Section step_lems.

Context
(mu : Inj.t) m1 m2
(Esrc Etgt : Values.block -> BinNums.Z -> bool) 
(mu' : Inj.t) m1' m2'
(unch1 : Memory.Mem.unchanged_on (fun b ofs => Esrc b ofs=false) m1 m1')
(unch2 : Memory.Mem.unchanged_on (fun b ofs => Etgt b ofs=false) m2 m2')
(fwd1 : mem_forward m1 m1')
(fwd2 : mem_forward m2 m2')
(val : forall b ofs, Esrc b ofs -> (*Mem.valid_block m1 b ->*) vis mu b) 
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
(sep : sm_inject_separated mu mu' m1 m2)
(alloc : sm_locally_allocated mu mu' m1 m2 m1' m2')
(visrc : REACH_closed m1' (vis mu')).

Lemma rel_inv_pred_step pkg 
  (fwd10 : mem_forward pkg.(frame_m10) m1)
  (fwd20 : mem_forward pkg.(frame_m20) m2) :
  rel_inv_pred m1 mu pkg -> rel_inv_pred m1' mu' pkg.
Proof.
move=> []incr' sep' disj.
split; first by apply: (incr_trans incr' (intern_incr_incr incr)).
have incr'': inject_incr (as_inj mu) (as_inj mu').
  apply: intern_incr_as_inj=> /=; first by apply: incr.
  by generalize dependent mu'; case.
by apply: (sm_sep_step (frame_val pkg) sep' sep fwd10 fwd20 incr'').
by apply: (disjinv_intern_step disj incr fwd10 fwd20 sep' sep (frame_val pkg)).
move=> b; case/andP=> /= H H2; apply: frame_rc0; apply/andP; split=> //=.
apply visrc in H; case: {H}(orP H)=> H3.
case e: (DomSrc mu b).
case: (orP e)=> L; first by apply: REACH_nil; apply/orP; left.
case: incr=> _ []_ []_ []_ []_ []_ []_ []_ []eq _; rewrite eq in L.
move: L; rewrite locBlocksSrc_extBlocksSrc=> //.
by apply: Inj_wd.
have H4: DomSrc pkg b by apply/orP; left.
by case: incr'=> _ []; move/(_ b H4); rewrite e.
move: H3; case: incr=> _ []_ []_ []_ []_ []_ []<- _ H3.
by apply: REACH_nil; apply/orP; right.
Qed.

Lemma rel_inv_pred_step0 a pkg :
  rel_inv_pred m1' mu' pkg -> 
  rel_inv_pred m1 a pkg -> 
  rel_inv_pred m1' a pkg.
Proof.
move=> relinv []incr' sep' disj' rc'; split=> //.
move=> b; case/andP=> /= H H2. 
case: relinv=> _ _ disj rc.
have S: {subset [predD REACH m1' (vis a) & REACH m1 (vis a)]
        <= REACH m1' (vis mu')}.
{ move=> b0; case/andP=> /= H3 H4.
  apply (reach_upd (B:=vis a) (E:=Esrc) (m1:=m1))=> //.
  move=> b1 ofs E; suff: vis mu b1. 
  case: incr=> _ []_ []lSub []_ []_ []_ []fS _; case/orP=> L. 
  by apply/orP; left; apply: (lSub _ L).
  by apply/orP; right; rewrite -fS L.
  by apply: (val E). 
  move: alloc; rewrite sm_locally_allocatedChar; case.
  move=> A []B []C []D []E F b1 G.
  by apply/orP; rewrite C; left; apply/orP; right. }
have [T|T]: b \in REACH m1 (vis a)
     \/ b \in REACH m1' (vis mu').
{ case e: (b \in REACH m1 (vis a)); first by left.
  by right; apply: S; apply/andP; split=> //=; rewrite e. }
by apply: rc'; apply/andP; split.
by apply: rc; apply/andP; split.
Qed.

Lemma all_relinv_step mus s1 s2 :
  frame_all mus m1 m2 s1 s2 -> 
  All (rel_inv_pred m1 mu) mus -> 
  All (rel_inv_pred m1' mu') mus.
Proof.
elim: mus s1 s2=> // pkg mus' IH s1 s2 A /= => [][] B C.
move: (rel_inv_pred_step (frame_all_fwd1 A) (frame_all_fwd2 A) B)=> D.
by split=> //; last by apply: (IH _ _ (frame_all_tail A) C).
Qed.

Lemma all_relinv_step0 a mus :
  All (rel_inv_pred m1' mu') mus -> 
  All (rel_inv_pred m1 a) mus -> 
  All (rel_inv_pred m1' a) mus.
Proof.
elim: mus=> // pkg mus' IH /= => [][]B C []D E.
split; first by apply: (rel_inv_pred_step0 B D).
by apply: IH.
Qed.

Lemma frame_all_step mus s1 s2 :
  All (rel_inv_pred m1 mu) mus -> 
  frame_all mus m1 m2 s1 s2 -> 
  frame_all mus m1' m2' s1 s2.
Proof.
elim: mus s1 s2=> // pkg mus' IH s1' s2' E.
simpl in E; case: E=> E F.
case: pkg E=> mu0 m10 m20 val' E.

move/frame_all_inv.
move=> []c []s1'' []d []s2'' []-> ->.
move=> []pf []cd []e1 []sig1 []vals1 []e2 []sig2 []vals2.
move=> []inv all.

split.
exists pf,cd,e1,sig1,vals1,e2,sig2,vals2.

case: inv=> ? ? ? ? val'' frmatch ? ? frvinj visinv fwd1' fwd2' ? ?. 
apply: Build_frame_inv=> //.

by apply: (mem_forward_trans _ _ _ fwd1' fwd1). 
by apply: (mem_forward_trans _ _ _ fwd2' fwd2). 

apply: (mem_lemmas.unchanged_on_trans m10 m1 m1')=> //.
set pubSrc' := [predI locBlocksSrc mu0 & REACH m10 (exportedSrc mu0 vals1)].
set pubTgt' := [predI locBlocksTgt mu0 & REACH m20 (exportedTgt mu0 vals2)].
set mu0'    := replace_locals mu0 pubSrc' pubTgt'.
have wd: SM_wd mu0'. 
{ apply: replace_reach_wd=> //.
  by apply: (forall_vals_inject_restrictD _ _ _ _ frvinj). }
have J: disjinv mu0' mu by case: E=> /= ? ? ? ?; apply: disjinv_call.
apply: (@disjinv_unchanged_on_src (Inj.mk wd) mu Esrc)=> //.
move: (sm_valid_smvalid_src _ _ _ val')=> ?.
apply: smvalid_src_replace_locals=> //=.
by apply: (smvalid_src_fwd fwd1').
by move=> x y H _; apply (val H).

apply: (mem_lemmas.unchanged_on_trans m20 m2 m2')=> //.
set pubSrc' := [predI locBlocksSrc mu0 & REACH m10 (exportedSrc mu0 vals1)].
set pubTgt' := [predI locBlocksTgt mu0 & REACH m20 (exportedTgt mu0 vals2)].
set mu0'    := replace_locals mu0 pubSrc' pubTgt'.
have J: disjinv mu0' mu by case: E=> /= ? ? ? ?; apply: disjinv_call.
have wd: SM_wd mu0'. 
{ apply: replace_reach_wd=> //.
  by apply: (forall_vals_inject_restrictD _ _ _ _ frvinj). }
apply: (@disjinv_unchanged_on_tgt (Inj.mk wd) mu Esrc Etgt 
  m10 m1 m2 m2' fwd1')=> //.
move=> b'; case: val''; move/(_ b')=> I _ Q; apply: I.
by rewrite replace_locals_DOM in Q.

by eapply IH; eauto.
Qed.

Lemma tail_inv_step mus s1 s2 :
  All (rel_inv_pred m1 mu) mus -> 
  tail_inv mus s1 s2 m1 m2 -> 
  tail_inv mus s1 s2 m1' m2'.
Proof. 
move=> A []B C; split=> //; last by apply: frame_all_step. 
elim: mus A B s1 s2 C=> // a mus' IH all all2 s1 s2 frall.
move: (frame_all_tail frall)=> frall'.
move: all=> /= [] rel all; move: all2=> /= [] all0 all2; split.
apply: all_relinv_step0=> //.
apply all_relinv_step with (s1 := STACK.pop s1) (s2 := STACK.pop s2)=> //.
by apply: (IH all all2 _ _ frall').
Qed.

Lemma vis_inv_step (c c' : Core.t cores_S) :
  vis_inv c mu -> 
  RC.args (Core.c c)=RC.args (Core.c c') -> 
  RC.rets (Core.c c)=RC.rets (Core.c c') -> 
  RC.locs (Core.c c') 
    = (fun b => RC.locs (Core.c c) b
             || freshloc m1 m1' b 
             || RC.reach_set (ge (cores_S (Core.i c))) (Core.c c) m1 b) ->
  REACH_closed m1 (vis mu) -> 
  vis_inv c' mu'.
Proof.
move=> E A B C rc; move: E.
case=> E; apply: Build_vis_inv=> b F.
move: F; rewrite/RC.reach_basis/in_mem/=; move/orP=> [|F].
rewrite -A -B=> F. 
by apply: (intern_incr_vis _ _ incr); apply: E; apply/orP; left.
case G: (RC.locs (Core.c c) b). 
by apply: (intern_incr_vis _ _ incr); apply: E; apply/orP; right.
move: G F; rewrite C=> -> /=; case/orP=> H.
move: alloc; rewrite sm_locally_allocatedChar /vis; case. 
by move=> _ []_ []-> _; rewrite H -orb_assoc orb_comm.
suff: vis mu b. 
rewrite /vis; case: incr=> _ []_ []sub1 []_ []_ []_ []<- _; case/orP.
by move/sub1=> ->.
by move=> ->; rewrite orb_comm.
apply: rc; apply: (REACH_mono _ _ _ _ _ H)=> //.
move=> b0 H2; move: (E b0); rewrite /in_mem /=; apply.
apply: (RC.reach_basis_domains_eq _ H2).
by apply: genvs_domain_eq_sym; apply: (my_ge_S (Core.i c)).
Qed.

Lemma head_inv_step 
    c d (pf : Core.i c=Core.i d) c' (d' : C (cores_T (Core.i d)))
    cd cd' mus s1 s2 U :
  head_inv pf cd mu mus m1 m2 -> 
  frame_all mus m1 m2 s1 s2 -> 
  RC.args (Core.c c)=RC.args c' -> 
  RC.rets (Core.c c)=RC.rets c' -> 
  RC.locs c' = (fun b => RC.locs (Core.c c) b 
    || freshloc m1 m1' b
    || RC.reach_set (ge (cores_S (Core.i c))) (Core.c c) m1 b) ->
  effect_semantics.effstep 
    (coreSem (cores_S (Core.i c))) (ge (cores_S (Core.i c))) U 
    (Core.c c) m1 c' m1' -> 
  match_state (sims (Core.i (Core.upd c c'))) cd' mu'
    (Core.c (Core.upd c c')) m1'
    (cast'' pf (Core.c (Core.upd d d'))) m2' -> 
  RC.locs c' 
    = (fun b => RC.locs (Core.c c) b
             || freshloc m1 m1' b 
             || RC.reach_set (ge (cores_S (Core.i c))) (Core.c c) m1 b) ->
  @head_inv (Core.upd c c') (Core.upd d d') pf cd' mu' mus m1' m2'.
Proof.
move=> hdinv frame args rets mylocs effstep mtch locs.
apply: Build_head_inv=> //.
by apply: (all_relinv_step frame); apply: (head_rel hdinv).
+ case: hdinv=> hdmtch ? A; apply: (vis_inv_step A)=> //.
  by apply match_visible in hdmtch.
Qed.

End step_lems.

Section R.

Import CallStack.
Import Linker.
Import STACK.

Record R (data : sig_data N (fun ix : 'I_N => (sims ix).(core_data))) 
         (mu : SM_Injection)
         (x1 : linker N cores_S) m1 (x2 : linker N cores_T) m2 := 
  { (* local defns. *)
    s1  := x1.(stack) 
  ; s2  := x2.(stack) 
  ; pf1 := CallStack.callStack_nonempty s1 
  ; pf2 := CallStack.callStack_nonempty s2 
  ; c   := STACK.head _ pf1 
  ; d   := STACK.head _ pf2 

    (* main invariant *)
  ; R_inv : 
    exists (pf : c.(Core.i)=d.(Core.i)) (mu_top : Inj.t) mus, 
    [/\ mu = mu_top
      , exists pf2 : projT1 data = c.(Core.i),
          @head_inv c d pf (cast_ty (lift_eq _ pf2) (projT2 data)) 
          mu_top mus m1 m2 
      & tail_inv mus (pop s1) (pop s2) m1 m2] 

    (* side conditions *)
  ; R_fntbl : x1.(fn_tbl)=x2.(fn_tbl) }.

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
  (cast'' peek_ieq (Core.c (peekCore x2))) m2.
Proof.
move: (R_inv pf)=> []A []mu_top []mus []eq []pf2.
move/head_match=> MATCH ?.
have ->: (cast'' peek_ieq (Core.c (peekCore x2)) 
         = cast'' A (Core.c (peekCore x2)))
  by f_equal; f_equal; apply proof_irr.
exists (cast_ty (lift_eq _ pf2) (projT2 data)). 
by exists mu_top.
Qed.

Lemma R_AllDisjointS 
    (mu_top : frame_pkg) (mus : seq frame_pkg) 
    c d (eq : Core.i c=Core.i d) cd s1 s2 :
  head_inv eq cd mu_top mus m1 m2 -> 
  tail_inv mus s1 s2 m1 m2 -> 
  AllDisjoint locBlocksSrc \o map (Inj.mu \o frame_mu0) 
    $ mu_top :: mus.
Proof.
move=> /= B C; split.
move: (head_AllDisjointLS B)=> D. 
by apply: D.
by apply: (tail_AllDisjointLS C).
Qed.

Lemma R_AllDisjointT
    (mu_top : frame_pkg) (mus : seq frame_pkg) 
    c d (eq : Core.i c=Core.i d) cd s1 s2 :
  head_inv eq cd mu_top mus m1 m2 -> 
  tail_inv mus s1 s2 m1 m2 -> 
  AllDisjoint locBlocksTgt \o map (Inj.mu \o frame_mu0) 
    $ mu_top :: mus.
Proof.
move=> /= B C; split.
by move: (head_AllDisjointLT B)=> D.
by apply: (tail_AllDisjointLT C).
Qed.

Lemma R_AllConsistent 
    (mu_top : frame_pkg) (mus : seq frame_pkg) 
    c d (eq : Core.i c=Core.i d) cd s1 s2 :
  head_inv eq cd mu_top mus m1 m2 -> 
  tail_inv mus s1 s2 m1 m2 -> 
  AllConsistent \o map (Inj.mu \o frame_mu0) 
    $ mu_top :: mus.
Proof.
move=> /= B C; split.
by move: (head_AllConsistent B)=> D.
by apply: (tail_AllConsistent C).
Qed.

Lemma R_len_callStack : size (callStack x1) = size (callStack x2).
Proof.
case: (R_inv pf)=> []A []mu_top []mus []eq []pf2 D.
move/tail_size_eq; rewrite /s1 /s2.
have l1: ssrnat.leq 1 (size (callStack x1)). 
  by move: (callStack_wf x1); move/andP=> [].
have l2: ssrnat.leq 1 (size (callStack x2)). 
  by move: (callStack_wf x2); move/andP=> [].
by apply: pop_size.
Qed.

Lemma R_inContext : inContext x1 -> inContext x2.
Proof. by rewrite /inContext /callStackSize R_len_callStack. Qed.

Lemma R_inContext' : inContext x2 -> inContext x1.
Proof. by rewrite /inContext /callStackSize R_len_callStack. Qed.

Lemma R_wd : SM_wd mu.
Proof.
case: (R_inv pf)=> pf2 []mu_top []mus []eq []pf3 [].
by move/match_sm_wd=> wd _ _ _; rewrite eq.
Qed.

End R_lems.

Section initCore_lems.

Context (my_cores : 'I_N -> t) c1 ix v vs 
        (init1 : initCore my_cores ix v vs = Some c1).

Lemma initCore_ix : ix = Core.i c1.
Proof.
move: init1; rewrite /init1 /initCore.
by case: (core_semantics.initial_core _ _ _ _)=> // c; 
  case; case: c1=> ? ?; case.
Qed.

End initCore_lems.

Section initCore_lems2.

Context c1 ix v vs (init1 : initCore cores_S ix v vs = Some c1).

Lemma initCore_args : RC.args (Core.c c1) = vs.
Proof.
move: init1; rewrite /initCore /= /RC.initial_core.
case: (initial_core _ _ _ _)=> // c. 
by case; case: c1=> ?; case=> ? ? ? ? /=; case=> _ _ ->.
Qed.

Lemma initCore_rets : RC.rets (Core.c c1) = [::].
Proof.
move: init1; rewrite /initCore /= /RC.initial_core.
case: (initial_core _ _ _ _)=> // c. 
by case; case: c1=> ?; case=> ? ? ? ? /=; case=> _ _ _ ->.
Qed.

Lemma initCore_locs : RC.locs (Core.c c1) = (fun _ => false).
Proof.
move: init1; rewrite /initCore /= /RC.initial_core.
case: (initial_core _ _ _ _)=> // c. 
by case; case: c1=> ?; case=> ? ? ? ? /=; case=> _ _ _ _ ->.
Qed.

End initCore_lems2.

Section call_lems.

Context
(mu : Inj.t) m1 m2 ef sig args1 
(st1 st1' : linker N cores_S) cd st2 id 
(valid : sm_valid mu m1 m2)
(fid : LinkerSem.fun_id ef = Some id)
(atext1 : LinkerSem.at_external0 st1 = Some (ef,sig,args1))
(hdl1 : LinkerSem.handle id st1 args1 = Some st1')
(inv : R cd mu st1 m1 st2 m2).

Lemma atext2 : 
  exists args2, 
  LinkerSem.at_external0 st2 = Some (ef,sig,args2).
Proof.
case: (R_inv inv)=> pf []mu_top []mus []eq []pf2; move/head_match.
unfold LinkerSem.at_external0 in atext1.
have atext1':
  at_external 
    (coreSem (cores_S (Core.i (peekCore st1)))) 
    (Core.c (peekCore st1)) =
  Some (ef,sig,args1) by rewrite /RC.at_external.
move=> hd_match _.
case: (core_at_external (sims (Core.i (c inv))) 
      _ _ _ _ _ _ hd_match atext1').
move=> inj []defs []args2 []valinj []atext2 []defs2 extends; exists args2.
set T := C \o cores_T.
rewrite /LinkerSem.at_external0.
set P := fun ix (x : T ix) => 
            at_external (coreSem (cores_T ix)) x
            = Some (ef, sig, args2).
change (P (Core.i (peekCore st2)) (Core.c (peekCore st2))).
have X: (P (Core.i (c inv)) (cast'' pf (Core.c (d inv)))).
{ move: atext2=> /=; rewrite /RC.at_external /P /=.
  have eq': at_external (coreSem (cores_T (Core.i (c inv))))
            (cast'' pf (Core.c (d inv))) =
           at_external (coreSem (cores_T (Core.i (d inv))))
            (Core.c (d inv)). 
  { set T' := C \o cores_T.
    set P' := fun ix (x : T' ix) => 
                 at_external (coreSem (cores_T ix)) x
                 = at_external (coreSem (cores_T (Core.i (d inv))))
                     (Core.c (d inv)).
    change (P' (Core.i (c inv)) 
               (cast T' (sym_eq pf) (Core.c (d inv)))).
    by apply: cast_indnatdep. }
  by []. }
by apply: (cast_indnatdep' X).
Qed.

Lemma vis_sub_DomSrc (mu0 : Inj.t) : {subset vis mu0 <= DomSrc mu0}.
Proof.
move=> b; case/orP; rewrite /DomSrc.
by rewrite /in_mem /= => ->.
by move/frgnsrc_sub_extsrc=> H; apply/orP; right.
Qed.

Import CallStack.

Require Import sepcomp.compcert. Import CompcertLibraries.

Lemma hdl2 args2 : 
  LinkerSem.at_external0 st2 = Some (ef,sig,args2) -> 
  exists cd' st2' mu',
    LinkerSem.handle id st2 args2 = Some st2'
    /\ R cd' mu' st1' m1 st2' m2.
Proof.
move=> A.
case: (R_inv inv)=> pf []mu_top []mus []mu_eq.
move=> []pf2 hdinv tlinv; move: hdl1; rewrite LinkerSem.handleP.
move=> []all_at1 []ix []c1 []fntbl1 init1 st1'_eq.

have atext1': 
  at_external (coreSem (cores_S (Core.i (c inv)))) (Core.c (c inv)) 
  = Some (ef,sig,args1) by [].

have atext2': 
  at_external (coreSem (cores_T (Core.i (c inv)))) 
              (cast'' pf (Core.c (d inv)))
  = Some (ef,sig,args2).
 { set T := C \o cores_T.
   set P := fun ix (x : T ix) => 
              at_external (coreSem (cores_T ix)) x
              = Some (ef, sig, args2).
   have: (P (Core.i (d inv)) (Core.c (d inv)))
     by rewrite /LinkerSem.at_external0.
   by apply: cast_indnatdep. }

have atext2'': 
  at_external (coreSem (cores_T (Core.i (c inv))))
              (cast'' pf (Core.c (d inv)))
  = Some (ef,sig,args2).
 { set T := C \o cores_T.
   set P := fun ix (x : T ix) => 
              at_external (coreSem (cores_T ix)) x
              = Some (ef, sig, args2).
   have: (P (Core.i (d inv)) (Core.c (d inv)))
     by rewrite /LinkerSem.at_external0.
   by apply: cast_indnatdep. }

case: (core_at_external (sims (Core.i (c inv))) 
      _ _ _ _ _ _ (head_match hdinv) atext1').
move=> inj []defs1 []args2' []vinj []atext2''' []defs2 extends.

have eq: args2 = args2' by move: atext2'''; rewrite atext2''; case.
subst args2'.

have exportedSrc_DomSrc:
  forall b, exportedSrc mu_top args1 b -> DomSrc mu_top b.
{ rewrite /exportedSrc=> b; move/orP; case.
  case/(getBlocks_inject _ _ _ vinj _)=> b' []ofs' [].
  move/restrictD_Some=> []H _ _.  
  by case: (as_inj_DomRng _ _ _ _ H (Inj_wd _)). 
  by apply: sharedsrc_sub_domsrc. }

have exportedTgt_DomTgt:
  forall b, exportedTgt mu_top args2 b -> DomTgt mu_top b.
{ rewrite /exportedTgt=> b; move/orP; case.
  move=> get2.
  have [b0 [ofs [getbs1 asinj1]]]: 
    exists b0 ofs, 
    [/\ getBlocks args1 b0
      & as_inj mu_top b0 = Some (b,ofs)]. 
  { move: (forall_inject_val_list_inject _ _ _ vinj)=> vinj'.
    case: (vals_def_getBlocksTS vinj' defs1 get2)=> x' []y' []? res.
    exists x',y'; split=> //.
    by case: (restrictD_Some _ _ _ _ _ res). }
  by case: (as_inj_DomRng _ _ _ _ asinj1 (Inj_wd _))=> _ ->. 
  by apply: sharedtgt_sub_domtgt. }

set (j := as_inj mu_top).
set (domS := DomSrc mu_top).
set (domT := DomTgt mu_top).
set (frgnS := REACH m1 (fun b => 
  isGlobalBlock (ge (cores_S (Core.i c1))) b || getBlocks args1 b)).
set (frgnT := REACH m2 (fun b => 
  isGlobalBlock (ge (cores_T (Core.i c1))) b || getBlocks args2 b)).

have j_domS_domT:
  forall b1 b2 d0,
  j b1 = Some (b2, d0) -> domS b1 = true /\ domT b2 = true.
{ move=> b1 b2 d0; rewrite /j /domS /domT; move/as_inj_DomRng.
  by move/(_ (Inj_wd _)). }

have DomTgt_rc: REACH_closed m2 (DomTgt mu_top).
  admit.

have frgnT_sub_domT: {subset frgnT <= domT}.
{ move=> b H; apply: DomTgt_rc. 
  apply: (REACH_mono (fun b : block =>
    isGlobalBlock (ge (cores_T (Core.i c1))) b || getBlocks args2 b))=> //.
  move=> b0 H2; apply: exportedTgt_DomTgt; apply/orP; case: (orP H2)=> H3.
  right; apply/orP; left. 
  move: (H3); rewrite -isGlob_iffT=> H3'.
  move: (head_globs hdinv); move/(_ b0 H3')=> H4.
  have J: extern_of mu_top b0 = Some (b0,0).
  { move: (head_match hdinv)=> mtch; apply match_genv in mtch.
    case: mtch=> pres _.
    move: (meminj_preserves_globals_isGlobalBlock _ _ pres b0)=> H5. 
    by move: H3'; rewrite isGlob_iffS; eauto. }
  case: (Inj_wd mu_top)=> _ _ _ _ _; case/(_ b0 H4)=> x []y []H5 H6 _ _.
  by move: H6; rewrite H5 in J; case: J=> ->.
  by left. }

have st1_eq: callStack (stack st1) = [:: c inv & STACK.pop st1].
{ by rewrite /c /s1; case: st1 inv=> //= ?; case=> //=; case. }

have st2_eq: callStack (stack st2) = [:: d inv & STACK.pop st2].
{ by rewrite /d /s2; case: st2 inv=> //= ?; case=> //=; case. }

have all_at2: all (atExternal cores_T) (CallStack.callStack st2).
{ move: (callStack_wf st2); move/andP=> []atext_tail _; rewrite st2_eq.
  move=> /=; apply/andP; split=> //.
  move: A; rewrite /LinkerSem.at_external0 /atExternal.
  rewrite /d /s2 /pf2 /peekCore.
  by case: (STACK.head _ _)=> ? /= d atext2; rewrite /RC.at_external atext2. }

have globs_frgnS:
  forall b,
  isGlobalBlock (ge (cores_S (Core.i c1))) b ->
  frgnBlocksSrc mu_top b.
{ move=> b H; case: (match_genv (head_match hdinv))=> _; move/(_ b); apply.  
  move: H; rewrite -(initCore_ix init1).
  have eq: genvs_domain_eq (ge (cores_S ix)) (ge (cores_S (Core.i (c inv)))).
    apply genvs_domain_eq_trans with (ge2 := my_ge)=> //.
    by apply: (genvs_domain_eq_sym _ _ (my_ge_S ix)).
  by rewrite (genvs_domain_eq_isGlobal _ _ eq). }

have presglobs: meminj_preserves_globals (ge (cores_S (Core.i c1))) j.
{ move: (head_presglobs hdinv).
  rewrite -meminj_preserves_genv2blocks.
  rewrite (genvs_domain_eq_match_genvs (my_ge_S (Core.i c1))).
  rewrite meminj_preserves_genv2blocks.
  rewrite match_genv_meminj_preserves_extern_iff_all=> //.
  by apply: Inj_wd. }

have globs_frgnT:
  forall b,
  isGlobalBlock (ge (cores_T (Core.i c1))) b ->
  frgnBlocksTgt mu_top b.
{ move=> b H; case: (match_genv (head_match hdinv))=> _; move=> I. 
  have fS: frgnBlocksSrc mu_top b.
  { apply: I; move: H; rewrite -(initCore_ix init1).
    have eq: genvs_domain_eq (ge (cores_T ix)) (ge (cores_S (Core.i (c inv)))).
      apply genvs_domain_eq_trans with (ge2 := my_ge)=> //.
      by apply: (genvs_domain_eq_sym _ _ (my_ge_T ix)).
    by rewrite (genvs_domain_eq_isGlobal _ _ eq). }
  case: (frgnSrc _ (Inj_wd _) _ fS)=> b' []d []fOf fT.
  have eq: b=b'. 
  { case: (match_genv (head_match hdinv))=> [][]J []K L _.
    have H': isGlobalBlock (ge (cores_S (Core.i (c inv)))) b.
    { erewrite isGlob_iffST'; eauto. }
    move: H'; rewrite /isGlobalBlock /=.
    case e1: (Genv.invert_symbol _ _)=> //=.
    move: (Genv.invert_find_symbol _ _ e1)=> M O.
    move: (J _ _ M)=> E.
    by move: (foreign_in_extern _ _ _ _ fOf); rewrite E; case.
    case e2: (Genv.find_var_info _ _)=> //[gv].
    move: (K _ _ e2).
    by move: (foreign_in_extern _ _ _ _ fOf)=> ->; case. }
  by rewrite eq. }

have vinj': Forall2 (val_inject (as_inj mu_top)) args1 args2. 
{ by apply: (forall_vals_inject_restrictD _ _ _ _ vinj). }

have domS_valid:
  forall b, domS b -> Mem.valid_block m1 b.
{ by move: (match_validblocks _ (head_match hdinv)); case=> H I; apply: H. }

have domT_valid:
  forall b, domT b -> Mem.valid_block m2 b.
{ 
(*by move: (match_validblocks _ (head_match hdinv)); case=> H I; apply: I.*)
admit.
}

have [cd_new [c2 [pf_new [init2 mtch12]]]]:
  exists (cd_new : core_data (sims (Core.i c1))) 
         (c2 : Core.t cores_T)
         (pf : Core.i c1 = Core.i c2),
    [/\ initCore cores_T ix (Vptr id Integers.Int.zero) args2 = Some c2
      & match_state (sims (Core.i c1)) cd_new
        (initial_SM domS domT frgnS frgnT j) 
        (Core.c c1) m1 (cast'' pf (Core.c c2)) m2].
{ move: init1; rewrite /initCore.
  case init1: (core_semantics.initial_core _ _ _ _)=> //[c1']; case=> X.
  generalize dependent c1; case=> c1_i c1; intros.
  move: (X) init1; case=> eq _ init1; subst ix=> /=.
  case: (core_initial _ _ _ _ (sims c1_i) _ 
         args1 _ m1 j args2 m2 domS domT init1 inj vinj')=> //.
  move=> cd' []c2' []init2 mtch_init12.
  exists cd',(Core.mk N cores_T c1_i c2'),erefl.
  move: init2=> /= ->; split=> //=.
  rewrite cast_ty_erefl; move: X; case=> X.
  move: (EqdepFacts.eq_sigT_snd X)=> /= <-. 
  rewrite -Eqdep_dec.eq_rect_eq_dec; first by apply: mtch_init12.
  move=> m n; case e: (m == n); first by left; move: (eqP e).
  right=> Contra; rewrite Contra in e. 
  by rewrite eq_refl in e. }

set (st2' := pushCore st2 c2 all_at2).

have eq1: 
    Core.i (STACK.head st1' (callStack_nonempty st1'))
  = Core.i c1.
{ by rewrite st1'_eq. }

have eq2: 
    Core.i (STACK.head st2' (callStack_nonempty st2'))
  = Core.i c2.
{ by []. }

set mu_new := initial_SM domS domT frgnS frgnT j.

have mu_new_wd: SM_wd mu_new.
{ apply: initial_SM_wd=> //.
  move=> b1; apply: REACH_inject=> // b; case/orP=> H.  
  move: (meminj_preserves_globals_isGlobalBlock _ _ presglobs _ H)=> H2.
  exists b,0; split=> //; apply/orP; left.
  by move: H; rewrite -(@isGlob_iffS (Core.i c1)) (@isGlob_iffT (Core.i c1)).
  case: (getBlocks_inject _ _ _ vinj' _ H)=> x []y []H2 H3.
  by exists x,y; split=> //; apply/orP; right.
  move=> b H; move: (head_match hdinv)=> mtch; apply match_visible in mtch.
  suff: vis mu_top b by apply: vis_sub_DomSrc.
  apply: mtch; apply: (REACH_mono 
    (fun b : block =>
      isGlobalBlock (ge (cores_S (Core.i c1))) b || getBlocks args1 b))=> //.
  by move=> b0; eapply globs_blocks_in_vis; eauto. }

set mu_new' := Inj.mk mu_new_wd.

case: (extends _ _ erefl erefl _ erefl). 

(* mu_pkg is leak-out(mu_top) *)

set mu_pkg' := 
  (replace_locals mu_top
  (fun b : block =>
    locBlocksSrc mu_top b && REACH m1 (exportedSrc mu_top args1) b)
  (fun b : block =>
    locBlocksTgt mu_top b && REACH m2 (exportedTgt mu_top args2) b)).

move=> mtch_pkg inj_pkg.

have mu_pkg_wd: SM_wd mu_pkg'.
{ by exploit lo_wd; eauto. }

set mu_pkg := Inj.mk mu_pkg_wd.

have valid': sm_valid mu_pkg m1 m2. 
{ by apply match_validblocks in mtch_pkg. }

set pkg := Build_frame_pkg valid'.

have mu_pkg_as_inj: as_inj mu_pkg = as_inj mu_top.
{ by rewrite /mu_pkg /= replace_locals_as_inj. }

have pkg_hdinv: 
  head_inv pf
  (cast (fun ix : 'I_N => core_data (sims ix)) pf2 (projT2 cd))
  pkg mus m1 m2.
{ move: (@lo_head_inv (c inv) (d inv) pf 
    (cast (fun ix0 : 'I_N => core_data (sims ix0)) pf2 (projT2 cd))
    mu_top mus m1 m2 hdinv _ _ args1 args2 inj vinj erefl erefl mtch_pkg).
  rewrite /pkg /= /mu_pkg.
  have ->: lo_wd _ _ _ _ _ = mu_pkg_wd by move=> *; apply: proof_irr.
  apply. }

have mu_new_rel_inv_pkg: rel_inv_pred m1 mu_new pkg.
{ apply init_rel_inv_mu
    with (c := c inv) (d := d inv) (pf := pf) 
         (cd := (cast (fun ix : 'I_N => core_data (sims ix)) pf2 (projT2 cd))) 
         (mus := mus)
         (inv := hdinv) (inj := inj) (vinj := vinj)
         (eq1 := erefl) (eq2 := erefl). }

have mu_new_rel_inv_all: 
  All (rel_inv_pred m1 (initial_SM domS domT frgnS frgnT j)) mus.
{ apply init_rel_inv_rest
    with (c := c inv) (d := d inv) (pf := pf) 
         (cd := (cast (fun ix : 'I_N => core_data (sims ix)) pf2 (projT2 cd))) 
         (mus := mus)=> //.
  by move: (head_match hdinv)=> mtch; apply match_visible in mtch. }

have mu_new_vis_inv: vis_inv c1 mu_new'.
{ apply: Build_vis_inv=> // b; rewrite /in_mem /= => Y.
  rewrite /vis /mu_new /frgnS /exportedSrc /=.
  move: Y; rewrite /RC.reach_basis; case/orP.
  case/orP. case/orP. move=> H1.
  have H1': isGlobalBlock (ge (cores_S' (Core.i c1))) b.
  { by rewrite -isGlob_iffS. }
  by apply: REACH_nil; apply/orP; left.
  move=> getB; apply: REACH_nil; apply/orP; right.
  have eq: RC.args (Core.c c1) = args1. 
  { erewrite initCore_args; eauto. }
  by rewrite eq in getB.
  have eq: RC.rets (Core.c c1) = [::]. 
  { erewrite initCore_rets; eauto. }
  by rewrite eq getBlocksD_nil.
  have eq: RC.locs (Core.c c1) = (fun _ => false).
  { erewrite initCore_locs; eauto. }
  by rewrite eq. }

have hdinv_new:
  head_inv pf_new cd_new mu_new' (pkg :: mus) m1 m2.
{ by apply: Build_head_inv. }

exists (existT _ (Core.i c1) cd_new),st2',mu_new'; split.
rewrite LinkerSem.handleP; exists all_at2,ix,c2; split=> //.
by move: fntbl1; rewrite (R_fntbl inv).

have valid_new: sm_valid mu_new' m1 m2. 
{ move: (head_match hdinv)=> mtch; apply match_validblocks in mtch.
  by apply: mtch. }

set (pkg_new := Build_frame_pkg valid_new).

have pf_new':
    Core.i (STACK.head st1' (callStack_nonempty st1'))
  = Core.i (STACK.head st2' (callStack_nonempty st2')).
{ by rewrite eq1 eq2; apply: pf_new. }

apply: Build_R.
exists pf_new',mu_new',[:: pkg & mus]; split=> //.
rewrite ->st1'_eq in *; rewrite /=.

have eq: Core.i c1 
       = Core.i (SeqStack.head (callStack (stack st1')) 
                (callStack_nonempty (stack st1'))).
{ by clear - st1'_eq; rewrite st1'_eq. }

exists eq; move: hdinv_new.
have hd_eq: 
  SeqStack.head (CallStack.callStack (stack st1')) (callStack_nonempty st1')
= c1.
{ by clear - st1'_eq; rewrite st1'_eq. }

clear - hd_eq; move: hd_eq eq pf_new'=> /=. 
set pf := (callStack_nonempty st1').
set q  := (SeqStack.head (CallStack.callStack (stack st1')) pf).
subst q=> -> eq; have ->: eq = erefl (Core.i c1) by apply: proof_irr.
rewrite cast_ty_erefl=> pf_new'.
by have ->: pf_new' = pf_new by apply: proof_irr.

have valid'': sm_valid pkg m1 m2 by apply: valid'.
have vinj'': 
  Forall2 (val_inject (restrict (as_inj pkg) (vis pkg))) args1 args2.
{ rewrite mu_pkg_as_inj; apply: restrict_forall_vals_inject=> //.
  move=> b H; move: (blocks_in_vis vinj); move/(_ b H).
  case/orP=> H2; apply/orP.
  by rewrite replace_locals_locBlocksSrc; left.
  by rewrite replace_locals_frgnBlocksSrc; right. }
have inj': Mem.inject (as_inj pkg) m1 m2.
{ by rewrite mu_pkg_as_inj. }
move: (head_tail_inv tlinv valid'' atext1' atext2' inj' vinj'' pkg_hdinv).
rewrite /s1 /s2 st1'_eq /st2' /pkg /= => tlinv'. 
by rewrite st1_eq st2_eq; apply: tlinv'.
by rewrite st1'_eq /st2'; apply: (R_fntbl inv).
Qed.

End call_lems.

(*TODO: move me into inj_lemmas.v*)
Lemma sm_inject_separated_replace_locals mu X Y mu' m1 m2 : 
  sm_inject_separated mu mu' m1 m2 -> 
  sm_inject_separated (replace_locals mu X Y) mu' m1 m2.
Proof.
case.
rewrite /sm_inject_separated.
rewrite replace_locals_DomSrc.
rewrite replace_locals_DomTgt.
rewrite replace_locals_as_inj.
by [].
Qed.

Section return_lems.

Context
(mu : Inj.t) m1 m2 rv1 st1''
(st1 st1' : linker N cores_S) cd st2  
(valid : sm_valid mu m1 m2)
(hlt1 : LinkerSem.halted0 st1 = Some rv1)
(pop1 : popCore st1 = Some st1'')
(aft1 : LinkerSem.after_external (Some rv1) st1'' = Some st1')
(inv : R cd mu st1 m1 st2 m2).

Lemma hlt2 : exists rv2, LinkerSem.halted0 st2 = Some rv2.
Proof.
case: (R_inv inv)=> pf []mu_top []mus []mu_eq.
move=> []pf2 hdinv tlinv.
move: hlt1; rewrite /LinkerSem.halted0=> hlt10.
case: (core_halted (sims (Core.i (peekCore st1)))
       _ _ _ _ _ _ (head_match hdinv) hlt10)
       => rv2 []inj12 []vinj []vdefs []hlt2 extends.
exists rv2.
set T := C \o cores_T.
set P := fun ix (x : T ix) => 
  halted (coreSem (cores_T ix)) x = Some rv2.
change (P (Core.i (peekCore st2)) (Core.c (peekCore st2))).
apply: (cast_indnatdep' (j := Core.i (peekCore st1)))=> // H.
rewrite /P; move: hlt2; rewrite /= /RC.halted /= => <-. 
f_equal.
f_equal.
f_equal.
f_equal.
by apply: proof_irr.
Qed.

Lemma pop2 : exists st2'', popCore st2 = Some st2''.
Proof.
move: pop1; case/popCoreE=> pf []inCtx1 st1''_eq.
have inCtx2: inContext st2.
  by apply: (R_inContext inv inCtx1).
have pf': wf_callStack (STACK.pop (CallStack.callStack st2)).
  apply: inContext_wf=> //.
  by apply: CallStack.callStack_wf.
exists (updStack st2 
  (CallStack.mk (STACK.pop (CallStack.callStack st2)) pf')).
by apply: popCoreI.
Qed.

Lemma aft2 : 
  exists rv2 st2'' (st2' : linker N cores_T) cd' mu', 
  [/\ LinkerSem.halted0 st2 = Some rv2
    , inContext st2
    , popCore st2 = Some st2''
    , LinkerSem.after_external (Some rv2) st2'' = Some st2'
    & R cd' mu' st1' m1 st2' m2].
Proof.
case: (R_inv inv)=> pf []mu_top []mus []mu_eq.
move=> []pf_hd hdinv tlinv.
move: hlt1; rewrite /LinkerSem.halted0=> hlt10.
case: (core_halted (sims (Core.i (peekCore st1)))
       _ _ _ _ _ _ (head_match hdinv) hlt10)
       => rv2 []inj12 []vinj []rv_defs []hlt2 extends. 
exists rv2.
case: pop2=> st2'' pop2.

case: (LinkerSem.after_externalE _ _ aft1)=> fntbl []hd1 []hd1' []tl1.
move=> []pf1 []pf2 []e1 []st1''_eq st1'_eq aft1'; exists st2''.
rewrite /s1 /s2 in tlinv.

have [hd2 [tl2 [pf20 st2''_eq]]]:
  exists hd2 tl2 pf2,
  st2'' = {| fn_tbl := fntbl; stack := CallStack.mk (hd2::tl2) pf2 |}.
{ case: (popCoreE _ pop2)=> wf_pf []inCtx2 st2''_eq.
  move: wf_pf st2''_eq; rewrite /updStack.
  case: (STACK.pop (CallStack.callStack st2))=> // x0 xs wf_pf ->.
  exists x0,xs,wf_pf; f_equal=> //; rewrite -(R_fntbl inv).
  by case: (popCoreE _ pop1)=> ? []_; rewrite st1''_eq; case. }

rewrite st2''_eq.

have [mu0 [mus' mus_eq]]:
  exists mu0 mus',
  mus = [:: mu0 & mus'].
{ clear - pop1 pop2 tlinv; case: mus pop1 pop2 tlinv.
  case/popCoreE=> []wf_pf1 []_ eq1; case/popCoreE=> []wf_pf2 []_ eq2.
  move: wf_pf1 eq1; case: (STACK.pop (CallStack.callStack st1))=> // x0 xs ? ?.
  move: wf_pf2 eq2; case: (STACK.pop (CallStack.callStack st2))=> // y0 ys ? ?.
  by case.
  by move=> mu0 mus' ? ? ?; exists mu0,mus'. }

case: (tlinv)=> allrelinv frameall.
rewrite mus_eq /tail_inv in tlinv.
case: tlinv=> allinv tlinv; move: tlinv=> /=.
case: mu0 mus_eq allinv=> /= mu0 m10 m20 mu0_val mus_eq []all0 allinv.

simpl in frameall.
case: (popCoreE _ pop1)=> pf_wf1 []ctx1.
rewrite /updStack st1''_eq; case=> fntbleq1 eq1; rewrite -eq1 in frameall|-*.
case: (popCoreE _ pop2)=> pf_wf2 []ctx2.
rewrite /updStack st2''_eq; case=> fntbleq2 eq2; rewrite -eq2 in frameall|-*.
move {eq1 eq2}.
case; case=> pf0 []cd0 []x0 []sig01 []vals01 []e0 []sig02 []vals02.
move=> fr0 frametail.

move: (frame_inj0 fr0)=> inj0.
move: (frame_match fr0)=> mtch0.
move: (frame_at1 fr0)=> at01.
move: (frame_at2 fr0)=> at02.
move: (frame_vinj fr0)=> vinj0.
move: (frame_fwd1 fr0)=> fwd1.
move: (frame_fwd2 fr0)=> fwd2.
move: (frame_unch1 fr0)=> unch1.
move: (frame_unch2 fr0)=> unch2.

have at02':
  at_external (coreSem (cores_T (Core.i hd1)))
    (cast'' pf0 (Core.c hd2)) = Some (e0,sig02,vals02).
{ by rewrite /= -at02; f_equal. }

(* nu = leak-out(mu0) -- mu0 is callee *)

set pubSrc' := fun b => 
  locBlocksSrc mu0 b && REACH m10 (exportedSrc mu0 vals01) b.
set pubTgt' := fun b => 
  locBlocksTgt mu0 b && REACH m20 (exportedTgt mu0 vals02) b.
set nu := replace_locals mu0 pubSrc' pubTgt'.

have mu0_wd: SM_wd mu0.
{ by apply: Inj_wd. }

have vinj0': Forall2 (val_inject (as_inj mu0)) vals01 vals02.
{ by apply: (forall_vals_inject_restrictD _ _ _ _ vinj0). }

have [nu_wd [nu_valid0 [nu_inj0 nu_vinj]]]:
  SM_wd nu
  /\ sm_valid nu m10 m20 
  /\ Mem.inject (as_inj nu) m10 m20 
  /\ Forall2 (val_inject (as_inj nu)) vals01 vals02.
{ by apply: (eff_after_check1 
  _ mu0_wd 
  _ _ mu0_val
  inj0 
  _ _ vinj0' 
  pubSrc' erefl
  pubTgt' erefl 
  nu erefl). }

(* nu' = reestablish nu w/r/t mu_top *)

set nu' := reestablish nu mu_top.

have restrict_mu_top_nu:
  restrict (as_inj mu_top) (DomSrc nu) = as_inj nu.
{ rewrite /restrict /as_inj /join; extensionality b.
  move: (head_rel hdinv); rewrite mus_eq /= => [][]. 
  case=> /= incr_mu0_top sep_mu0_top disj_mu0_top _ _.
  case e: (DomSrc nu b)=> //.
  case eOf_nu: (extern_of nu b)=> [[x' y']|].  
  rewrite /nu replace_locals_extern in eOf_nu.
  case eOf_top: (extern_of mu_top b)=> [[x'' y'']|].
  case: incr_mu0_top; rewrite /as_inj /join.
  by move/(_ b x' y'); rewrite eOf_nu eOf_top=> H1 H2; apply: H1.
  case: incr_mu0_top; rewrite /as_inj /join; move/(_ b x' y').
  by rewrite eOf_nu eOf_top=> H1 H2; apply: H1.
  rewrite /nu replace_locals_extern in eOf_nu.
  rewrite /nu replace_locals_DomSrc in e.
  case eOf_top: (extern_of mu_top b)=> [[x' y']|].
  case lOf_nu: (local_of nu b)=> [[x'' y'']|].
  case: incr_mu0_top=> inj_incr []H1 H2.  
  move: (inj_incr b x'' y''); rewrite /as_inj /join.
  rewrite /nu replace_locals_local in lOf_nu.
  by rewrite eOf_nu eOf_top lOf_nu; apply.
  case: sep_mu0_top; move/(_ b x' y').
  rewrite /nu replace_locals_local in lOf_nu.
  rewrite /as_inj /join eOf_nu lOf_nu eOf_top; case=> //.
  by rewrite e.
  case: incr_mu0_top=> inj_incr []H1 H2.
  case lOf_nu: (local_of nu b)=> [[x' y']|].
  rewrite /nu replace_locals_local in lOf_nu.
  case lOf_top: (local_of mu_top b)=> [[x'' y'']|].
  move: (inj_incr b x' y'); rewrite /as_inj /join.
  by rewrite lOf_nu lOf_top eOf_nu eOf_top; apply.
  move: (inj_incr b x' y'); rewrite /as_inj /join.
  by rewrite lOf_nu lOf_top eOf_nu eOf_top; move/(_ erefl).
  rewrite /nu replace_locals_local in lOf_nu.
  case lOf_top: (local_of mu_top b)=> //[[x' y']].
  case: (local_locBlocks _ (Inj_wd _) _ _ _ lOf_top).
  case: sep_mu0_top; move/(_ b x' y').
  rewrite /as_inj /join eOf_nu lOf_nu eOf_top lOf_top; case=> //.
  by rewrite e. 
  case eOf_nu: (extern_of nu b)=> [[x' y']|].
  rewrite /nu replace_locals_extern in eOf_nu.
  case: (extern_DomRng' _ (Inj_wd _) _ _ _ eOf_nu).
  move=> _ []_ []_ []_ []_ []_ []dSrc _.
  by rewrite /nu replace_locals_DomSrc dSrc in e.
  case lOf_nu: (local_of nu b)=> //[[x' y']].
  rewrite /nu replace_locals_local in lOf_nu.
  case: (local_DomRng _ (Inj_wd _) _ _ _ lOf_nu)=> H1 _.  
  by rewrite /DomSrc /nu replace_locals_locBlocksSrc H1 /= in e. }

have asInj_nu'_mu_top: as_inj nu' = as_inj mu_top.
{ by apply: reestablish_as_inj. }

have nu'_vinj: val_inject (as_inj nu') rv1 rv2.
{ rewrite asInj_nu'_mu_top.
  by apply: (val_inject_restrictD _ _ _ _ vinj). }

move: (head_rel hdinv); rewrite mus_eq /= => [][].  
case=> /= incr0_top sep0_top disj0_top _ _.

have extsrc_nu_top b: extBlocksSrc nu b -> DomSrc mu_top b.
{ rewrite /nu replace_locals_extBlocksSrc=> H1.
  case: incr0_top=> _ []; move/(_ b); rewrite /DomSrc H1.
  by move=> H2 _; apply: H2; apply/orP; right. }

have exttgt_nu_top b: extBlocksTgt nu b -> DomTgt mu_top b.
{ rewrite /nu replace_locals_extBlocksTgt=> H1.
  case: incr0_top=> _ [] _; move/(_ b); rewrite /DomTgt H1.
  by apply; apply/orP; right. }

have nu_nu'_eincr: extern_incr nu nu'.
{ apply: reestablish_extern_incr=> //; first by apply: Inj_wd. }

have locsrc_nu_top b: locBlocksSrc nu b -> DomSrc mu_top b.
{ rewrite /nu replace_locals_locBlocksSrc=> H1.
  case: incr0_top=> _ []; move/(_ b); rewrite /DomSrc H1.
  by move=> H2 _; apply: H2. }

have loctgt_nu_top b: locBlocksTgt nu b -> DomTgt mu_top b.
{ rewrite /nu replace_locals_locBlocksTgt=> H1.
  by case: incr0_top=> _ [] _; move/(_ b); rewrite /DomTgt H1; apply. }

have nu_nu'_sep: sm_inject_separated nu nu' m10 m20.
{ apply: reestablish_sm_injsep=> //; first by apply: Inj_wd.
  by apply: sm_inject_separated_replace_locals. }

have nu'_wd: SM_wd nu'.
{ apply: reestablish_wd=> //; first by apply: Inj_wd.
  case: sep0_top=> H1 _; rewrite /nu. 
  rewrite replace_locals_DomSrc replace_locals_DomTgt. 
  by rewrite replace_locals_as_inj. }

have nu'_valid: sm_valid nu' m1 m2.
{ apply: reestablish_sm_valid=> //.
  by apply: Inj_wd.
  by apply: (head_valid hdinv). }

have nu'_inj: Mem.inject (as_inj nu') m1 m2.
{ by rewrite /nu' reestablish_as_inj. }

set frgnSrc' := fun b => 
  [&& DomSrc nu' b, ~~locBlocksSrc nu' b
    & REACH m1 (exportedSrc nu' [:: rv1]) b].
set frgnTgt' := fun b => 
  [&& DomTgt nu' b, ~~locBlocksTgt nu' b
    & REACH m2 (exportedTgt nu' [:: rv2]) b].

(* mu' = leak-in(nu') *)

set mu' := replace_externs nu' frgnSrc' frgnTgt'.

have [hd2' [pf_eq22' [pf_eq12' [cd' [aft2' mtch12']]]]]:
  exists hd2' (pf_eq22' : Core.i hd2 = Core.i hd2') 
              (pf_eq12' : Core.i hd1' = Core.i hd2')
         cd',
  [/\ after_external (coreSem (cores_T (Core.i hd2)))
        (Some rv2) (Core.c hd2) 
      = Some (cast'' pf_eq22' (Core.c hd2'))
    & match_state (sims (Core.i hd1')) cd' mu' 
      (Core.c hd1') m1 (cast'' pf_eq12' (Core.c hd2')) m2].
{ case: (popCoreE _ pop2)=> wf_pf []inCtx2 st2''_eq'.
  rewrite st2''_eq' in st2''_eq.
  rewrite /updStack in st2''_eq; case: st2''_eq=> fntbl_eq pop2_eq'.
  move: (@eff_after_external 
  _ _ _ _ _ _ _ _ 
  _ _  
  (sims (Core.i hd1))
  _ _ _ _ _ _ _ _ _ _ _ _
  inj0 mtch0 at01 at02' vinj0

  pubSrc' erefl pubTgt' erefl nu erefl

  nu' rv1 m1 rv2 m2

  nu_nu'_eincr nu_nu'_sep
  nu'_wd nu'_valid nu'_inj nu'_vinj
  fwd1 fwd2

  frgnSrc' erefl frgnTgt' erefl mu' erefl

  unch1 unch2).
  case=> cd' []c0' []d0' []aft1'' []aft2'' mtch12'.
  exists (Core.mk _ cores_T (Core.i hd1) d0'),(sym_eq pf0),(sym_eq e1)=> /=.
  exists (cast (fun ix => core_data (sims ix)) e1 cd'); split=> //.
  
  move: aft2''.
  set T := C \o cores_T.  
  set P := fun ix (x : T ix) (y : T ix) => 
    after_external (coreSem (cores_T ix)) (Some rv2) x = Some y.
  change (P (Core.i hd1) (cast T (sym_eq pf0) (Core.c hd2)) d0'
       -> P (Core.i hd2) (Core.c hd2) (cast T (sym_eq (sym_eq pf0)) d0')).
  have ->: sym_eq (sym_eq pf0) = pf0 by apply: proof_irr.
  by apply: cast_indnatdep2.

  move: mtch12'.
  have ->: sym_eq (sym_eq e1) = e1 by apply: proof_irr.
  rewrite aft1' in aft1''; case: aft1''=> <-.
  set T := (fun ix => core_data (sims ix)).
  set U := C \o cores_S.
  set V := C \o cores_T.
  set P := fun ix (x : T ix) (y : U ix) (z : V ix) => 
    match_state (sims ix) x mu' y m1 z m2.
  change (P (Core.i hd1) cd' (cast U (sym_eq e1) (Core.c hd1')) d0'
       -> P (Core.i hd1') (cast T e1 cd') (Core.c hd1') (cast V e1 d0')).
  by apply: cast_indnatdep33. }

set st2' := {| fn_tbl := fntbl; stack := CallStack.mk (hd2'::tl2) pf20 |}.

exists st2'. 
exists (existT _ (Core.i hd1') cd'). 
exists mu'.

split=> //.

move: hlt2.

set T := C \o cores_T.
set P := fun ix (x : T ix) => 
 halted (coreSem (cores_T ix)) x = Some rv2.
change (P (Core.i (peekCore st1)) (cast T (sym_eq pf) (Core.c (d inv)))
     -> P (Core.i (peekCore st2)) (Core.c (peekCore st2))).
by apply: cast_indnatdep'.

by rewrite pop2 st2''_eq.

{ rewrite /st2'; move: aft2'.
rewrite /LinkerSem.after_external /= => -> /=. 
rewrite /SeqStack.updStack /Core.upd.
do 3 f_equal; first by move=> ? ?; case=> -> ->.
f_equal; clear - hd2' pf_eq22'; destruct hd2'=> /=.
by move: pf_eq22'=> /= pf; subst; f_equal.
by apply: proof_irr. }

apply: Build_R=> /=.
rewrite st1'_eq; exists pf_eq12'.

have mu'_wd : SM_wd mu'.
{ case: (eff_after_check2 nu' rv1 m1 m2 rv2 nu'_inj nu'_vinj
        frgnSrc' erefl frgnTgt' erefl mu' erefl nu'_wd nu'_valid)=> H1 H2.
  by apply: H1. }

have mu'_valid : sm_valid mu' m1 m2.
{ case: (eff_after_check2 nu' rv1 m1 m2 rv2 nu'_inj nu'_vinj
        frgnSrc' erefl frgnTgt' erefl mu' erefl nu'_wd nu'_valid)=> H1 H2.
  by apply: H2. }

have mu0_mu'_inject_incr : inject_incr (as_inj mu0) (as_inj mu').
{ by apply: (eff_after_check4 mu0 pubSrc' pubTgt' nu erefl nu' nu_nu'_eincr
            mu' frgnSrc' frgnTgt' erefl nu'_wd). }

have mu0_in: In (Inj.mu mu0) 
                [seq (Inj.mu \o frame_mu0) x | x <- mus].
{ by rewrite mus_eq /=; left. }

have mu0_mu'_incr : incr mu0 mu'.
{ split=> //; split=> b0.
  rewrite /DomSrc; case/orP; rewrite /mu' replace_externs_locBlocksSrc /nu'.
  by rewrite reestablish_locBlocksSrc /nu replace_locals_locBlocksSrc=> ->.
  rewrite /mu' replace_externs_extBlocksSrc /nu'.
  rewrite reestablish_extBlocksSrc /nu replace_locals_locBlocksSrc=> E.
  have lN: locBlocksSrc mu0 b0 = false.
  { by move: (extBlocksSrc_locBlocksSrc _ (Inj_wd _) _ E). }
  rewrite lN; apply/orP; right.
  move: (head_rel hdinv); rewrite mus_eq /=; case; case=> /=; case.
  move=> _; case; move/(_ b0)=> H _ _ _ _ _; apply: H.
  by rewrite /DomSrc E; apply/orP; right.

  rewrite /DomTgt; case/orP; rewrite /mu' replace_externs_locBlocksTgt /nu'.
  by rewrite reestablish_locBlocksTgt /nu replace_locals_locBlocksTgt=> ->.
  rewrite /mu' replace_externs_extBlocksTgt /nu'.
  rewrite reestablish_extBlocksTgt /nu replace_locals_locBlocksTgt=> E.
  have lN: locBlocksTgt mu0 b0 = false.
  { by move: (extBlocksTgt_locBlocksTgt _ (Inj_wd _) _ E). }
  rewrite lN; apply/orP; right.
  move: (head_rel hdinv); rewrite mus_eq /=; case; case=> /=; case.
  move=> _; case=> _; move/(_ b0)=> H _ _ _ _; apply: H.
  by rewrite /DomTgt E; apply/orP; right. }

have as_inj_mu'_mu_top : as_inj mu' = as_inj mu_top.
{ by rewrite replace_externs_as_inj asInj_nu'_mu_top. }

have DomSrc_mu'_mu_top : DomSrc mu' = DomSrc mu_top.
{ by rewrite /mu' replace_externs_DomSrc reestablish_DomSrc. }

have DomTgt_mu'_mu_top : DomTgt mu' = DomTgt mu_top.
{ by rewrite /mu' replace_externs_DomTgt reestablish_DomTgt. }

have mu_top_mu'_incr : incr mu_top mu'.
{ split; first by rewrite as_inj_mu'_mu_top; apply: inject_incr_refl.
  split; first by rewrite DomSrc_mu'_mu_top.
  by rewrite DomTgt_mu'_mu_top. }

have locBlocksSrc_mu'_eq : locBlocksSrc mu' = locBlocksSrc mu0.
{ rewrite /mu' replace_externs_locBlocksSrc /nu'.
  by rewrite reestablish_locBlocksSrc /nu replace_locals_locBlocksSrc. }

have locBlocksTgt_mu'_eq : locBlocksTgt mu' = locBlocksTgt mu0.
{ rewrite /mu' replace_externs_locBlocksTgt /nu'.
  by rewrite reestablish_locBlocksTgt /nu replace_locals_locBlocksTgt. }

have extBlocksSrc_mu'_eq : 
  extBlocksSrc mu' 
= (fun b => if locBlocksSrc mu0 b then false else DomSrc mu_top b).
{ rewrite /mu' replace_externs_extBlocksSrc /nu'.
  by rewrite reestablish_extBlocksSrc /nu replace_locals_locBlocksSrc. }

have extBlocksTgt_mu'_eq : 
  extBlocksTgt mu' 
= (fun b => if locBlocksTgt mu0 b then false else DomTgt mu_top b).
{ rewrite /mu' replace_externs_extBlocksTgt /nu'.
  by rewrite reestablish_extBlocksTgt /nu replace_locals_locBlocksTgt. }

have frgnBlocksSrc_mu'_eq : frgnBlocksSrc mu' = frgnSrc'.
{ by rewrite /mu' replace_externs_frgnBlocksSrc. }

have frgnBlocksTgt_mu'_eq : frgnBlocksTgt mu' = frgnTgt'.
{ by rewrite /mu' replace_externs_frgnBlocksTgt. }

have subFS: {subset frgnBlocksSrc mu0 <= frgnSrc'}.
{ rewrite /frgnSrc' /nu'=> b0; rewrite /in_mem /= => H.
  rewrite /DomSrc reestablish_locBlocksSrc /nu.
  rewrite replace_locals_locBlocksSrc.
  rewrite reestablish_extBlocksSrc.
  rewrite replace_locals_locBlocksSrc.
  have lN: locBlocksSrc mu0 b0 = false.
  { by move: (extBlocksSrc_locBlocksSrc _ (Inj_wd _) _ (frgnsrc_sub_extsrc H)). }
  rewrite lN /=.
  rewrite /exportedSrc sharedSrc_iff_frgnpub.
  rewrite reestablish_frgnBlocksSrc.
  rewrite replace_locals_frgnBlocksSrc.
  have pub_eq: 
    pubBlocksSrc (reestablish (replace_locals mu0 pubSrc' pubTgt') mu_top)
    = pubBlocksSrc (replace_locals mu0 pubSrc' pubTgt').
  { by rewrite reestablish_pubBlocksSrc. }
  rewrite pub_eq replace_locals_pubBlocksSrc; apply/andP; split.
  case: incr0_top=> _; case; move/(_ b0)=> H2 _.
  apply: H2; rewrite /DomSrc.
  move: (frgnsrc_sub_extsrc H). 
  by rewrite /in_mem /= => ->; apply/orP; right.
  by apply: REACH_nil; apply/orP; right; apply/orP; left.
  by apply: nu'_wd. }

have subFT: {subset frgnBlocksTgt mu0 <= frgnTgt'}.
{ rewrite /frgnTgt' /nu'=> b0; rewrite /in_mem /= => H.
  rewrite /DomTgt reestablish_locBlocksTgt /nu.
  rewrite replace_locals_locBlocksTgt.
  rewrite reestablish_extBlocksTgt.
  rewrite replace_locals_locBlocksTgt.
  have lN: locBlocksTgt mu0 b0 = false.
  { by move: (extBlocksTgt_locBlocksTgt _ (Inj_wd _) _ (frgntgt_sub_exttgt H)). }
  rewrite lN /=.
  rewrite /exportedTgt /sharedTgt. 
  rewrite reestablish_frgnBlocksTgt replace_locals_frgnBlocksTgt.
  have pub_eq: 
    pubBlocksTgt (reestablish (replace_locals mu0 pubSrc' pubTgt') mu_top)
    = pubBlocksTgt (replace_locals mu0 pubSrc' pubTgt').
  { by rewrite reestablish_pubBlocksTgt. }
  rewrite pub_eq replace_locals_pubBlocksTgt; apply/andP; split.
  case: incr0_top=> _; case; move/(_ b0)=> _ H2.
  apply: H2; rewrite /DomTgt.
  move: (frgntgt_sub_exttgt H). 
  by rewrite /in_mem /= => ->; apply/orP; right.
  by apply: REACH_nil; apply/orP; right; apply/orP; left. }

have shrdS_mu0_mu': {subset sharedSrc mu0 <= sharedSrc mu'}.
{ move=> b0; rewrite !sharedSrc_iff_frgnpub=> //; case/orP=> F.
  apply/orP; left; rewrite frgnBlocksSrc_mu'_eq.
  by apply: subFS.
  rewrite /mu' replace_externs_pubBlocksSrc /nu'.
  rewrite reestablish_pubBlocksSrc /nu replace_locals_pubBlocksSrc.
  apply/orP; right; rewrite /pubSrc'; apply/andP; split.
  by apply: pubsrc_sub_locsrc.
  apply: REACH_nil; apply/orP; right; rewrite sharedSrc_iff_frgnpub.
  by apply/orP; right.
  by apply: Inj_wd. }

have shrdT_mu0_mu': {subset sharedTgt mu0 <= sharedTgt mu'}.
{ move=> b0; rewrite /sharedTgt; case/orP=> F.
  apply/orP; left; rewrite frgnBlocksTgt_mu'_eq.
  by apply: subFT.
  rewrite /mu' replace_externs_pubBlocksTgt /nu'.
  rewrite reestablish_pubBlocksTgt /nu replace_locals_pubBlocksTgt.
  apply/orP; right; rewrite /pubTgt'; apply/andP; split.
  by apply: pubtgt_sub_loctgt.
  apply: REACH_nil; apply/orP; right; rewrite /sharedTgt.
  by apply/orP; right. }

have mu0_mu'_sep : sm_inject_separated mu0 mu' m10 m20.
{ by apply: (eff_after_check5 mu0 pubSrc' pubTgt' nu erefl nu'
            mu' frgnSrc' frgnTgt' erefl m10 m20 nu_nu'_sep). }

exists (Inj.mk mu'_wd),(tl mus).

move=> /=; split=> //.

set mu0_pkg := {| frame_mu0 := mu0; frame_m10 := m10; frame_m20 := m20;
                  frame_val := mu0_val |}.

{(* head_inv *)
exists erefl.

move: (head_rel hdinv); rewrite mus_eq /= => rel.
case: rel; case=> /= incr1 sep1 disj1 rc rel. 

have vinj'': 
 Forall2 (val_inject (restrict (as_inj mu_top) (vis mu_top))) 
 [:: rv1] [:: rv2].
{ by apply: Forall2_cons. }

have vinj''': 
 val_list_inject (restrict (as_inj mu_top) (vis mu_top)) 
 [:: rv1] [:: rv2].
{ by apply: val_cons_inject. }

have eq: sharedSrc (reestablish nu mu_top) = sharedSrc nu.
{ rewrite !sharedSrc_iff_frgnpub=> //; extensionality b0.
  by rewrite reestablish_frgnBlocksSrc reestablish_pubBlocksSrc. }

apply: Build_head_inv=> //.
{(*All (rel_inv_pred ...) mus'*)
  move {mus_eq allinv frametail rc}.
  elim: mus' all0 rel=> // a mus' IH.
  move=> /= []H1 H2 []H3 H4; split; last by apply: IH.
  case: H3=> incr3 sep3 disj3 rel3.

  have frgnSrc'_loc_pub: 
    {subset [predI frgnSrc' & locBlocksSrc a] <= pubBlocksSrc a}.
  { rewrite /frgnSrc' /nu' /exportedSrc eq.
    move=> b; rewrite /in_mem /= /in_mem /=; case/andP=> XX YY.
    case: disj3=> A B C D E.
    case: {XX}(andP XX)=> H5; case/andP=> H6 H7.
    rewrite reestablish_locBlocksSrc replace_locals_locBlocksSrc in H6.
    rewrite reestablish_DomSrc in H5=> //; case: (orP H5)=> H8.
    by move: A; move/DisjointP; move/(_ b); rewrite YY H8; case.
    have V: {subset [predI REACH m1 (vis mu0) & locBlocksSrc a]
            <= pubBlocksSrc a}.
    { by case: H1. }
    have [U|U]: b \in frgnBlocksSrc mu_top 
             \/ b \in REACH m1 (vis mu0).
    { case fS: (_ \in frgnBlocksSrc _); first by left.
      move: H7; case/REACH_split=> H9.
      suff: vis mu_top b. 
      case/orP; first by rewrite extBlocksSrc_locBlocksSrc=> //; apply: Inj_wd.
      by move=> fS'; move: fS' fS; rewrite /= /in_mem /= => ->.
      move: (head_match hdinv)=> mtch; apply match_visible in mtch.
      apply: mtch; apply: (REACH_mono (getBlocks [:: rv1]))=> //.
      move=> b0 get; case: (getBlocks_inject _ _ _ vinj'' _ get)=> x []y [].    
      case/restrictD_Some=> H; case/orP; first by rewrite /vis=> ->.
      by rewrite /vis=> -> _; apply/orP; right.
      right; apply: (REACH_mono (sharedSrc nu))=> // b0.
      rewrite sharedSrc_iff_frgnpub=> //; rewrite replace_locals_frgnBlocksSrc.
      case/orP=> H10; apply/orP; first by right; rewrite H10.
      move: H10; rewrite replace_locals_pubBlocksSrc /pubSrc'. 
      by case/andP=> -> _; left. }
    by apply: C; apply/andP; split.
    by apply: V; apply/andP; split. }

  apply: Build_rel_inv=> //; first by apply: (incr_trans incr3).
  { case: mu_top_mu'_incr=> AA []BB CC; case: sep3=> XX []YY ZZ; split.
  move=> b1 b2 d1 asInj asInj'.  
  case e: (as_inj mu_top b1)=> [[x y]|].
  move: (AA _ _ _ e); rewrite asInj'; case=> -> _.
  by apply: (XX _ _ _ asInj e).
  by rewrite as_inj_mu'_mu_top in asInj'; rewrite asInj' in e.
  by rewrite DomSrc_mu'_mu_top DomTgt_mu'_mu_top; split. }

  {(*disjinv a mu'*) 
  case: H1=> _ _ disj4 rc4.
  case: disj4=> X Y Z W U; apply: Build_disjinv.
  by rewrite locBlocksSrc_mu'_eq.
  by rewrite locBlocksTgt_mu'_eq.
  by rewrite frgnBlocksSrc_mu'_eq; apply: frgnSrc'_loc_pub. 

  move=> b1 b2 d1 fOf.
  case: (foreign_DomRng _ mu'_wd _ _ _ fOf)=> _[]_ []_ []_.
  rewrite frgnBlocksSrc_mu'_eq frgnBlocksTgt_mu'_eq; case=> AA []BB _.

  have aOf: as_inj mu_top b1 = Some (b2,d1).
  { move: fOf; rewrite /mu' replace_externs_foreign.
    case xx: (frgnSrc' _)=> //.
    rewrite /nu' reestablish_extern_of.
    case yy: (locBlocksSrc _ _)=> // H. }

  rewrite /in_mem /=; case/orP=> L.

  { have pA: pubBlocksSrc a b1.
    { apply: frgnSrc'_loc_pub; rewrite /in_mem /= /in_mem /=; apply/andP.
      by split. }
    case: (pubSrcAx _ _ _ pA); first by apply: Inj_wd.
    move=> x []z []lOf pT.
    case: disj3=> _ _ _ _ Catop.
    case e: (pub_of a b1)=> [[? ?]|].
    move: (pub_in_local _ _ _ _ e); rewrite lOf; case=> <- <-.
    rewrite /Consistent /consistent /= in Catop.
    move: (Catop b1 x b2 z d1).
    rewrite (local_in_all _ _ _ _ _ lOf).
    by case/(_ erefl aOf)=> -> ->.
    by apply: Inj_wd.
    move: e; rewrite /pub_of.
    by case: (Inj.mu a) pA lOf=> /= ? ? pubSrc ? lOf ? ? ? ? ? -> ->. }

  { suff e: pubBlocksSrc a b1. 
    move: (e); move/pubSrcAx; case/(_ (Inj_wd _))=> x []y []lOf pT. 
    { have asInj: as_inj a b1 = Some (x,y) 
        by apply: local_in_all=> //; apply: Inj_wd.
      case: incr3; move/(_ _ _ _ asInj)=> asInj' _.
      rewrite asInj' in aOf; case: aOf=> <- <-.
      clear - lOf e; case: a lOf e=> ???? /=.
      by rewrite /pub_of; case f: (Inj.mu _)=> //= g ->. }
    apply: frgnSrc'_loc_pub; apply/andP; split=> //.
    have aOf0: as_inj a b1 = Some (b2,d1).
    { case e: (as_inj a b1)=> [[x y]|].
      by case: incr3; move/(_ _ _ _ e); rewrite aOf; case=> <- <-.
      case: sep3; case/(_ b1 b2 d1 e aOf)=> _ D _.
      move: D; rewrite /DomTgt L; discriminate. }
    by rewrite /= /in_mem /= (@as_inj_locBlocks a _ _ _ (Inj_wd _) aOf0). }

  move=> b1 b2 b2' d1 d1' AA BB.
  rewrite as_inj_mu'_mu_top in BB.
  case: disj3=> _ _ _ _ Catop.
  by apply: (Catop b1 b2 b2' d1 d1' AA BB). }(*END disjinv a mu'*)

  {(*sub REACH ...*)
    move=> b; case/andP=> /= A B.
    case: H1=> incr0 sep0 disj0 sub0.
    have C: b \in vis mu' by apply match_visible in mtch12'; apply: mtch12'.
    case: (orP C)=> D.
    case: disj0; move/DisjointP; move/(_ b)=> E _ _ _.
    move: B E; rewrite /in_mem /= => ->.
    by move: D; rewrite locBlocksSrc_mu'_eq=> ->; case.
    rewrite replace_externs_frgnBlocksSrc in D.
    by apply: frgnSrc'_loc_pub; apply/andP; split. }
  }(*END All (rel_inv_pred ...) mus'*)

{(*vis_inv*) 
apply: Build_vis_inv.
rewrite /vis /=.
rewrite /mu'.
rewrite replace_externs_locBlocksSrc replace_externs_frgnBlocksSrc.
have eqL: locBlocksSrc nu' = locBlocksSrc mu0.
{ by rewrite /nu' reestablish_locBlocksSrc /nu replace_locals_locBlocksSrc. }
rewrite eqL.
have subF: {subset frgnBlocksSrc mu0 <= frgnSrc'}.
{ rewrite /frgnSrc' /nu'=> b; rewrite /in_mem /= => H.
  rewrite /DomSrc reestablish_locBlocksSrc /nu.
  rewrite replace_locals_locBlocksSrc.
  rewrite reestablish_extBlocksSrc.
  rewrite replace_locals_locBlocksSrc.
  have lN: locBlocksSrc mu0 b = false.
  { by move: (extBlocksSrc_locBlocksSrc _ (Inj_wd _) _ (frgnsrc_sub_extsrc H)). }
  rewrite lN /=.
  rewrite /exportedSrc sharedSrc_iff_frgnpub.
  rewrite reestablish_frgnBlocksSrc.
  rewrite replace_locals_frgnBlocksSrc.
  have pub_eq: 
    pubBlocksSrc (reestablish (replace_locals mu0 pubSrc' pubTgt') mu_top)
    = pubBlocksSrc (replace_locals mu0 pubSrc' pubTgt').
  { by rewrite reestablish_pubBlocksSrc. }
  rewrite pub_eq replace_locals_pubBlocksSrc; apply/andP; split.
  case: incr0_top=> _; case; move/(_ b)=> H2 _.
  apply: H2; rewrite /DomSrc.
  move: (frgnsrc_sub_extsrc H). 
  by rewrite /in_mem /= => ->; apply/orP; right.
  by apply: REACH_nil; apply/orP; right; apply/orP; left.
  by apply: nu'_wd. }
{(*{subset RC.reach_basis ...}*)
  move: aft1'=> /= aft1'.
  move: (RC.after_external_rc_basis (ge (cores_S (Core.i hd1))) aft1').
  move=> eq_hd1' b; rewrite /in_mem /= => H.
  have eq_hd1'': 
    RC.reach_basis (ge (cores_S (Core.i hd1'))) (Core.c hd1')
    = (fun b => 
         getBlocks [:: rv1] b
      || RC.reach_basis (ge (cores_S (Core.i hd1))) (Core.c hd1) b).
  { move: eq_hd1'. 
    set T := C \o cores_S.
    set P := fun ix (x : T ix) => 
               RC.reach_basis (ge (cores_S ix)) x 
           = (fun b0 => 
              getBlocks [:: rv1] b0
              || RC.reach_basis (ge (cores_S (Core.i hd1))) (Core.c hd1) b0).
    change (P (Core.i hd1) (cast T (sym_eq e1) (Core.c hd1'))
         -> P (Core.i hd1') (Core.c hd1')).
    by apply: cast_indnatdep'. }
  have eq_hd1''': 
    RC.reach_basis my_ge (Core.c hd1') 
    = (fun b =>
         getBlocks [:: rv1] b
         || RC.reach_basis (ge (cores_S (Core.i hd1))) (Core.c hd1) b).
  { rewrite -eq_hd1'' /RC.reach_basis; extensionality b0.
    have glob_eq: isGlobalBlock my_ge b0
                = isGlobalBlock (ge (cores_S (Core.i hd1'))) b0. 
    { suff: isGlobalBlock my_ge b0 
        <-> isGlobalBlock (ge (cores_S (Core.i hd1'))) b0.
      case: (isGlobalBlock _ _)=> //.
      case: (isGlobalBlock _ _)=> //.
      case=> //.
      by move/(_ erefl).         
      case: (isGlobalBlock _ _)=> //.
      case=> //.
      by move=> _; move/(_ erefl).               
      by rewrite -isGlob_iffS. }
    by rewrite -glob_eq. }
  rewrite eq_hd1''' in H.
  case: (orP H).
  { move=> get1; case: (getBlocks_inject _ _ _ vinj'' _ get1)=> x []y [].
    case/restrictD_Some=> I J K.
    case l: (locBlocksSrc mu0 b); first by apply/orP; left.
    rewrite /frgnSrc' /exportedSrc; apply/orP; right; apply/andP; split.
    rewrite /nu' reestablish_DomSrc /DomSrc.
    by apply: (vis_sub_DomSrc J).
    rewrite /nu replace_locals_locBlocksSrc=> b0 M.
    case: incr1=> _ []; move/(_ b0)=> O _; apply: O.
    by apply/orP; left.
    apply/andP; split; first by rewrite eqL l.
    by apply: REACH_nil; apply/orP; left. }
  { move=> RB; case: (frame_vis fr0)=> vis_sub. 
    have vis0_b: vis mu0 b.
    { apply: vis_sub.
      rewrite /in_mem /=; move: RB; rewrite /RC.reach_basis.
      have glob_eq: isGlobalBlock my_ge b
                  = isGlobalBlock (ge (cores_S (Core.i hd1))) b. 
      { suff: isGlobalBlock my_ge b 
          <-> isGlobalBlock (ge (cores_S (Core.i hd1))) b.
        case: (isGlobalBlock _ _)=> //.
        case: (isGlobalBlock _ _)=> //.
        case=> //.
        by move/(_ erefl).         
        case: (isGlobalBlock _ _)=> //.
        case=> //.
        by move=> _; move/(_ erefl).               
        by rewrite -isGlob_iffS. }
      by rewrite -glob_eq. }
    { case: (orP vis0_b); first by move=> ->.
      by move=> L; apply/orP; right; apply: subF. } } 
}(*END {subset RC.reach_basis ...}*)
}(*END vis_inv*)
}(*END head_inv*)

split; first by move: allinv; rewrite mus_eq.
by rewrite mus_eq.
by rewrite st1'_eq.
Qed.

End return_lems.

Section halted_lems.

Context
(mu : Inj.t) m1 m2 rv1 
(st1 : linker N cores_S) cd st2  
(hlt1 : LinkerSem.halted st1 = Some rv1)
(inv : R cd mu st1 m1 st2 m2).

Lemma toplevel_hlt2 : exists rv2, LinkerSem.halted st2 = Some rv2.
Proof.
case: (R_inv inv)=> pf []mu_top []mus []mu_eq.
move=> []pf2 hdinv tlinv.
move: hlt1; rewrite /LinkerSem.halted. 
case inCtx1: (inContext st1)=> //=.
have inCtx2: ~~inContext st2.
{ case inCtx2: (inContext st2)=> //=.
  by move: (R_inContext' inv inCtx2); rewrite inCtx1. }
rewrite inCtx2.
case hlt0: (LinkerSem.halted0 st1)=> [rv1'|//]; case=> eq1.
by case: (hlt2 hlt0 inv)=> rv2 hlt2; exists rv2; rewrite hlt2.
Qed.

End halted_lems.

Lemma link (main : val) :
  Wholeprog_simulation_inject linker_S linker_T my_ge my_ge main.
Proof.

eapply Build_Wholeprog_simulation_inject
  with (core_data   := sig_data N (fun ix : 'I_N => (sims ix).(core_data)))
       (core_ord    := sig_ord (fun ix : 'I_N => (sims ix).(core_ord)))
       (match_state := R).

(* well_founded ord *)
{ by apply: wf_sig_ord. }

(* genvs_domain_eq *)
{ by apply: genvs_domain_eq_refl. }

{(* Case: [core_initial] *)
  move=> j c1 vals1 m1 vals2 m2 init1 inj vinj pres reach.
  move: init1. 
  rewrite /= /LinkerSem.initial_core.
  case e: main=> [//|//|//|//|b ofs].
  case f: (fun_tbl b)=> [ix|//].
  case g: (initCore _ _ _ _)=> [x|//].
  case h: (Integers.Int.eq _ _)=> //.
  case.
  move=> <-.
  case: x g=> ix1 c0 init1.

  set fS := (REACH m1 (fun b0 : block => 
    isGlobalBlock (ge (cores_S ix)) b0 || getBlocks vals1 b0)).
  set fT := (REACH m2 (fun b0 : block => 
    isGlobalBlock (ge (cores_T ix)) b0 || getBlocks vals2 b0)).

  set dS := (fun b : block => valid_block_dec m1 b).
  set dT := (fun b : block => valid_block_dec m2 b).

  exists (initial_SM dS dT fS fT j).

  Arguments core_initial : default implicits.

  move: init1; rewrite /initCore.
  case g: (core_semantics.initial_core _ _ _ _)=> [c|//].
  case=> eq1 H2. subst ix1.
  apply Eqdep_dec.inj_pair2_eq_dec in H2. subst c0.

  have valid_dec: forall m b, Mem.valid_block m b -> valid_block_dec m b.
  { by move=> m b0; rewrite /is_left; case l: (valid_block_dec m b0). }

  have valid_dec': forall m b, valid_block_dec m b -> Mem.valid_block m b.
  { by move=> m b0; rewrite /is_left; case l: (valid_block_dec m b0). }

  have main_eq: main = Vptr b Integers.Int.zero.
  { move: (Integers.Int.eq_spec ofs Integers.Int.zero).
    by rewrite e; move: h g=> /= -> h ->. }
    
  move: (core_initial (sims ix))=> H1.
  move: (H1 main vals1 c m1 j vals2  m2 dS dT).
  case=> //.

  by rewrite main_eq.

  rewrite -meminj_preserves_genv2blocks.
  rewrite -(genvs_domain_eq_match_genvs (my_ge_S ix)).
  rewrite meminj_preserves_genv2blocks.
  by [].

  { rewrite /dS /dT /mapped=> ? ? ? eq; split.
    apply Mem.valid_block_inject_1 with (m1:=m1) (m2:=m2) in eq=> //.
    by apply: valid_dec.
    apply Mem.valid_block_inject_2 with (m1:=m1) (m2:=m2) in eq=> //. 
    by apply: valid_dec. }

  { move=> b0 R; suff: Mem.valid_block m2 b0.
    by apply: valid_dec.
    apply: reach; apply: (REACH_mono (fun b' : block =>
      isGlobalBlock (ge (cores_T ix)) b' || getBlocks vals2 b'))=> //.
    move=> b1; case/orP; first by rewrite -isGlob_iffT=> ->.
    by move=> ->; apply/orP; right. }

  { by apply: valid_dec'. }

  { by apply: valid_dec'. }

  move=> cd []c2 []init2 mtch12.

  exists (existT _ ix cd).
  exists (mkLinker fun_tbl (CallStack.singl (Core.mk _ _ ix c2))).
  
  split.

  rewrite /as_inj /join /=; extensionality b0.
  by case: (j b0)=> [[? ?]//|//].

  simpl in init2.

  rewrite -main_eq init2; split=> //.

  set mu_top0 := initial_SM dS dT fS fT j.

  have mu_top_wd : SM_wd mu_top0.
  { apply: initial_SM_wd=> //. 
    move=> b1 b2 d0 l; split.
    apply Mem.valid_block_inject_1 with (m1:=m1) (m2:=m2) in l=> //.
    by apply: valid_dec.
    apply Mem.valid_block_inject_2 with (m1:=m1) (m2:=m2) in l=> //.
    by apply: valid_dec.
    move=> b1; rewrite /fS; case l: (j b1)=> [[x y]|//].
    exists x,y; split=> //.
    rewrite /fT; set fT0 := (fun b0 : block =>
      isGlobalBlock (ge (cores_T ix)) b0 || getBlocks vals2 b0).
    move: H; move/REACH_inject; case/(_ _ _ inj fT0)=> b0.
    case/orP=> H2.
    move: pres; move/meminj_preserves_globals_isGlobalBlock.
    have H3: isGlobalBlock my_ge b0 by move: H2; rewrite -isGlob_iffS.
    move/(_ b0 H3)=> J; exists b0,0; split=> //.
    by apply/orP; left; rewrite -isGlob_iffT.
    case: (getBlocks_inject _ _ _ vinj _ H2)=> x' []y' []J X.
    by exists x',y'; split=> //; apply/orP; right.
    by case=> d []J H; rewrite l in J; case: J=> -> _.
    set fT0 := (fun b0 : block =>
      isGlobalBlock (ge (cores_T ix)) b0 || getBlocks vals2 b0).
    move/REACH_inject; case/(_ _ _ inj fT0)=> b0.
    case/orP=> H2.
    move: pres; move/meminj_preserves_globals_isGlobalBlock.
    have H3: isGlobalBlock my_ge b0 by move: H2; rewrite -isGlob_iffS.
    move/(_ b0 H3)=> J; exists b0,0; split=> //.
    by apply/orP; left; rewrite -isGlob_iffT.
    case: (getBlocks_inject _ _ _ vinj _ H2)=> x' []y' []J X.
    by exists x',y'; split=> //; apply/orP; right.
    by case=> d []J; rewrite J in l; discriminate.
    move=> b0 H.
    case: (REACH_inject _ _ _ inj 
      (fun b0 : block =>
        isGlobalBlock (ge (cores_S ix)) b0 || getBlocks vals1 b0)
      (fun b0 : block =>
        isGlobalBlock (ge (cores_T ix)) b0 || getBlocks vals2 b0) _ b0).
    move=> b1; case/orP=> H2.
    move: pres; move/meminj_preserves_globals_isGlobalBlock.
    have H3: isGlobalBlock my_ge b1 by move: H2; rewrite -isGlob_iffS.
    move/(_ b1 H3)=> J; exists b1,0; split=> //.
    by apply/orP; left; rewrite -isGlob_iffT.
    case: (getBlocks_inject _ _ _ vinj _ H2)=> x' []y' []J X.
    by exists x',y'; split=> //; apply/orP; right.
    by apply: (REACH_mono (fun b1 : block =>
      isGlobalBlock (ge (cores_S ix)) b1 || getBlocks vals1 b1)).
    move=> x []y []J _; apply: valid_dec.
    by apply Mem.valid_block_inject_1 with (m1:=m1) (m2:=m2) in J.
    move=> b0 F; apply: valid_dec; apply: reach.
    apply: (REACH_mono (fun b1 : block => 
      isGlobalBlock (ge (cores_T ix)) b1 || getBlocks vals2 b1))=> //.
    move=> b1; case/orP=> G. 
    by apply/orP; left; move: G; rewrite -isGlob_iffT.
    by apply/orP; right. }

  set mu_top := Inj.mk mu_top_wd.
  
  have mu_top_val: sm_valid mu_top m1 m2.
  { split.
    by move=> b1; rewrite /DOM /DomSrc; case/orP=> //=; apply: valid_dec'.
    by move=> b2; rewrite /RNG /DomTgt; case/orP=> //=; apply: valid_dec'. }

  apply: Build_R=> /=.
  exists erefl,mu_top,[::]=> /=; split=> //.

  exists erefl; apply: Build_head_inv=> //.
  apply: Build_vis_inv; rewrite /= /RC.reach_basis /vis /mu_top0 /= /fS.

  have ->: RC.args c = vals1.
  { by apply: (RC.initial_core_args g). }

  have ->: RC.rets c = [::].
  { by apply: (RC.initial_core_rets g). }

  have ->: RC.locs c = (fun _ => false).
  { by apply: (RC.initial_core_locs g). }

  move=> /=; rewrite /in_mem {2}/getBlocks /= => b1 H.
  suff [H2|H2]: isGlobalBlock my_ge b1 \/ getBlocks vals1 b1.
  by apply: REACH_nil; apply/orP; left; rewrite -isGlob_iffS.
  by apply: REACH_nil; apply/orP; right.
  case: (orP H)=> //; case/orP=> //; case/orP; first by move=> ->; left.
  by move=> ->; right.

  by [].

  by apply: ord_dec. 

  by case: (Integers.Int.eq _ _).
  by case: (Integers.Int.eq _ _). }(*END [Case: core_initial]*)
    
{(*[Case: diagram]*)
move=> st1 m1 st1' m1' U1 STEP data st2 mu m2 U1_DEF INV.
case: STEP=> STEP STEP_EFFSTEP; case: STEP.

{(*[Subcase: corestep0]*)
move=> STEP. 
set c1 := peekCore st1.
set c2 := peekCore st2.

have [c1' [STEP0 [U1'_EQ [c1_args [c1_rets [c1_locs ST1']]]]]]:
   exists c1',
       Coresem.corestep 
         (t := effect_instance (coreSem (cores_S (Core.i c1)))) 
         (ge (cores_S (Core.i c1))) (Core.c c1) m1 c1' m1' 
   /\ (forall b ofs, U1 b ofs -> 
       RC.reach_set (ge (cores_S (Core.i c1))) (Core.c c1) m1 b)
   /\ RC.args (Core.c (c INV)) = RC.args c1'
   /\ RC.rets (Core.c (c INV)) = RC.rets c1'
   /\ RC.locs c1' 
      = (fun b => RC.locs (Core.c (c INV)) b || freshloc m1 m1' b 
               || RC.reach_set (ge (cores_S (Core.i c1))) (Core.c (c INV)) m1 b)
   /\ st1' = updCore st1 (Core.upd c1 c1').
  { move: (STEP_EFFSTEP STEP)=> EFFSTEP.
    move: STEP; rewrite/LinkerSem.corestep0=> [][]c1' []B C. 
    move: EFFSTEP; rewrite/effstep0.
    move=> []? []/=; rewrite/RC.effstep=> [][]EFFSTEP []u1 []args []rets locs D.
    exists c1'. split=> //. split=> //.
    by move: C D=> ->; move/updCore_inj_upd=> ->; split. }

have EFFSTEP: 
    effect_semantics.effstep 
    (coreSem (cores_S (Core.i c1)))
    (ge (cores_S (Core.i c1))) U1 (Core.c c1) m1 c1' m1'.
  { move: (STEP_EFFSTEP STEP); rewrite/effstep0=> [][] c1'' [] STEP0' ST1''. 
    by rewrite ST1'' in ST1'; rewrite -(updCore_inj_upd ST1'). }

(* specialize core diagram at module (Core.i c1) *)
move: (effcore_diagram _ _ _ _ (sims (Core.i c1))).  
move/(_ _ _ _ _ _ EFFSTEP).
case: (R_inv INV)=> pf []mupkg []mus []mu_eq.
move=> []pf2 hdinv tlinv.

have U1_DEF': forall b ofs, U1 b ofs -> vis mupkg b. 
{ by move=> b ofs U; rewrite -mu_eq; apply: (U1_DEF _ _ U). }

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
set c2''   := cast' (peek_ieq INV) c2'.
set st2'   := updCore st2 (Core.upd c2 c2'').
set data'  := (existT (fun ix => core_data (sims ix)) (Core.i c1) cd'). 
set mu'    := mu_top'.
exists st2', m2', data', mu'. 
split. 

{(* Label: [re-establish invariant] *) 
 apply: Build_R; rewrite ST1'; rewrite /st2'.

 exists pf,mupkg',mus; split=> //.

 (* head_inv *)
 { case: tlinv=> allrel frameall.
   exists erefl=> /=.
   have rcvis: REACH_closed m1' (vis mu').
   { by apply match_visible in MATCH'; apply: MATCH'. }
   apply: (@head_inv_step 
     mupkg m1 m2 mu_top' m1' m2' (head_valid hdinv) INCR SEP LOCALLOC rcvis
     (c INV) (d INV) pf c1' c2'' _ _ mus
     (STACK.pop (CallStack.callStack (s1 INV))) 
     (STACK.pop (CallStack.callStack (s2 INV))) U1 hdinv frameall)=> //=.
   have ->: cast'' pf c2'' = c2' by apply: cast_cast_eq'.
   by []. }

 (* tail_inv *)
 { eapply tail_inv_step with (Esrc := U1) (Etgt := U2) (mu' := mu_top'); eauto.
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
     exists n, effstepN (coreSem (cores_T (Core.i c1)))
               (ge (cores_T (Core.i c1))) n U2 
               (cast'' pf (Core.c (d INV))) m2 c2' m2'.
   { case: STEP'; first by move=> []n ?; exists (S n).
     by move=> [][]n ? _; exists n. }
   by eapply effstepN_valid in STEPN; eauto.
   by apply: (head_valid hdinv).
   by apply match_visible in MATCH'; apply: MATCH'.
   by apply: (head_rel hdinv). } 

 (* fn_tbl *)
 { by rewrite (R_fntbl INV). } 
 } (*end [re-establish invariant]*)
 
 {(* Label: [matching execution] *) 
 have EFFECTS_REFINEMENT: 
     forall b ofs, U2 b ofs = true ->
     visTgt mu b = true /\
     (locBlocksTgt mu b = false ->
       exists b1 d1, 
         foreign_of mu b1 = Some (b, d1) /\
         U1 b1 (ofs - d1) = true /\
         Mem.perm m1 b1 (ofs - d1) Max Nonempty).
 { move=> b ofs X; move: (PERM _ _ X)=> []H Y; split.
   by move: H; rewrite mu_eq. 
   by rewrite mu_eq. }

exists U2; split=> //; case: STEP'=> STEP'.

have STEP'': 
  effstep_plus (coreSem (cores_T (Core.i c2)))
  (ge (cores_T (Core.i c2))) U2 (Core.c (d INV)) m2 c2'' m2'. 
 { set T := C \o cores_T.
   set P := fun ix (x : T ix) (y : T ix) => 
             effstep_plus (coreSem (cores_T ix))
             (ge (cores_T ix)) U2 x m2 y m2'.
   change (P (Core.i c2) (Core.c c2) c2''); apply: cast_indnatdep2.
   by move: STEP'; have ->: pf = peek_ieq INV by apply: proof_irr. }

by left; move: STEP''; apply: stepPLUS_STEPPLUS.

have STEP'': 
  effstep_star (coreSem (cores_T (Core.i c2)))
  (ge (cores_T (Core.i c2))) U2 (Core.c c2) m2 c2'' m2'. 
 { set T := C \o cores_T.
   set P := fun ix (x : T ix) (y : T ix) => 
             effstep_star (coreSem (cores_T ix))
             (ge (cores_T ix)) U2 x m2 y m2'.
   change (P (Core.i c2) (Core.c c2) c2''); apply: cast_indnatdep2.
   by case: STEP'; have ->: pf = peek_ieq INV by apply: proof_irr; by []. }

right; split; first by move: STEP''; apply: stepSTAR_STEPSTAR.

rewrite /sig_ord /data' /=.

have eq: Core.i c1 = projT1 data.
{ by clear - pf2; move: pf2; rewrite /c /s1 /c1 /peekCore /= => ->. }

exists eq; case: STEP'=> STEP' ORD.
have <-: pf2 = sym_eq eq by apply: proof_irr.
by apply: ORD. } (*end [Label: matching execution]*)

} (*end [Subcase: corestep0]*)

move=> []<- []NSTEP.
case CTXT: (inContext st1)=> //.
case AT1: (LinkerSem.at_external0 st1)=> [[[ef1 sig1] args1]|].

{(*[Subcase: at_external0]*)
case FID: (LinkerSem.fun_id ef1)=> [id|//].
case HDL: (LinkerSem.handle _)=> [st1''|//] eq1 A.
have wd: SM_wd mu by apply: (R_wd INV).
have INV': R data (Inj.mk wd) st1 m1 st2 m2 by [].
case: (atext2 AT1 INV')=> args2 AT2.
case: (hdl2 AT1 HDL INV' AT2)=> cd' []st2' []mu' []HDL2 INV2.
exists st2',m2,cd',mu'; split=> //; first by rewrite eq1.
set (empty_U := fun (_ : block) (_ : Z) => false); exists empty_U; split=> //.
left; exists O=> /=; exists st2',m2,empty_U,empty_U; split=> //.
constructor=> //. 
right; split=> //; split=> //.
by move/LinkerSem.corestep_not_at_external0; rewrite AT2.
have in_ctx2: inContext st2 by apply: (R_inContext INV).
by rewrite in_ctx2 AT2 FID HDL2.
by move/LinkerSem.corestep_not_at_external0; rewrite AT2.
}(*end [Subcase: at_external0]*)

case HLT1: (LinkerSem.halted0 st1)=> [rv|].

{(*[Subcase: halted0]*)
case POP1: (popCore st1)=> [st1''|//].
case AFT1: (LinkerSem.after_external (Some rv) st1'')=> [st1'''|//] eq1 A.

have mu_wd: SM_wd mu. 
{ by apply: (R_wd INV). }

have INV': R data (Inj.mk mu_wd) st1 m1 st2 m2.
{ by apply: INV. }

case: (aft2 HLT1 POP1 AFT1 INV')=> 
  rv2 []st2'' []st2' []cd' []mu' []HLT2 CTX2 POP2 AFT2 INV''.
exists st2',m2,cd',mu'.
split=> //; first by rewrite eq1.
exists (fun _ _ => false); split=> //.
left; exists O=> /=; exists st2',m2,(fun _ _ => false),(fun _ _ => false).
split=> //.
rewrite /effstep; split=> //.
rewrite /LinkerSem.corestep; right; split=> //.
have nStep: ~LinkerSem.corestep0 st2 m2 st2' m2.
{ case=> x []step st2'_eq; apply corestep_not_halted in step.
  by move: step HLT2; rewrite /LinkerSem.halted0 /= /RC.halted=> ->. }
split=> //. 
rewrite CTX2.
have atExt2: (LinkerSem.at_external0 st2 = None).
{ case: (LinkerSem.at_external_halted_excl0 st2)=> //.
  by rewrite HLT2. }
by rewrite atExt2 HLT2 POP2 AFT2.
move: HLT2; rewrite /LinkerSem.halted0 /LinkerSem.corestep0.
move=> HLT2' []c' []; move=> STEP _.
apply corestep_not_halted in STEP.
by move: STEP HLT2'=> /=; rewrite/RC.halted=> ->.
}(*end [Subcase: halted0]*)

by [].

} (*end [Case: diagram]*)

{(*Case: halted*)
move=> cd mu c1 m1 c2 m2 v1 inv hlt1.
have mu_wd: SM_wd mu by apply: R_wd inv.
have inv': R cd (Inj.mk mu_wd) c1 m1 c2 m2 by [].
case: (toplevel_hlt2 hlt1 inv')=> v2 hlt2.
case: (R_inv inv')=> pf []mupkg []mus []mu_eq.
move=> []pf2 hdinv tlinv; move: (head_match hdinv)=> mtch0.

have hlt10: 
  halted (coreSem (cores_S (Core.i (c inv')))) (Core.c (c inv)) 
= Some v1.
{ move: hlt1; rewrite /= /LinkerSem.halted.
  case inCtx1: (inContext c1)=> //=.
  case hlt10: (LinkerSem.halted0 c1)=> [v1'|//]; case=> <-.
  by move: hlt10; rewrite /LinkerSem.halted0 /c /= /RC.halted=> ->. }

case: (core_halted (sims (Core.i (c inv'))) _ _ _ _ _ _ mtch0 hlt10).
move=> v2' []inj []vinj []vdef []hlt2' extends.

exists (as_inj mupkg),v2'; split.

rewrite -meminj_preserves_genv2blocks.
rewrite (genvs_domain_eq_match_genvs (my_ge_S (Core.i (c inv')))).
rewrite meminj_preserves_genv2blocks.
case: (match_genv mtch0)=> ext isGlob_frgn.
rewrite match_genv_meminj_preserves_extern_iff_all=> //.
by apply: Inj_wd.
split; first by apply: (val_inject_restrictD _ _ _ _ vinj).
split; first by [].
rewrite /= hlt2.
move: hlt2; rewrite /LinkerSem.halted.
case e: (~~ inContext c2)=> //.
case f: (LinkerSem.halted0 c2)=> [rv|//]; case=> <-.
rewrite /LinkerSem.halted0 /= /RC.halted in f hlt2'.
have g: halted (coreSem (cores_T (Core.i (c inv'))))
               (cast'' pf (Core.c (d inv')))  
      = Some rv.
{ set T := C \o cores_T.
  set P := fun ix (x : T ix) => 
             halted (coreSem (cores_T ix)) x  
           = Some rv.
  change (P (Core.i (c inv')) (cast T (sym_eq pf) (Core.c (d inv')))).
  by apply: cast_indnatdep; rewrite /P; rewrite -f. }
by rewrite -g. }(*END Case: halted*)

Qed.

End linkingSimulation.

Print Assumptions link.