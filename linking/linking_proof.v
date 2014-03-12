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

End glob_lems.

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

Lemma relinv_consistent : Consistent mu (frame_mu0 pkg).
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
  All (fun mu2 => Consistent mu mu2) $ map (Inj.mu \o frame_mu0) mus.
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
                     $ mu_top :: [seq (Inj.mu \o frame_mu0) x | x <- mus]
  ; trash_disj_T   : All (DisjointLT mu_trash) 
                     $ mu_top :: [seq (Inj.mu \o frame_mu0) x | x <- mus]
  ; trash_consist  : All (Consistent mu_trash) 
                     $ mu_top :: [seq (Inj.mu \o frame_mu0) x | x <- mus] }.

End trash_inv.

Definition frgnS_contained mu_trash mu mus :=
  forall b, 
  frgnBlocksSrc mu b -> 
  let mu_rest := join_all mu_trash (map frame_mu0 mus) 
  in locBlocksSrc mu_rest b || frgnBlocksSrc mu_rest b.

Definition frgnT_contained mu_trash mu mus :=
  forall b, 
  frgnBlocksTgt mu b -> 
  let mu_rest := join_all mu_trash (map frame_mu0 mus) 
  in locBlocksTgt mu_rest b || frgnBlocksTgt mu_rest b.

Definition frgnS_mapped mu_trash mu mus :=
  forall b b' d', 
  foreign_of mu b = Some (b',d') -> 
  let mu_rest := join_all mu_trash (map frame_mu0 mus)
  in as_inj mu_rest b = Some (b',d').

Section head_inv.

Import Core.

Variables (c : t cores_S) (d : t cores_T). 
Variable  (pf : c.(i)=d.(i)).

Record head_inv cd mu_trash (mu : Inj.t) mus z m1 m2 : Type :=
  { head_match : (sims c.(i)).(match_state) cd mu 
                 c.(Core.c) m1 (rc_cast'' pf d.(Core.c)) m2 
  ; head_rel   : All (rel_inv_pred mu) mus 
  ; head_vis   : vis_inv c mu 
  ; head_safe  : forall n, 
                 safeN (RC.effsem (cores_S c.(i)).(coreSem)) 
                 espec_S (cores_S c.(i)).(ge) n z c m1 
  ; head_ctndS : frgnS_contained mu_trash mu mus 
  ; head_ctndT : frgnT_contained mu_trash mu mus 
  ; head_mapdS : frgnS_mapped mu_trash mu mus 
  ; head_ctns  : if mus is [:: mu' & mus] then 
                   {subset (sharedSrc mu') <= sharedSrc mu} 
                 else True }.

End head_inv.

Section contain_lems.

Variable mu : Inj.t.

Variables args1 args2 : list val.

Let j := as_inj mu.

Variable vinj : Forall2 (val_inject (restrict j (sharedSrc mu))) args1 args2.

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
    & j b0 = Some (b,d)]. admit. (*assumes no Vundefs at extcall argument sites*)
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

Section contain_lems2.

Context mu_trash (mu : frame_pkg) mus (ctndS : frgnS_contained mu_trash mu mus).

Variables args1 args2 : list val.

Let j := as_inj mu.
Let domS := DomSrc mu.
Let domT := DomTgt mu.
Let frgnS := exportedSrc mu args1.
Let frgnT := exportedTgt mu args2.

Variable vinj : Forall2 (val_inject (restrict j (sharedSrc mu))) args1 args2.

Lemma init_ctndS : 
  frgnS_contained mu_trash (initial_SM domS domT frgnS frgnT j) [:: mu & mus].
Proof.
move: ctndS; rewrite /frgnS_contained=> A b /= C; rewrite /in_mem /=.
rewrite /frgnS /exportedSrc in C; case: (orP C)=> D.
case: (getBlocks_frgnpubS vinj D).
by move/pubsrc_sub_locsrc; rewrite /in_mem /= => -> .
move=> E; rewrite E; case: (orP (A _ E))=> F; rewrite F /=.
by rewrite -(orb_comm true).
by rewrite -!(orb_comm true).
rewrite sharedSrc_iff_frgnpub in D.
case: (orP D)=> E.
rewrite E; case: (orP (A _ E))=> F; rewrite F.
by rewrite -(orb_comm true).
by rewrite -!(orb_comm true).
by move: (pubsrc_sub_locsrc E); rewrite /in_mem /= => ->.
by apply: Inj_wd.
Qed.

Variable ctndT : frgnT_contained mu_trash mu mus.

Lemma init_ctndT : 
  frgnT_contained mu_trash (initial_SM domS domT frgnS frgnT j) [:: mu & mus].
Proof.
move: ctndT; rewrite /frgnT_contained=> A b /= C; rewrite /in_mem /=.
rewrite /frgnT /exportedTgt in C; case: (orP C)=> D.
case: (getBlocks_frgnpubT vinj D).
by move/pubtgt_sub_loctgt; rewrite /in_mem /= => -> .
move=> E; rewrite E; case: (orP (A _ E))=> F; rewrite F /=.
by rewrite -(orb_comm true).
by rewrite -!(orb_comm true).
rewrite /sharedTgt in D.
case: (orP D)=> E.
rewrite E; case: (orP (A _ E))=> F; rewrite F.
by rewrite -(orb_comm true).
by rewrite -!(orb_comm true).
by move: (pubtgt_sub_loctgt E); rewrite /in_mem /= => ->.
Qed.

Variable mapdS : frgnS_mapped mu_trash mu mus.

Lemma init_frgnS_mapped : 
  frgnS_mapped mu_trash (initial_SM domS domT frgnS frgnT j) (mu :: mus).
Proof.
move=> b b' d' /=; case e: (frgnS b)=> // J.
move: e; rewrite /frgnS /exportedSrc sharedSrc_iff_frgnpub.
case/orP=> H1.

move: (getBlocks_frgnpubS vinj H1); case=> H2.
rewrite /join_sm /as_inj /join /=; case e: (join2 _ _ _)=> [[? ?]|].
move: e; case/join2P=> H3 H4.
case: (extern_DomRng' _ (Inj_wd _) _ _ _ H3)=> _ []_ []_ []_ []H5 _.
move: (extBlocksSrc_locBlocksSrc _ (Inj_wd _) _ H5)=> H6.
by move: (pubsrc_sub_locsrc H2); rewrite /in_mem /= H6.
case l: (local_of _ _)=> //[[? ?]|].
rewrite /j in J; rewrite (local_in_all _ _ _ _ _ l) in J.
by case: J=> -> ->.
by apply: Inj_wd.
move: J; rewrite /j /as_inj /join l.
case f: (extern_of _ _)=> //[[? ?]] _.
case: (extern_DomRng _ (Inj_wd _) _ _ _ f)=> H3 _.
move: (extBlocksSrc_locBlocksSrc _ (Inj_wd _) _ H3)=> H4.
by move: (pubsrc_sub_locsrc H2); rewrite /in_mem /= H4.
have fOf: foreign_of mu b = Some (b',d').
{ case: (frgnSrc _ (Inj_wd _) _ H2)=> ? []? []fOf _.
  move: (foreign_in_all _ _ _ _ fOf); rewrite /j in J; rewrite J.
  by case=> -> ->. }
move: (mapdS fOf)=> H3.
rewrite /as_inj /join /=.
case eOf:
  (join2 (extern_of mu) (extern_of (join_all mu_trash (map frame_mu0 mus))) b)
  => [[? ?]|]. 
move: eOf; move/join2P=> []eOf1 eOfAll.
by move: (foreign_in_extern _ _ _ _ fOf); rewrite eOf1; case=> -> ->.
move: (foreign_in_extern _ _ _ _ fOf)=> eOf1.
rewrite /join2 eOf1 in eOf.
have eOfAll: 
  extern_of (join_all mu_trash (map frame_mu0 mus)) b = None.
{ move: eOf.
  case e: (extern_of _ _)=> //[[? ?]].
  move: (extern_in_all _ _ _ _ e); rewrite H3; case=> -> ->.
  by rewrite Pos.eqb_refl Zeq_bool_refl. }
rewrite eOfAll in eOf.
rewrite /as_inj /join eOfAll in H3.
rewrite /join H3.
case l: (local_of mu b)=> //[[? ?]].
by move: (local_some_extern_none l); rewrite eOf1.

case: (orP H1)=> H2.
have fOf: (foreign_of mu b = Some (b',d')). 
{ case: (frgnSrc _ (Inj_wd _) _ H2)=> ? []? []fOf _.
  move: (foreign_in_all _ _ _ _ fOf); rewrite /j in J; rewrite J.
  by case=> -> ->. }
have l: (local_of mu b = None).
{ case l: (local_of mu b)=> //[[? ?]].
  case: (local_locBlocks _ _ _ _ _ l); first by apply: Inj_wd.
  by move=> _ []_ []_ []_ []; rewrite H2. }
move: (mapdS fOf)=> H5.
rewrite /join_sm /as_inj /join /=; case e: (join2 _ _ _)=> [[? ?]|].
move: e; case/join2P=> H3 H4.
move: (extern_in_all _ _ _ _ H3).
by rewrite /j in J; rewrite J; case=> -> ->.
rewrite l.
have f: (extern_of mu b = Some (b',d')).
{ by apply: (foreign_in_extern _ _ _ _ fOf). }
rewrite /join2 f in e.
move: e; case eAll: (extern_of _ _)=> //[[? ?]|].
move: (extern_in_all _ _ _ _ eAll); rewrite H5; case=> -> ->.
by rewrite Pos.eqb_refl Zeq_bool_refl.
by move=> _; rewrite /as_inj /join eAll in H5.

rewrite /as_inj /join /join2 /=.
have l: (local_of mu b = Some (b',d')).
{ case: (pubSrcAx _ (Inj_wd _) _ H2)=> ? []? []H3 _.
  rewrite /j in J; rewrite (local_in_all _ _ _ _ _ H3) in J.
  by case: J=> <- <-. 
  by apply: Inj_wd. }
have e: (extern_of mu b = None).
{ by rewrite (local_some_extern_none l). }
have eOfAllNone: 
  join2 (extern_of mu) (extern_of (join_all mu_trash (map frame_mu0 mus))) b
  = None.
{ by rewrite /join2 e. }
by rewrite eOfAllNone /join; rewrite l.
by apply: Inj_wd.
Qed.

End contain_lems2.

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
by case: inv=> // A _ _ _ _ _ _ _; apply: (match_validblocks _ A).
Qed.

Lemma head_atext_inj ef sig args : 
  at_external (coreSem (cores_S (Core.i c))) (RC.core (Core.c c)) 
    = Some (ef,sig,args) -> 
  Mem.inject (as_inj mu) m1 m2.
Proof.
move=> atext; move: (head_match inv)=> mtch.
by case: (core_at_external (sims (Core.i c)) _ _ _ _ _ _ mtch atext).
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
              , frgnS_contained mu_trash mu0 mus' 
              , frgnT_contained mu_trash mu0 mus' 
              , frgnS_mapped mu_trash mu0 mus' 
              & if mus' is [:: mu' & mus''] then 
                  {subset (sharedSrc mu') <= sharedSrc mu0}
                else True]
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
            , frgnS_contained mu_trash mu0 mus 
            , frgnT_contained mu_trash mu0 mus 
            , frgnS_mapped mu_trash mu0 mus 
            , if mus is [:: mu' & mus'] then 
                {subset (sharedSrc mu') <= sharedSrc mu0}
              else True
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
move=> []pf []cd []? []? []? []? []? []? []B XS MS XT Y C.
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
move=> []pf []cd []? []? []? []? []? []? []B XS MS XT Y C.
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
move=> []pf []cd []? []? []? []? []? []? []B XS MS XT Y C.
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

Lemma tail_size_eq : size s1 = size s2.
Proof.
by case: tlinv=> _; move/frame_all_size_eq.
Qed.

Lemma head_tail_inv c d pf cd (mu : frame_pkg) e sig args1 args2
  (val : sm_valid mu m1 m2)
  (atext1 : at_external (coreSem (cores_S (Core.i c))) 
            (RC.core (Core.c c)) = Some (e,sig,args1))
  (atext2 : at_external (coreSem (cores_T (Core.i c))) 
            (cast'' pf (RC.core (Core.c d))) = Some (e,sig,args2))
  (inj : Mem.inject (as_inj mu) m1 m2)
  (vals_inj : Forall2 (val_inject (as_inj mu)) args1 args2) 
  (inv : @head_inv c d pf cd mu_trash mu mus z m1 m2) :
  tail_inv mu_trash [:: Build_frame_pkg val & mus] z [:: c & s1] [:: d & s2] m1 m2.
Proof.
split=> /=.
split; first by apply: (head_rel inv).
by case: tlinv.
split. 
exists pf,cd,e,sig,args1,e,sig,args2; split.
apply: Build_frame_inv=> //.
by apply: (head_match inv).
by apply: (head_vis inv).
by apply: (head_safe inv).
by apply: (head_ctndS inv).
by apply: (head_ctndT inv).
by apply: (head_mapdS inv).
by apply: (head_ctns inv).
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
move=> []inv containS mapS containT all /=.

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

by apply: containS.
by apply: mapS.
by apply: containT.
by move: all; case: mus' IH F containS mapS containT p.
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
by case: hdinv=> ? ? A _ _ _ _ _; apply: (vis_inv_step A)=> //.
case: hdinv=> ? ? _ A _ _ _ _; move: (effax1 effstep)=> []step _. 
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
by move: (head_ctndS hdinv); rewrite/frgnS_contained -(intern_incr_frgnsrc incr).
by move: (head_ctndT hdinv); rewrite/frgnT_contained -(intern_incr_frgntgt incr).
by move: (head_mapdS hdinv); rewrite/frgnS_mapped -(intern_incr_foreign _ _ incr).
move: (head_ctns hdinv); generalize dependent mus; case=> //.
by move=> mu0 ? _ _ A b; move/A; apply: intern_incr_sharedSrc.
Qed.

Lemma trash_inv_step (mu_trash : Inj.t) mupkg mupkg' (mus : seq frame_pkg) : 
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
eapply DisjointLT_intern_step 
  with (mu := mu) (m1 := m1) (m2 := m2)=> //. 
by move: H; rewrite A.
by move: incr; rewrite B.
by move: sep; rewrite B.
split=> //. 
move=> b1 b2 b2' d2 d2' A1 A2.
case e: (as_inj mupkg b1)=> [[b2'' d2'']|].
rewrite A in e; rewrite B in A2.
case: (intern_incr_as_inj_eq incr e A2)=> eq1 eq2.
rewrite -eq1 -eq2.
rewrite -A in e; apply: (K _ _ _ _ _ A1 e).
case: sep; rewrite -A -B; move/(_ _ _ _ e A2); case=> DS _.
case; move/(_ _ DS); case. 
by case: (as_inj_DomRng _ _ _ _ A2 (Inj_wd _)).
case: E=> H1 H2; apply: H1; rewrite /DOM.
by case: (as_inj_DomRng _ _ _ _ A1 (Inj_wd _))=> ->.
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

    (* main invariant *)
  ; R_inv : 
    exists (pf : c.(Core.i)=d.(Core.i)) mu_trash (mu_top : Inj.t) mus z, 
    let mu_tot := join_all (frame_mu0 mu_trash) $ mu_top :: map frame_mu0 mus in
    [/\ mu = restrict_sm mu_tot (vis mu_tot) 
      , REACH_closed m1 (vis mu)
      , trash_inv mu_trash mu_top mus m1 m2
      , @head_inv c d pf (Lex.get c.(Core.i) data) mu_trash mu_top mus z m1 m2 
      & tail_inv mu_trash mus z (pop s1) (pop s2) m1 m2] 

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
have valid: sm_valid mu_top m1 m2 by apply: (match_validblocks _ (head_match E)).
have D': trash_inv mu_trash (Build_frame_pkg valid) mus m1 m2 by [].
rewrite B; apply: restrict_sm_WD=> //; apply: join_all_wd.
by move: (R_AllDisjointS D' E F)=> /=; rewrite map_comp.
by move: (R_AllDisjointT D' E F)=> /=; rewrite map_comp.
by move: (R_AllConsistent D' E F)=> /=; rewrite map_comp.
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
have valid: sm_valid mu_top m1 m2 by apply: (match_validblocks _ (head_match Y)).
have X': trash_inv mu_trash (Build_frame_pkg valid) mus m1 m2 by [].
rewrite B. 
apply: restrict_sm_preserves_globals'.
apply: join_all_preserves_globals.
by apply: (trash_presglob X).
by move: (R_AllDisjointS X' Y Z)=> /=; rewrite map_comp.
by move: (R_AllDisjointT X' Y Z)=> /=; rewrite map_comp.
by move: (R_AllConsistent X' Y Z)=> /=; rewrite map_comp.
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

Lemma R_len_callStack : size (callStack x1) = size (callStack x2).
Proof.
case: (R_inv pf)=> []pf0 []? []? []? []? []A B C D.
move/tail_size_eq; rewrite /s1 /s2.
have l1: ssrnat.leq 1 (size (callStack x1)). 
  by move: (callStack_wf x1); move/andP=> [].
have l2: ssrnat.leq 1 (size (callStack x2)). 
  by move: (callStack_wf x2); move/andP=> [].
by apply: pop_size.
Qed.

Lemma R_inContext : inContext x1 -> inContext x2.
Proof.
by rewrite /inContext /callStackSize R_len_callStack.
Qed.

End R_lems.

Section initCore_lems.

Context (my_cores : 'I_N -> t) c1 ix v vs 
        (init1 : initCore my_cores ix v vs = Some c1).

Lemma initCore_ix : ix = Core.i c1.
Proof.
move: init1; rewrite /init1 /initCore.
by case: (RC.initial_core _ _ _ _)=> // c; case; case: c1=> ? ?; case.
Qed.

Lemma initCore_args : RC.args (Core.c c1) = vs.
Proof.
move: init1; rewrite /init1 /initCore /RC.initial_core.
case: (initial_core _ _ _ _)=> // c. 
by case; case: c1=> ?; case=> ? ? ? ? /=; case=> _ _ ->.
Qed.

Lemma initCore_rets : RC.rets (Core.c c1) = [::].
Proof.
move: init1; rewrite /init1 /initCore /RC.initial_core.
case: (initial_core _ _ _ _)=> // c. 
by case; case: c1=> ?; case=> ? ? ? ? /=; case=> _ _ _ ->.
Qed.

Lemma initCore_locs : RC.locs (Core.c c1) = (fun _ => false).
Proof.
move: init1; rewrite /init1 /initCore /RC.initial_core.
case: (initial_core _ _ _ _)=> // c. 
by case; case: c1=> ?; case=> ? ? ? ? /=; case=> _ _ _ _ ->.
Qed.

End initCore_lems.

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
case: (R_inv inv)=> pf []mu_trash []mu_top []mus []x []_.
move=> rc _; move/head_match.
unfold LinkerSem.at_external0 in atext1.
have atext1':
  at_external 
    (RC.effsem (coreSem (cores_S (Core.i (peekCore st1))))) 
    (Core.c (peekCore st1)) =
  Some (ef,sig,args1) by rewrite /RC.at_external.
move=> hd_match _.
case: (core_at_external (sims (Core.i (c inv))) 
      _ _ _ _ _ _ hd_match atext1').
move=> inj []rc1 []args2 []valinj []atext2 rc2; exists args2.
set T := C \o cores_T.
rewrite /LinkerSem.at_external0.
set P := fun ix (x : T ix) => 
            at_external (coreSem (cores_T ix)) x
            = Some (ef, sig, args2).
change (P (Core.i (peekCore st2)) (RC.core (Core.c (peekCore st2)))).
have X: (P (Core.i (c inv)) (cast'' pf (RC.core (Core.c (d inv))))).
{ move: atext2=> /=; rewrite /RC.at_external /P /=.
  have eq: at_external (coreSem (cores_T (Core.i (c inv))))
            (cast'' pf (RC.core (Core.c (d inv)))) =
           at_external (coreSem (cores_T (Core.i (d inv))))
            (RC.core (Core.c (d inv))). 
  { set T' := C \o cores_T.
    set P' := fun ix (x : T' ix) => 
                 at_external (coreSem (cores_T ix)) x
                 = at_external (coreSem (cores_T (Core.i (d inv))))
                     (RC.core (Core.c (d inv))).
    change (P' (Core.i (c inv)) 
               (cast T' (sym_eq pf) (RC.core (Core.c (d inv))))).
    by apply: cast_indnatdep. }
  rewrite eq=> X.
  set T' := RC.state \o C \o cores_T.
  set P' := fun ix (x : T' ix) => 
               at_external (coreSem (cores_T ix)) (RC.core x)
               = Some (ef, sig, args2).
  change (P' (Core.i (d inv))  (Core.c (d inv))).
  have X': (P' (Core.i (c inv)) (rc_cast'' pf (Core.c (d inv))))
    by apply: X.
  by apply: (cast_indnatdep' X'). }
by apply: (cast_indnatdep' X).
Qed.

Import CallStack.

Require Import sepcomp.compcert. Import CompcertLibraries.

Lemma hdl2 args2 : 
  LinkerSem.at_external0 st2 = Some (ef,sig,args2) -> 
  exists cd' st2',
    LinkerSem.handle id st2 args2 = Some st2'
    /\ R cd' mu st1' m1 st2' m2.
Proof.
move=> A.
case: (R_inv inv)=> pf []mu_trash []mu_top []mus []x []mu_eq.
move=> rc trinv hdinv tlinv; move: hdl1; rewrite LinkerSem.handleP.
move=> []all_at1 []ix []c1 []fntbl1 init1 st1'_eq.

have atext1': 
  at_external (coreSem (cores_S (Core.i (c inv)))) (RC.core (Core.c (c inv))) 
  = Some (ef,sig,args1) by [].

have atext2': 
  at_external (coreSem (cores_T (Core.i (c inv)))) 
              (cast'' pf (RC.core (Core.c (d inv))))
  = Some (ef,sig,args2).
 { set T := C \o cores_T.
   set P := fun ix (x : T ix) => 
              at_external (coreSem (cores_T ix)) x
              = Some (ef, sig, args2).
   have: (P (Core.i (d inv)) (RC.core (Core.c (d inv))))
     by rewrite /LinkerSem.at_external0.
   by apply: cast_indnatdep. }

have atext2'': 
  at_external (RC.effsem (coreSem (cores_T (Core.i (c inv)))))
              (rc_cast'' pf (Core.c (d inv)))
  = Some (ef,sig,args2).
 { set T := RC.state \o C \o cores_T.
   set P := fun ix (x : T ix) => 
              at_external (RC.effsem (coreSem (cores_T ix))) x
              = Some (ef, sig, args2).
   have: (P (Core.i (d inv)) (Core.c (d inv)))
     by rewrite /LinkerSem.at_external0.
   by apply: cast_indnatdep. }

case: (core_at_external (sims (Core.i (c inv))) 
      _ _ _ _ _ _ (head_match hdinv) atext1').
move=> inj []rc_exportedSrc []args2' []vinj []atext2''' rc_exportedTgt.

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
  have [b0 [ofs [getbs1 asinj1]]]: 
    exists b0 ofs, 
    [/\ getBlocks args1 b0
      & as_inj mu_top b0 = Some (b,ofs)]. admit. (*assumes no Vundef at extcall points*)
  by case: (as_inj_DomRng _ _ _ _ asinj1 (Inj_wd _))=> _ ->. 
  by apply: sharedtgt_sub_domtgt. }
 
set (j := as_inj mu_top).
set (domS := DomSrc mu_top).
set (domT := DomTgt mu_top).
set (frgnS := exportedSrc mu_top args1).
set (frgnT := exportedTgt mu_top args2).

have st1_len: (ssrnat.leq 1 (size (callStack (stack st1)))).
{ by move: (callStack_wf st1); move/andP=> []_ ?. }

have st2_len: (ssrnat.leq 1 (size (callStack (stack st2)))).
{ by move: (callStack_wf st2); move/andP=> []_ ?. }

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

have j_domS_domT:
  forall b1 b2 d0,
  j b1 = Some (b2, d0) -> domS b1 = true /\ domT b2 = true.
{ move=> b1 b2 d0; rewrite /j /domS /domT=> asinj.
  by apply: (as_inj_DomRng _ _ _ _ asinj (Inj_wd _)). }

have reach_frgnS:
  forall b,
  REACH m1
   (fun b' : block =>
    isGlobalBlock (ge (cores_S (Core.i c1))) b' || getBlocks args1 b') b -> 
  frgnS b.
{ rewrite /frgnS; move=> b rch; apply: rc_exportedSrc; rewrite /exportedSrc.
  apply: (REACH_mono _ _ _ _ _ rch)=> b'; move/orP; case; last by move=> ->.
  by move/globs_frgnS; apply: frgnsrc_sub_exportedsrc. }

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
    move: H; rewrite /isGlobalBlock /=.
    case e1: (Genv.invert_symbol _ _)=> //.
    move: (Genv.invert_find_symbol _ _ e1)=> M O.
    have [id' M']: 
      exists id', 
      Genv.find_symbol (ge (cores_S (Core.i (c inv)))) id' = Some b.
    { admit. (*follows from genv_domains_eq*) }
    move: (J _ _ M')=> E.
    by move: (foreign_in_extern _ _ _ _ fOf); rewrite E; case.
    case e2: (Genv.find_var_info _ _)=> //[gv].
    have [gv' M']: 
      exists gv',
      Genv.find_var_info (ge (cores_S (Core.i (c inv)))) b = Some gv'.
    { admit. (*follows from genv_domains_eq*) }
    move: (K _ _ M').
    by move: (foreign_in_extern _ _ _ _ fOf)=> ->; case. }
  by rewrite eq. }

have reach_frgnT:  
  forall b,
  REACH m2
   (fun b' : block =>
    isGlobalBlock (ge (cores_T (Core.i c1))) b' || getBlocks args2 b') b ->
  frgnT b.
{ rewrite /frgnT; move=> b rch. apply rc_exportedTgt. rewrite /exportedTgt.
  apply: (REACH_mono _ _ _ _ _ rch)=> b'; move/orP; case; last by move=> ->.
  by move/globs_frgnT; apply: frgntgt_sub_exportedtgt. }

have rc_rgnS: REACH_closed m1 frgnS.
{ by apply: rc_exportedSrc. }

have vinj': Forall2 (val_inject (as_inj mu_top)) args1 args2. 
{ by apply: (forall_vals_inject_restrictD _ _ _ _ vinj). }

have frgnS_mapped:
 forall b1,
 frgnS b1 -> 
 exists b2 ofs, j b1 = Some (b2, ofs) /\ domT b2.
{ rewrite /frgnS /exportedSrc=> b1; move/orP; case=> getbs1.
  case: (getBlocks_inject _ _ _ vinj _ getbs1)=> b2 []ofs []asinj getbs2.
  exists b2,ofs; split; first by case: (restrictD_Some _ _ _ _ _ asinj).
  by apply: exportedTgt_DomTgt; apply/orP; left.
  move: getbs1; rewrite /sharedSrc; case e: (shared_of _ _)=> //[[b2 ofs]].
  move=> _; exists b2,ofs; split=> //.
  rewrite /j; apply: shared_in_all=> //.
  by apply: Inj_wd.
  have shrdS: sharedSrc mu_top b1 by rewrite /sharedSrc e.
  move: (shared_SrcTgt _ (Inj_wd _) _ shrdS)=> []b2' []ofs' []e' shrdT.
  move: e e'=> ->; case=> -> _. 
  by apply: (sharedTgt_DomTgt shrdT). }

have domS_valid:
  forall b, domS b -> Mem.valid_block m1 b.
{ move: (match_validblocks _ (head_match hdinv)); case=> H I.
  by apply: H. }

have domT_valid:
  forall b, domT b -> Mem.valid_block m2 b.
{ move: (match_validblocks _ (head_match hdinv)); case=> H I.
  by apply: I. }

have ep: 
  In (Vptr id Int.zero,Vptr id Int.zero,sig) entry_points. 
{ admit. (*this is a ridiculous side condition that needs to be 
           communicated to the semantics somehow; e.g., whenever
           we're at external w/ fid id, then (id,id) in entry_points*) }

have [cd_new [c2 [pf_new [init2 mtch12]]]]:
  exists (cd_new : core_data entry_points (sims (Core.i c1))) 
         (c2 : Core.t cores_T)
         (pf : Core.i c1 = Core.i c2),
    [/\ initCore cores_T ix (Vptr id Integers.Int.zero) args2 = Some c2
      & match_state (sims (Core.i c1)) cd_new
        (initial_SM domS domT frgnS frgnT j) 
        (Core.c c1) m1 (rc_cast'' pf (Core.c c2)) m2].

{ move: init1; rewrite /initCore.
  case init1: (RC.initial_core _ _ _ _)=> //[c1']; case=> X.
  generalize dependent c1; case=> c1_i c1; intros.
  move: (X) init1; case=> eq _ init1; subst ix=> /=.
  case: (core_initial _ _ _ _ _ (sims c1_i) _ _ _ ep args1
        _ m1 j args2 m2 frgnS frgnT domS domT init1 inj vinj')=> //.
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

have valid': sm_valid mu_top m1 m2. 
{ by apply: (head_valid hdinv). }

set pkg := Build_frame_pkg valid'.

set mu_new := initial_SM domS domT frgnS frgnT j.

have mu_new_wd: SM_wd mu_new.
{ admit. (*by core_initial_wd*) }

set mu_new' := Inj.mk mu_new_wd.

have cons_trash_j: consistent (as_inj mu_trash) j.
{ rewrite /j /consistent=> b1 b2 b2' d2 d2' eOf asInj.
  case: trinv=> X Y Z W U V.
  move: V=> /=; case=> AA BB.
  by apply: (AA b1 b2 b2' d2 d2' eOf asInj). }

have cons_mutop_j: consistent (as_inj mu_top) j.
{ rewrite /j /consistent=> b1 b2 b2' d2 d2' eOf asInj.
  by rewrite eOf in asInj; case: asInj=> -> ->. }

have getBlocks1_frgnpub b:
  getBlocks args1 b -> 
  [\/ pubBlocksSrc mu_top b | frgnBlocksSrc mu_top b].
{ move=> H1; apply: (getBlocks_frgnpubS vinj H1). }

have getBlocks1_locpub b: 
  locBlocksSrc mu_top b -> 
  getBlocks args1 b -> 
  pubBlocksSrc mu_top b.
{ move=> H1 H2; apply: (getBlocks_locpubS vinj H1 H2). }

have mu_new_rel_inv_pkg: rel_inv_pred mu_new pkg.
{ rewrite /mu_new; apply: Build_rel_inv.
  split=> //; first by rewrite initial_SM_as_inj /j; apply: inject_incr_refl.
  split; first by rewrite initial_SM_as_inj /j /pkg /= => ? ? ? ->.
  split; first by rewrite /pkg /initial_SM /domS /DomSrc /= => ? ->.
  by rewrite /pkg /initial_SM /domT /DomTgt /= => ? ->.
  apply: Build_disjinv.
  by rewrite /initial_SM /= predI01.
  by rewrite /initial_SM /= predI01.
  move=> b; rewrite /in_mem /= /in_mem /= /frgnS; move/andP=> []X Y.
  move: rc_exportedSrc; rewrite /exportedSrc=> Z.
  rewrite (sharedSrc_iff_frgnpub mu_top (Inj_wd _)) in Z.
  cut [|| getBlocks args1 b, frgnBlocksSrc mu_top b | pubBlocksSrc mu_top b].
  case/orP; first by apply: getBlocks1_locpub.
  case/orP=> //. 
  by move/(frgnBlocksSrc_locBlocksSrc _ (Inj_wd _)); rewrite Y.
  apply: Z; apply: REACH_nil.  
  move: X; rewrite /exportedSrc sharedSrc_iff_frgnpub.
  by move=> ->.
  by apply: Inj_wd.
  rewrite /initial_SM /frgnS /= => b1 b2 d'.
  case e: (exportedSrc _ _ _)=> // J.
  rewrite /in_mem /=; case/orP.
  move: e; rewrite /exportedSrc sharedSrc_iff_frgnpub.
  case/orP. 
  move=> H1 H2; move: (getBlocks1_locpub _ H2 H1)=> H3.
  case: (StructuredInjections.pubSrc _ (Inj_wd _) _ H3)=> ? []? []X Y.
  rewrite /j in J; move: (pub_in_all _ (Inj_wd _) _ _ _ X); rewrite J.
  by case=> -> ->.
  case/orP; first by move/(frgnBlocksSrc_locBlocksSrc _ (Inj_wd _))=> ->.
  move=> H3.
  case: (StructuredInjections.pubSrc _ (Inj_wd _) _ H3)=> ? []? []X Y.
  rewrite /j in J; move: (pub_in_all _ (Inj_wd _) _ _ _ X); rewrite J.
  by case=> -> ->.
  by apply: Inj_wd. 
  move=> H3.
  case: (orP e)=> H1.
  case fS: (frgnBlocksSrc mu_top b1).
  have fT: (frgnBlocksTgt mu_top b2).
  { case: (frgnSrc _ (Inj_wd _) _ fS)=> []? []? []fOf fT'.
    move: (foreign_in_all _ _ _ _ fOf); rewrite /j in J; rewrite J.
    by case=> e1 _; rewrite -e1 in fT'. }
  by rewrite (frgnBlocksTgt_locBlocksTgt _ (Inj_wd _) _ fT) in H3.
  have lS: (locBlocksSrc mu_top b1).
  { move: e; rewrite /exportedSrc sharedSrc_iff_frgnpub.
    rewrite fS /=; case/orP.
    case/getBlocks1_frgnpub; first by apply: pubsrc_sub_locsrc.
    by rewrite fS.
    by apply: pubsrc_sub_locsrc.
    by apply: Inj_wd. }
  move: (getBlocks1_locpub _ lS H1)=> H4.
  case: (StructuredInjections.pubSrc _ (Inj_wd _) _ H4)=> ? []? []X Y.
  rewrite /j in J; move: (pub_in_all _ (Inj_wd _) _ _ _ X); rewrite J.
  by case=> -> ->.
  rewrite sharedSrc_iff_frgnpub in H1.
  case: (orP H1).
  case/(frgnSrc _ (Inj_wd _) _)=> ? []? []fOf fT'.
  move: (foreign_in_all _ _ _ _ fOf); rewrite /j in J; rewrite J.
  case=> e1 _; rewrite -e1 in fT'. 
  by rewrite (frgnBlocksTgt_locBlocksTgt _ (Inj_wd _) _ fT') in H3.
  move=> H4.
  case: (StructuredInjections.pubSrc _ (Inj_wd _) _ H4)=> ? []? []X Y.
  rewrite /j in J; move: (pub_in_all _ (Inj_wd _) _ _ _ X); rewrite J.
  by case=> -> ->.
  by apply: Inj_wd.
  by move=> /=; rewrite initial_SM_as_inj; apply: cons_mutop_j. }

have mu_new_rel_inv_all: 
  All (rel_inv_pred (initial_SM domS domT frgnS frgnT j)) mus.
{ admit. (*provable, i think*)}

have mu_new_vis_inv: vis_inv c1 mu_new'.
{ apply: Build_vis_inv=> // b; rewrite /in_mem /= => Y.
  rewrite /vis /mu_new /frgnS /exportedSrc /=.
  move: Y; rewrite /RC.reach_basis; case/orP.
  case/orP. case/orP. move=> H1.
  have H1': isGlobalBlock (ge (cores_S (Core.i (c inv)))) b.
  { by rewrite -isGlob_iffS. }
  apply/orP; right; rewrite sharedSrc_iff_frgnpub. 
  apply/orP; left.
  by case: (match_genv (head_match hdinv))=> _; move/(_ b H1').
  by apply: Inj_wd.
  have eq: RC.args (Core.c c1) = args1. 
  { erewrite initCore_args; eauto. }
  by rewrite eq=> ->.
  have eq: RC.rets (Core.c c1) = [::]. 
  { erewrite initCore_rets; eauto. }
  by rewrite eq getBlocksD_nil.
  have eq: RC.locs (Core.c c1) = (fun _ => false).
  { erewrite initCore_locs; eauto. }
  by rewrite eq. }

have trinv_new:
  trash_inv mu_trash mu_new' (pkg :: mus) m1 m2.
{ case: trinv=> X Y Z W U V.
  apply: Build_trash_inv=> //.
  split=> //=; first by rewrite predI01.
  split=> //=; first by rewrite predI01. 
  by split=> //=; rewrite /mu_new initial_SM_as_inj. }

have mu_new'_ctndS: 
  frgnS_contained mu_trash mu_new' (pkg :: mus).
{ rewrite /mu_new' /= /mu_new /domS /domT /frgnS /frgnT. 
  cut (
    frgnS_contained mu_trash
     (initial_SM (DomSrc pkg) (DomTgt pkg) (exportedSrc pkg args1)
        (exportedTgt pkg args2) j) (pkg :: mus))=> //.
  apply: init_ctndS.
  by apply: (head_ctndS hdinv).
  by apply: vinj. }

have mu_new'_ctndT: 
  frgnT_contained mu_trash mu_new' (pkg :: mus).
{ rewrite /mu_new' /= /mu_new /domS /domT /frgnS /frgnT. 
  cut (
    frgnT_contained mu_trash
     (initial_SM (DomSrc pkg) (DomTgt pkg) (exportedSrc pkg args1)
        (exportedTgt pkg args2) j) (pkg :: mus))=> //.
  apply: init_ctndT.
  by apply: vinj. 
  by apply: (head_ctndT hdinv). }

have mu_new'_mapd: 
  linkingSimulation.frgnS_mapped mu_trash mu_new' (pkg :: mus).
{ rewrite /mu_new' /= /mu_new /domS /domT /frgnS /frgnT /j.
  cut (
   linkingSimulation.frgnS_mapped mu_trash
     (initial_SM (DomSrc pkg) (DomTgt pkg) (exportedSrc pkg args1)
        (exportedTgt pkg args2) (as_inj pkg)) (pkg :: mus))=> //.
  apply: init_frgnS_mapped.
  by apply: vinj. 
  by apply: (head_mapdS hdinv). }

have shrd_pkg_sub_mu_new':
 {subset sharedSrc pkg <= sharedSrc mu_new'}.
{ rewrite /mu_new' /= /mu_new=> b; rewrite /in_mem /= /is_true. 
  rewrite sharedSrc_iff_frgnpub. 
  rewrite sharedSrc_iff_frgnpub /= /frgnS /exportedSrc sharedSrc_iff_frgnpub.
  by case/orP=> ->; rewrite -!(orb_comm true).
  by apply: Inj_wd.
  move: mu_new_wd mu_new' mu_new_vis_inv trinv_new 
    mu_new'_ctndS mu_new'_ctndT mu_new'_mapd.
  rewrite /mu_new /frgnS /exportedSrc sharedSrc_iff_frgnpub.
  by move=> H ? ? ? ? ? ?; apply: H.
  by apply: Inj_wd. by apply: Inj_wd. by apply: Inj_wd. }

have hdinv_new:
  head_inv pf_new cd_new mu_trash mu_new' (pkg :: mus) x m1 m2.
{ apply: Build_head_inv=> //.
  admit.  (*safeN*) }

exists (Lex.set (Core.i c1) cd_new cd),st2'; split.
rewrite LinkerSem.handleP; exists all_at2,ix,c2; split=> //.
by move: fntbl1; rewrite (R_fntbl inv).

have valid_new: sm_valid mu_new' m1 m2. 
{ rewrite /initial_SM /sm_valid /DOM /RNG /DomSrc /DomTgt /=.
  rewrite /domS /domT; split=> b; generalize dependent valid'; case.
  by move=> X ? ? ? ? ? ? ? ? H; apply: (X b).
  by move=> ? X ? ? ? ? ? ? ? H; apply: (X b). }

set (pkg_new := Build_frame_pkg valid_new).
set (mu_tot := join_all mu_trash [seq frame_mu0 i | i <- pkg :: mus]).
set (mu_tot_new := 
  join_all mu_trash [seq frame_mu0 i | i <- pkg_new :: pkg :: mus]).

have mu_tot_new_eq: mu_tot_new = mu_tot. 
{ rewrite /mu_tot_new /mu_tot /pkg_new /= join_sm_absorb'=> //. 
  by apply: extern_in_all.
  rewrite /mu_new /= /domS.
  by apply: extsrc_sub_domsrc.
  by apply: exttgt_sub_domtgt. 
  by apply: frgnsrc_sub_exportedsrc.
  by apply: frgntgt_sub_exportedtgt. }

have pf_new':
    Core.i (STACK.head st1' (callStack_nonempty st1'))
  = Core.i (STACK.head st2' (callStack_nonempty st2')).
{ by rewrite eq1 eq2; apply: pf_new. }

apply: Build_R.
exists pf_new',mu_trash,mu_new',[:: pkg & mus],x; split=> //.
by move: mu_tot_new_eq; rewrite /mu_tot_new /mu_tot=> ->.
rewrite ->st1'_eq in *.
admit. (*by Lex.gss & hdinv_new*)
have valid'': sm_valid pkg m1 m2 by apply: valid'.

move: (head_tail_inv tlinv valid'' atext1' atext2' inj vinj' hdinv).
rewrite /s1 /s2 st1'_eq /st2' /pkg /= => tlinv'. 
by rewrite st1_eq st2_eq; apply: tlinv'.
by rewrite st1'_eq /st2'; apply: (R_fntbl inv).
Qed.

End call_lems.

Lemma link : SM_simulation_inject linker_S linker_T my_ge my_ge entry_points.
Proof.

eapply Build_SM_simulation_inject
  with (core_data   := Lex.t types)
       (core_ord    := ord)
       (match_state := R).

(* well_founded ord *)
{ by apply: Lex.wf_ord. }

(* match -> SM_wd mu *)
{ by apply: R_wd. }

(* genvs_domain_eq *)
{ by apply: genvs_domain_eq_refl. }

(* match_genv *)
{ by move=> data mu c1 m1 c2 m2; apply: R_match_genv. }

(* match_visible *)
{ by apply: R_match_visible. }

(* match_restrict *)
{ by move=> data mu c1 m1 c2 m2 X H; apply: (R_match_restrict H). }

(* match_validblocks *)
{ by apply: R_match_validblocks. }

(* core_initial *)
{ by admit. (* TODO *) }

{ by admit. (* NOT NEEDED diagram1 *) }

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

  { case: hdinv=> mtch ?; case=> visinv _ _ _ _ _ b ofs A; move: (U1'_EQ _ _ A).
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
{ rewrite mu_eq; apply join_all_restrict_incr with (m1 := m1) (m2 := m2)=> //.
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
by apply: (trash_valid trinv). }

have val0: sm_valid mupkg m1 m2 by apply: (head_valid hdinv).
set mupkg0 := Build_frame_pkg val0.

split. 

(*sep*)
{ rewrite mu_eq. apply join_all_restrict_sep 
   with (m1 := m1) (m2 := m2) (m1' := m1') (m2' := m2')=> //.
by move: (head_AllConsistent hdinv); rewrite All_comp2 {1}map_comp.
by move: (tail_valid tlinv); rewrite -All_comp3.
by move: (trash_consist trinv)=> /= []; rewrite map_comp; move/consistentC.
by apply: (trash_valid trinv).
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
change (SM_wd (join_all mu_trash [seq (frame_mu0 i) | i <- mupkg0 :: mus])).
have trinv': trash_inv mu_trash mupkg0 mus m1 m2 by [].
apply: join_all_wd.
by move: (R_AllDisjointS trinv' hdinv tlinv); rewrite All2_comp2 map_comp.
by move: (R_AllDisjointT trinv' hdinv tlinv); rewrite All2_comp2 map_comp.
by move: (R_AllConsistent trinv' hdinv tlinv); rewrite All2_comp2 map_comp. }

(*loc_alloc*)
split; first by rewrite mu_eq; apply: join_all_locally_allocated.

split.

{(* Label: [re-establish invariant] *) 
 apply: Build_R; rewrite ST1'; rewrite /st2'.

 exists pf, mu_trash, mupkg', mus, z; split=> //.

 (*rc m1' (vis mu')*)
 { apply: (join_all_REACH_closed (mu := mupkg) (m1 := m1))=> //.
   by move: (trash_disj_S trinv)=> /= []; rewrite DisjointC.
   by move: (head_AllDisjointLS hdinv); rewrite -map_comp.
   apply mem_unchanged_on_sub with (Q := fun b ofs => U1 b ofs=false).
   by apply effstep_unchanged in EFFSTEP; apply: EFFSTEP.
   move=> b ofs X; move: (U1_DEF' b ofs); rewrite X=> Y.
   by case W: (U1 b ofs)=> //; rewrite W in Y; rewrite Y.
   by apply: (head_ctndS hdinv).  
   by move: (trash_valid trinv); apply/sm_valid_smvalid_src.
   by move: (tail_valid_src tlinv); rewrite -All_comp3. 
   by move: rclosed; rewrite mu_eq vis_restrict_sm.
   by eapply match_visible; eauto. }

 (*trash_inv*)
 { apply trash_inv_step 
   with (m1 := m1) (m2 := m2)
        (mu := mupkg) (mu' := mu_top') (mupkg := mupkg0)=> //.
   by apply: (effstep_fwd _ _ _ _ _ _ _ EFFSTEP).
   case: STEP'=> [STEP'|[STEP' _]]. 
   by apply: (effstep_plus_fwd _ _ _ _ _ _ _ STEP').
   by apply: (effstep_star_fwd _ _ _ _ _ _ _ STEP'). }

 (* head_inv *)
 { case: tlinv=> allrel frameall.
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
   by apply/orP; right. }

 (* tail_inv *)
 { eapply tail_inv_step with (Etgt := U2); eauto.
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
     move: H; rewrite mu_eq /visTgt /= /in_mem /=. 
     move/orP; case; first by move=> ->; apply/orP; left; apply/orP; left.
     move=> H; apply/orP; move: (head_ctndT hdinv H); move/orP; case=> LTGT.
     by left; apply/orP; right; apply: LTGT.
     by right; rewrite H; apply: LTGT.

     move=> LTGT.

     have LTGT_MU: locBlocksTgt mupkg b=false. 
       move: LTGT; rewrite mu_eq /= /in_mem /=. 
       by case: (locBlocksTgt mupkg b).

     case: (Y LTGT_MU)=> b' []d' []FRGN []V PERM'; exists b', d'; split=> //.
     rewrite mu_eq /= /in_mem /=.

     have FRGNS: frgnBlocksSrc mupkg b'. 
       have FRGN': foreign_of (frame_mu0 mupkg0) b' = Some (b,d') by [].
       case: (foreign_DomRng _ (Inj_wd _) _ _ _ FRGN'). 
       by move=> _ []_ []_ []_ [] ->.

     have FRGNT: frgnBlocksTgt mupkg b. 
       case: (frgnSrc _ (Inj_wd _) _ FRGNS)=> b'' []d'' []FRGN' ?.       
       by rewrite FRGN' in FRGN; case: FRGN=> <- _.

     have VIS: vis (join_all mu_trash [seq frame_mu0 i | i <- mus]) b'.
       rewrite /vis; move: (head_ctndS hdinv FRGNS); case/orP=> -> //.
       by apply/orP; right.

     have WD: SM_wd (join_all mu_trash (List.map frame_mu0 mus)). 
       apply: join_all_wd=> /=; split.
       by move: (trash_disj_S trinv)=> /= []_; rewrite -map_comp.
       by move: (tail_AllDisjointLS tlinv); rewrite map_comp. 
       by move: (trash_disj_T trinv)=> /= []_; rewrite -map_comp.
       by move: (tail_AllDisjointLT tlinv); rewrite map_comp. 
       by move: (trash_consist trinv)=> /= []_; rewrite -map_comp.
       by move: (tail_AllConsistent tlinv); rewrite map_comp. 
       
     move: (head_ctndT hdinv FRGNT); move/orP; case.
     by move: LTGT; rewrite mu_eq /= /in_mem /= LTGT_MU /= => ->.
     move=> FRGNTT.

     move: (head_mapdS hdinv FRGN)=> INJ.

     have INJ': as_inj (Inj.mk WD) b' = Some (b,d') by apply: INJ.

     have VIS': vis (Inj.mk WD) b' by apply: VIS.

     have FRGNSS: 
         frgnBlocksSrc (join_all mu_trash [seq frame_mu0 i | i <- mus]) b'.
       by move: (mapped_frgnS_frgnT INJ' VIS)=> ->; apply: FRGNTT.

     rewrite FRGNS /= FRGNSS /restrict /vis /= /in_mem /= FRGNS FRGNSS.

     have FRGNSS': frgnBlocksSrc (Inj.mk WD) b' by apply: FRGNSS.

     case: (frgnSrc _ (Inj_wd _) _ FRGNSS')=> b'' []d'' [] FRGN_OF _.

     have [eq1 eq2]: [/\ b=b'' & d'=d'']. 
       move: (foreign_in_all (Inj.mk WD)); move/(_ _ _ _ FRGN_OF).
       by rewrite INJ'; case=> -> ->.
       
     case E: (locBlocksSrc mupkg b' || _ || _); rewrite/join2; move: E.
       - rewrite (foreign_of_extern_of FRGN).
         move: FRGN_OF; move/foreign_of_extern_of=> ->.
         by rewrite -eq1 -eq2 Pos.eqb_refl Zeq_bool_refl.
       - by rewrite orb_true_r. }

exists U2; split=> //; case: STEP'=> STEP'.

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
} (*end [Label: matching execution]*)

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
case: (hdl2 AT1 HDL INV' AT2)=> cd' []st2' []HDL2 INV2.
exists st2',m2,cd',mu.
split=> //.
split=> //.
by apply: sm_inject_separated_refl.
split=> //.
by apply sm_locally_allocated_refl.
rewrite -eq1 in INV2; split=> //.
set (empty_U := fun (_ : block) (_ : Z) => false).
exists empty_U.
split=> //.
left.
exists O=> /=; exists st2',m2,empty_U,empty_U.
split=> //.
constructor=> //.
right.
split=> //.
split=> //.
move/LinkerSem.corestep_not_at_external0.
by rewrite AT2.
have in_ctx2: inContext st2 by apply: (R_inContext INV).
by rewrite in_ctx2 AT2 FID HDL2.
move/LinkerSem.corestep_not_at_external0.
by rewrite AT2.
}(*end [Subcase: at_external0]*)

case HLT1: (LinkerSem.halted0 st1)=> [rv|].

{(*[Subcase: halted0]*)
case POP1: (popCore st1)=> [st1''|//].
case AFT1: (LinkerSem.after_external (Some rv) st1'')=> [st1'''|//] eq1 A.
admit. (*TODO*)
}(*end [Subcase: halted0]*)

by [].

} (*end [Case: diagram]*)

Admitted. (*WORK-IN-PROGRESS*)

End linkingSimulation.


