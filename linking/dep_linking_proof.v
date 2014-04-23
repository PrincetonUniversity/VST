(* NOTE: To build this variant of the separate compilation proof,          *)
(* do the following:                                                       *)
(*   1) In sepcomp/arguments.v, change the line                            *)
(*                                                                         *)
(*        Require Import sepcomp.effect_simulations*                       *)
(*                                                                         *)
(*    to                                                                   *)
(*                                                                         *)
(*        Require Import sepcomp.dep_effect_simulationsEXP.                *)
(*                                                                         *)
(*   2) Do the same in linking/sepcomp.v, but additionally, change         *)
(*                                                                         *)
(*        Require Import sepcomp.wholeprog_simulations*                    *)
(*                                                                         *)
(*    to                                                                   *)
(*                                                                         *)
(*        Require Import sepcomp.dep_wholeprog_simulations.                *)

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
  Modsem.mk (cores_S' ix).(ge) (RC.effsem (cores_S' ix).(sem)).

Variable fun_tbl : ident -> option 'I_N.
Variable sims : forall i : 'I_N, 
  let s := cores_S i in
  let t := cores_T i in
  SM_simulation_inject s.(sem) t.(sem) s.(ge) t.(ge).
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
  { vis_sup : {subset (RC.roots my_ge c.(Core.c)) <= vis mu} }.

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
  ; frame_at1   : at_external (cores_S c.(i)).(sem) c.(Core.c)
                    = Some (e1, ef_sig1, vals1) 
  ; frame_at2   : at_external (cores_T c.(i)).(sem) (cast'' pf d.(Core.c)) 
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

Record trash_minimal mu_trash mu_top mus : Type :=
  { trash_ctnd_topS   : {subset (extBlocksSrc mu_trash) <= extBlocksSrc mu_top} 
  ; trash_ctnd_topT   : {subset (extBlocksTgt mu_trash) <= extBlocksTgt mu_top} 
  ; trash_ctnd_restS  : forall mu, List.In mu mus -> 
                        {subset (extBlocksSrc mu_trash) <= extBlocksSrc mu} 
  ; trash_ctnd_restT  : forall mu, List.In mu mus -> 
                        {subset (extBlocksTgt mu_trash) <= extBlocksTgt mu} 

  ; trash_fctnd_topS  : {subset (frgnBlocksSrc mu_trash) <= frgnBlocksSrc mu_top} 
  ; trash_fctnd_topT  : {subset (frgnBlocksTgt mu_trash) <= frgnBlocksTgt mu_top} 
  ; trash_fctnd_restS : forall mu, List.In mu mus -> 
                        {subset (frgnBlocksSrc mu_trash) <= frgnBlocksSrc mu} 
  ; trash_fctnd_restT : forall mu, List.In mu mus -> 
                        {subset (frgnBlocksTgt mu_trash) <= frgnBlocksTgt mu} 
  ; trash_eincr_top   : inject_incr (extern_of mu_trash) (extern_of mu_top)
  ; trash_eincr_rest  : forall mu, List.In mu mus -> 
                        inject_incr (extern_of mu_trash) (extern_of mu) }.

Record trash_inv mu_trash mu_top mus m1 m2 : Type :=
  { trash_presglob : Events.meminj_preserves_globals my_ge $ extern_of mu_trash
  ; trash_isglob   : (forall b, isGlobalBlock my_ge b -> frgnBlocksSrc mu_trash b)
  ; trash_valid    : sm_valid mu_trash m1 m2
  ; trash_disj_S   : All (DisjointLS mu_trash) 
                     $ mu_top :: [seq (Inj.mu \o frame_mu0) x | x <- mus]
  ; trash_disj_T   : All (DisjointLT mu_trash) 
                     $ mu_top :: [seq (Inj.mu \o frame_mu0) x | x <- mus]
  ; trash_consist  : All (Consistent mu_trash) 
                     $ mu_top :: [seq (Inj.mu \o frame_mu0) x | x <- mus] 
  ; trash_min      : trash_minimal mu_trash mu_top [seq (Inj.mu \o frame_mu0) x | x <- mus] }.

End trash_inv.

Section trash_inv_lems.

Context (mu_trash mu_top : Inj.t) mus m1 m2 
  (trinv : trash_inv mu_trash mu_top mus m1 m2).

Lemma frgnS_join_all : 
    frgnBlocksSrc (join_all mu_trash [seq frame_mu0 x | x <- mus])
  = frgnBlocksSrc mu_trash.
Proof.
move: (trash_fctnd_restS (trash_min trinv)).
elim: mus=> // mu0 mus' IH /= ctnd; rewrite IH.
extensionality b; case fmu_tr: (frgnBlocksSrc mu_trash b)=> //=.
rewrite (ctnd mu0) /in_mem //; first by left.
by rewrite /in_mem /= fmu_tr andb_false_r.
by move=> mu H; apply: (ctnd mu); right.
Qed.

Lemma frgnS_join_all_sub mus' : 
  (forall mu, List.In mu mus' -> List.In mu [seq frame_mu0 x | x <- mus]) -> 
    frgnBlocksSrc (join_all mu_trash mus')
  = frgnBlocksSrc mu_trash.
Proof.
move=> H1.
cut (frgnBlocksSrc (join_all mu_trash mus')
   = frgnBlocksSrc (join_all mu_trash [seq frame_mu0 x | x <- mus])).
move=> ->.
apply: frgnS_join_all.
elim: mus' H1=> /=.
by move=> _; rewrite frgnS_join_all.
move=> mu2 mus2 /= IH H.
rewrite IH. 
rewrite frgnS_join_all.
move: (trash_fctnd_restS (trash_min trinv))=> /= S.
have IN: In (Inj.mu mu2) [seq (Inj.mu \o frame_mu0) x | x <- mus].
{ cut (In mu2 [seq frame_mu0 x | x <- mus]).
  move=> IN; clear - IN; elim: mus IN=> //=.  
  move=> ? ? IH; case; first by move=> ->; left.
  by move=> IN; right; apply: (IH IN). 
  by apply: (H _ (or_introl erefl)). }
by rewrite predIC (predI_sub4 (S _ IN)).
by move=> mu H2; apply: (H mu (or_intror H2)).
Qed.

Let mu_trash'' := join_sm mu_top mu_trash.

Variable mu_trash''_wd : SM_wd mu_trash''.

Let mu_trash' := Inj.mk mu_trash''_wd.

Lemma frgnS_join_all' : 
    frgnBlocksSrc (join_all mu_trash' [seq frame_mu0 x | x <- mus])
  = frgnBlocksSrc mu_trash.
Proof.
move: (trash_fctnd_topS (trash_min trinv)).
move: (trash_fctnd_restS (trash_min trinv)).
elim: mus. 
move=> ctndr ctndt=> /=; extensionality b=> /=.
case fmu_tr: (frgnBlocksSrc mu_trash b)=> //=.
rewrite ctndt=> //.
by rewrite /in_mem /= fmu_tr andb_false_r.
move=> mu0 mus' IH /= ctndr ctndt; rewrite IH.
extensionality b; case fmu_tr: (frgnBlocksSrc mu_trash b)=> //=.
rewrite (ctndr mu0) /in_mem //; first by left.
by rewrite /in_mem /= fmu_tr andb_false_r.
by move=> mu H; apply: (ctndr mu); right.
by [].
Qed.

Lemma frgnS_join_all'_sub mus' : 
  (forall mu, List.In mu mus' -> List.In mu [seq frame_mu0 x | x <- mus]) -> 
    frgnBlocksSrc (join_all mu_trash' mus')
  = frgnBlocksSrc mu_trash.
Proof.
move=> H1.
cut (frgnBlocksSrc (join_all mu_trash' mus')
   = frgnBlocksSrc (join_all mu_trash' [seq frame_mu0 x | x <- mus])).
move=> ->.
apply: frgnS_join_all'.
elim: mus' H1=> /=.
move=> _; rewrite frgnS_join_all'.
move: (trash_fctnd_topS (trash_min trinv))=> S.
by rewrite predIC (predI_sub4 S).
move=> mu2 mus2 /= IH H.
rewrite IH. 
rewrite frgnS_join_all'.
move: (trash_fctnd_restS (trash_min trinv))=> /= S.
have IN: In (Inj.mu mu2) [seq (Inj.mu \o frame_mu0) x | x <- mus].
{ cut (In mu2 [seq frame_mu0 x | x <- mus]).
  move=> IN; clear - IN; elim: mus IN=> //=.  
  move=> ? ? IH; case; first by move=> ->; left.
  by move=> IN; right; apply: (IH IN). 
  by apply: (H _ (or_introl erefl)). }
by rewrite predIC (predI_sub4 (S _ IN)).
by move=> mu H2; apply: (H mu (or_intror H2)).
Qed.

Lemma frgnT_join_all : 
    frgnBlocksTgt (join_all mu_trash [seq frame_mu0 x | x <- mus])
  = frgnBlocksTgt mu_trash.
Proof.
move: (trash_fctnd_restT (trash_min trinv)).
elim: mus=> // mu0 mus' IH /= ctnd; rewrite IH.
extensionality b; case fmu_tr: (frgnBlocksTgt mu_trash b)=> //=.
rewrite (ctnd mu0) /in_mem //; first by left.
by rewrite /in_mem /= fmu_tr andb_false_r.
by move=> mu H; apply: (ctnd mu); right.
Qed.

Lemma frgnT_join_all_sub mus' : 
  (forall mu, List.In mu mus' -> List.In mu [seq frame_mu0 x | x <- mus]) -> 
    frgnBlocksTgt (join_all mu_trash mus')
  = frgnBlocksTgt mu_trash.
Proof.
move=> H1.
cut (frgnBlocksTgt (join_all mu_trash mus')
   = frgnBlocksTgt (join_all mu_trash [seq frame_mu0 x | x <- mus])).
move=> ->.
apply: frgnT_join_all.
elim: mus' H1=> /=.
by move=> _; rewrite frgnT_join_all.
move=> mu2 mus2 /= IH H.
rewrite IH. 
rewrite frgnT_join_all.
move: (trash_fctnd_restT (trash_min trinv))=> /= S.
have IN: In (Inj.mu mu2) [seq (Inj.mu \o frame_mu0) x | x <- mus].
{ cut (In mu2 [seq frame_mu0 x | x <- mus]).
  move=> IN; clear - IN; elim: mus IN=> //=.  
  move=> ? ? IH; case; first by move=> ->; left.
  by move=> IN; right; apply: (IH IN). 
  by apply: (H _ (or_introl erefl)). }
by rewrite predIC (predI_sub4 (S _ IN)).
by move=> mu H2; apply: (H mu (or_intror H2)).
Qed.

Lemma frgnT_join_all' : 
    frgnBlocksTgt (join_all mu_trash' [seq frame_mu0 x | x <- mus])
  = frgnBlocksTgt mu_trash.
Proof.
move: (trash_fctnd_topT (trash_min trinv)).
move: (trash_fctnd_restT (trash_min trinv)).
elim: mus. 
move=> ctndr ctndt=> /=; extensionality b=> /=.
case fmu_tr: (frgnBlocksTgt mu_trash b)=> //=.
rewrite ctndt=> //.
by rewrite /in_mem /= fmu_tr andb_false_r.
move=> mu0 mus' IH /= ctndr ctndt; rewrite IH.
extensionality b; case fmu_tr: (frgnBlocksTgt mu_trash b)=> //=.
rewrite (ctndr mu0) /in_mem //; first by left.
by rewrite /in_mem /= fmu_tr andb_false_r.
by move=> mu H; apply: (ctndr mu); right.
by [].
Qed.

Lemma frgnT_join_all'_sub mus' : 
  (forall mu, List.In mu mus' -> List.In mu [seq frame_mu0 x | x <- mus]) -> 
    frgnBlocksTgt (join_all mu_trash' mus')
  = frgnBlocksTgt mu_trash.
Proof.
move=> H1.
cut (frgnBlocksTgt (join_all mu_trash' mus')
   = frgnBlocksTgt (join_all mu_trash' [seq frame_mu0 x | x <- mus])).
move=> ->.
apply: frgnT_join_all'.
elim: mus' H1=> /=.
move=> _; rewrite frgnT_join_all'.
move: (trash_fctnd_topT (trash_min trinv))=> S.
by rewrite predIC (predI_sub4 S).
move=> mu2 mus2 /= IH H.
rewrite IH. 
rewrite frgnT_join_all'.
move: (trash_fctnd_restT (trash_min trinv))=> /= S.
have IN: In (Inj.mu mu2) [seq (Inj.mu \o frame_mu0) x | x <- mus].
{ cut (In mu2 [seq frame_mu0 x | x <- mus]).
  move=> IN; clear - IN; elim: mus IN=> //=.  
  move=> ? ? IH; case; first by move=> ->; left.
  by move=> IN; right; apply: (IH IN). 
  by apply: (H _ (or_introl erefl)). }
by rewrite predIC (predI_sub4 (S _ IN)).
by move=> mu H2; apply: (H mu (or_intror H2)).
Qed.

Lemma extS_join_all : 
    extBlocksSrc (join_all mu_trash [seq frame_mu0 x | x <- mus])
  = extBlocksSrc mu_trash.
Proof.
move: (trash_ctnd_restS (trash_min trinv)).
elim: mus=> // mu0 mus' IH /= ctnd; rewrite IH.
extensionality b; case fmu_tr: (extBlocksSrc mu_trash b)=> //=.
rewrite (ctnd mu0) /in_mem //; first by left.
by rewrite /in_mem /= fmu_tr andb_false_r.
by move=> mu H; apply: (ctnd mu); right.
Qed.

Lemma extS_join_all_sub mus' : 
  (forall mu, List.In mu mus' -> List.In mu [seq frame_mu0 x | x <- mus]) -> 
    extBlocksSrc (join_all mu_trash mus')
  = extBlocksSrc mu_trash.
Proof.
move=> H1.
cut (extBlocksSrc (join_all mu_trash mus')
   = extBlocksSrc (join_all mu_trash [seq frame_mu0 x | x <- mus])).
move=> ->.
apply: extS_join_all.
elim: mus' H1=> /=.
by move=> _; rewrite extS_join_all.
move=> mu2 mus2 /= IH H.
rewrite IH. 
rewrite extS_join_all.
move: (trash_ctnd_restS (trash_min trinv))=> /= S.
have IN: In (Inj.mu mu2) [seq (Inj.mu \o frame_mu0) x | x <- mus].
{ cut (In mu2 [seq frame_mu0 x | x <- mus]).
  move=> IN; clear - IN; elim: mus IN=> //=.  
  move=> ? ? IH; case; first by move=> ->; left.
  by move=> IN; right; apply: (IH IN). 
  by apply: (H _ (or_introl erefl)). }
by rewrite predIC (predI_sub4 (S _ IN)).
by move=> mu H2; apply: (H mu (or_intror H2)).
Qed.

Lemma extS_join_all' : 
    extBlocksSrc (join_all mu_trash' [seq frame_mu0 x | x <- mus])
  = extBlocksSrc mu_trash.
Proof.
move: (trash_ctnd_topS (trash_min trinv)).
move: (trash_ctnd_restS (trash_min trinv)).
elim: mus. 
move=> ctndr ctndt=> /=; extensionality b=> /=.
case fmu_tr: (extBlocksSrc mu_trash b)=> //=.
rewrite ctndt=> //.
by rewrite /in_mem /= fmu_tr andb_false_r.
move=> mu0 mus' IH /= ctndr ctndt; rewrite IH.
extensionality b; case fmu_tr: (extBlocksSrc mu_trash b)=> //=.
rewrite (ctndr mu0) /in_mem //; first by left.
by rewrite /in_mem /= fmu_tr andb_false_r.
by move=> mu H; apply: (ctndr mu); right.
by [].
Qed.

Lemma extS_join_all'_sub mus' : 
  (forall mu, List.In mu mus' -> List.In mu [seq frame_mu0 x | x <- mus]) -> 
    extBlocksSrc (join_all mu_trash' mus')
  = extBlocksSrc mu_trash.
Proof.
move=> H1.
cut (extBlocksSrc (join_all mu_trash' mus')
   = extBlocksSrc (join_all mu_trash' [seq frame_mu0 x | x <- mus])).
move=> ->.
apply: extS_join_all'.
elim: mus' H1=> /=.
move=> _; rewrite extS_join_all'.
move: (trash_ctnd_topS (trash_min trinv))=> S.
by rewrite predIC (predI_sub4 S).
move=> mu2 mus2 /= IH H.
rewrite IH. 
rewrite extS_join_all'.
move: (trash_ctnd_restS (trash_min trinv))=> /= S.
have IN: In (Inj.mu mu2) [seq (Inj.mu \o frame_mu0) x | x <- mus].
{ cut (In mu2 [seq frame_mu0 x | x <- mus]).
  move=> IN; clear - IN; elim: mus IN=> //=.  
  move=> ? ? IH; case; first by move=> ->; left.
  by move=> IN; right; apply: (IH IN). 
  by apply: (H _ (or_introl erefl)). }
by rewrite predIC (predI_sub4 (S _ IN)).
by move=> mu H2; apply: (H mu (or_intror H2)).
Qed.

Lemma extT_join_all : 
    extBlocksTgt (join_all mu_trash [seq frame_mu0 x | x <- mus])
  = extBlocksTgt mu_trash.
Proof.
move: (trash_ctnd_restT (trash_min trinv)).
elim: mus=> // mu0 mus' IH /= ctnd; rewrite IH.
extensionality b; case fmu_tr: (extBlocksTgt mu_trash b)=> //=.
rewrite (ctnd mu0) /in_mem //; first by left.
by rewrite /in_mem /= fmu_tr andb_false_r.
by move=> mu H; apply: (ctnd mu); right.
Qed.

Lemma extT_join_all_sub mus' : 
  (forall mu, List.In mu mus' -> List.In mu [seq frame_mu0 x | x <- mus]) -> 
    extBlocksTgt (join_all mu_trash mus')
  = extBlocksTgt mu_trash.
Proof.
move=> H1.
cut (extBlocksTgt (join_all mu_trash mus')
   = extBlocksTgt (join_all mu_trash [seq frame_mu0 x | x <- mus])).
move=> ->.
apply: extT_join_all.
elim: mus' H1=> /=.
by move=> _; rewrite extT_join_all.
move=> mu2 mus2 /= IH H.
rewrite IH. 
rewrite extT_join_all.
move: (trash_ctnd_restT (trash_min trinv))=> /= S.
have IN: In (Inj.mu mu2) [seq (Inj.mu \o frame_mu0) x | x <- mus].
{ cut (In mu2 [seq frame_mu0 x | x <- mus]).
  move=> IN; clear - IN; elim: mus IN=> //=.  
  move=> ? ? IH; case; first by move=> ->; left.
  by move=> IN; right; apply: (IH IN). 
  by apply: (H _ (or_introl erefl)). }
by rewrite predIC (predI_sub4 (S _ IN)).
by move=> mu H2; apply: (H mu (or_intror H2)).
Qed.

Lemma extT_join_all' : 
    extBlocksTgt (join_all mu_trash' [seq frame_mu0 x | x <- mus])
  = extBlocksTgt mu_trash.
Proof.
move: (trash_ctnd_topT (trash_min trinv)).
move: (trash_ctnd_restT (trash_min trinv)).
elim: mus. 
move=> ctndr ctndt=> /=; extensionality b=> /=.
case fmu_tr: (extBlocksTgt mu_trash b)=> //=.
rewrite ctndt=> //.
by rewrite /in_mem /= fmu_tr andb_false_r.
move=> mu0 mus' IH /= ctndr ctndt; rewrite IH.
extensionality b; case fmu_tr: (extBlocksTgt mu_trash b)=> //=.
rewrite (ctndr mu0) /in_mem //; first by left.
by rewrite /in_mem /= fmu_tr andb_false_r.
by move=> mu H; apply: (ctndr mu); right.
by [].
Qed.

Lemma extT_join_all'_sub mus' : 
  (forall mu, List.In mu mus' -> List.In mu [seq frame_mu0 x | x <- mus]) -> 
    extBlocksTgt (join_all mu_trash' mus')
  = extBlocksTgt mu_trash.
Proof.
move=> H1.
cut (extBlocksTgt (join_all mu_trash' mus')
   = extBlocksTgt (join_all mu_trash' [seq frame_mu0 x | x <- mus])).
move=> ->.
apply: extT_join_all'.
elim: mus' H1=> /=.
move=> _; rewrite extT_join_all'.
move: (trash_ctnd_topT (trash_min trinv))=> S.
by rewrite predIC (predI_sub4 S).
move=> mu2 mus2 /= IH H.
rewrite IH. 
rewrite extT_join_all'.
move: (trash_ctnd_restT (trash_min trinv))=> /= S.
have IN: In (Inj.mu mu2) [seq (Inj.mu \o frame_mu0) x | x <- mus].
{ cut (In mu2 [seq frame_mu0 x | x <- mus]).
  move=> IN; clear - IN; elim: mus IN=> //=.  
  move=> ? ? IH; case; first by move=> ->; left.
  by move=> IN; right; apply: (IH IN). 
  by apply: (H _ (or_introl erefl)). }
by rewrite predIC (predI_sub4 (S _ IN)).
by move=> mu H2; apply: (H mu (or_intror H2)).
Qed.

Lemma extern_of_trash_join_all : 
    extern_of (join_all mu_trash [seq frame_mu0 x | x <- mus])
  = extern_of mu_trash.
Proof.
extensionality b.
move: (trash_eincr_rest (trash_min trinv)).
elim: mus=> // mu0 mus' IH /= eincr.
rewrite /join2.
rewrite IH.
case eOf0: (extern_of mu0 b)=> [[x y]|].
case eOftr: (extern_of mu_trash b)=> [[x' y']|//].
rewrite (eincr mu0 (or_introl erefl) _ _ _ eOftr) in eOf0.
by case: eOf0=> -> ->; rewrite Pos.eqb_refl Zeq_bool_refl.
case eOftr: (extern_of mu_trash b)=> [[x' y']|//].
by move: (eincr mu0 (or_introl erefl) _ _ _ eOftr); rewrite eOf0.
by move=> mu H; apply: (eincr mu (or_intror H)).
Qed.

Lemma extern_of_trash_join_all_sub mus' :
  (forall mu, List.In mu mus' -> List.In mu mus) -> 
    extern_of (join_all mu_trash [seq frame_mu0 x | x <- mus'])
  = extern_of mu_trash.
Proof.
move=> S. 
suff: extern_of (join_all mu_trash [seq frame_mu0 x | x <- mus']) 
    = extern_of (join_all mu_trash [seq frame_mu0 x | x <- mus]).
move=> ->; apply: extern_of_trash_join_all.
elim EQ: mus' S=> [|mu0 mus''] /=.
by move=> S; rewrite extern_of_trash_join_all.
move=> /= IH H; rewrite IH.
rewrite extern_of_trash_join_all.
rewrite /join2; extensionality b.
move: (trash_eincr_rest (trash_min trinv)).
move: (H mu0 (or_introl erefl))=> IN0.
have IN: 
  In ((Inj.mu \o frame_mu0) mu0) [seq (Inj.mu \o frame_mu0) x0 | x0 <- mus].
{ elim: mus IN0=> //= ? ? IH'; case; first by move=> ->; left.
  by move=> H'; right; apply: (IH' H'). }
move=> eincr.
case eOf0: (extern_of mu0 b)=> [[x y]|].
case eOftr: (extern_of mu_trash b)=> [[x' y']|//].
move: (eincr mu0 IN _ _ _ eOftr); rewrite eOf0; case=> -> ->.
by rewrite Pos.eqb_refl Zeq_bool_refl.
case eOftr: (extern_of mu_trash b)=> [[x' y']|//].
by move: (eincr mu0 IN _ _ _ eOftr); rewrite eOf0.
by move=> mu IN; apply: H; right.
Qed.

Lemma extern_of_trash_join_all' : 
    extern_of (join_all mu_trash' [seq frame_mu0 x | x <- mus])
  = extern_of mu_trash.
Proof.
extensionality b.
move: (trash_eincr_top (trash_min trinv)).
move: (trash_eincr_rest (trash_min trinv)).
elim: mus. 
move=> eincr_r eincr_t; rewrite /= /join2.
case eOf0: (extern_of mu_top b)=> [[x y]|].
case eOftr: (extern_of mu_trash b)=> [[x' y']|//].
rewrite (eincr_t _ _ _ eOftr) in eOf0.
by case: eOf0=> -> ->; rewrite Pos.eqb_refl Zeq_bool_refl.
case eOftr: (extern_of mu_trash b)=> [[x' y']|//].
by move: (eincr_t _ _ _ eOftr); rewrite eOf0.
move=> mu0 mus' IH eincr_r eincr_t; rewrite /= /join2.
rewrite IH.
case eOf0: (extern_of mu0 b)=> [[x y]|].
case eOftr: (extern_of mu_trash b)=> [[x' y']|//].
rewrite (eincr_r mu0 (or_introl erefl) _ _ _ eOftr) in eOf0.
by case: eOf0=> -> ->; rewrite Pos.eqb_refl Zeq_bool_refl.
case eOftr: (extern_of mu_trash b)=> [[x' y']|//].
by move: (eincr_r mu0 (or_introl erefl) _ _ _ eOftr); rewrite eOf0.
by move=> mu H; apply: (eincr_r mu (or_intror H)).
by [].
Qed.

Lemma join2_extern_top_trash :
    join2 (extern_of mu_top) (extern_of mu_trash) 
  = extern_of mu_trash.
Proof.
rewrite join2C join2_inject_incr=> //.
by apply: (trash_eincr_top (trash_min trinv)).
Qed.

Lemma join2_extern_mu0_trash (mu0 : Inj.t) :
  List.In mu0 [seq frame_mu0 x | x <- mus] -> 
    join2 (extern_of mu0) (extern_of mu_trash) 
  = extern_of mu_trash.
Proof.
move=> IN; rewrite join2C join2_inject_incr=> //.
apply: (trash_eincr_rest (trash_min trinv)).
elim: mus IN=> // a mus' /= IH; case; first by move=> ->; left.
by move=> IN; right; apply: IH.
Qed.

Lemma extern_of_trash_join_all'_sub mus' :
  (forall mu, List.In mu mus' -> List.In mu mus) -> 
    extern_of (join_all mu_trash' [seq frame_mu0 x | x <- mus'])
  = extern_of mu_trash.
Proof.
move=> S. 
suff: extern_of (join_all mu_trash' [seq frame_mu0 x | x <- mus']) 
    = extern_of (join_all mu_trash' [seq frame_mu0 x | x <- mus]).
move=> ->; apply: extern_of_trash_join_all'.
elim EQ: mus' S=> [|mu0 mus''] /=.
move=> S; rewrite extern_of_trash_join_all'.
by apply: join2_extern_top_trash.
move=> /= IH H; rewrite IH.
rewrite extern_of_trash_join_all'.
rewrite /join2; extensionality b.
move: (trash_eincr_rest (trash_min trinv)).
move: (H mu0 (or_introl erefl))=> IN0.
have IN: 
  In ((Inj.mu \o frame_mu0) mu0) [seq (Inj.mu \o frame_mu0) x0 | x0 <- mus].
{ elim: mus IN0=> //= ? ? IH'; case; first by move=> ->; left.
  by move=> H'; right; apply: (IH' H'). }
move=> eincr.
case eOf0: (extern_of mu0 b)=> [[x y]|].
case eOftr: (extern_of mu_trash b)=> [[x' y']|//].
move: (eincr mu0 IN _ _ _ eOftr); rewrite eOf0; case=> -> ->.
by rewrite Pos.eqb_refl Zeq_bool_refl.
case eOftr: (extern_of mu_trash b)=> [[x' y']|//].
by move: (eincr mu0 IN _ _ _ eOftr); rewrite eOf0.
by move=> mu IN; apply: H; right.
Qed.

Lemma as_inj_shift b b' d' mus' :
  All [eta DisjointLS mu_top] [seq (Inj.mu \o frame_mu0) x | x <- mus] -> 
  (forall mu, List.In mu mus' -> List.In mu mus) -> 
  as_inj (join_sm mu_top 
    (join_all mu_trash [seq frame_mu0 x | x <- mus'])) b = Some (b', d') ->
  as_inj (join_all mu_trash' 
    [seq frame_mu0 x | x <- mus']) b = Some (b', d').
Proof.
move=> D.
rewrite /as_inj /= => H.

have disj: All [eta DisjointLS mu_top] 
  [seq Inj.mu x0 | x0 <- [seq frame_mu0 x0 | x0 <- mus']].
{ move: D; rewrite -!map_comp /= /comp.
move: H; elim: mus'=> //= a mus' IH IN; split=> //.
have IN': In a mus.
{ by apply: IN; left. }
clear - IN' D; elim: mus D IN'=> // b mus' /= IH []D A.
case; first by move=> <-.
by move=> IN; apply: IH=> //.
by apply: IH; first by move=> mu IN'; apply: (IN _ (or_intror IN')). }

rewrite extern_of_trash_join_all_sub //.
rewrite extern_of_trash_join_all'_sub //.
rewrite join2_extern_top_trash.
rewrite /join.
case e: (extern_of _ _)=> //.
case l: (local_of _ _)=> [[x y]|].
case=> <- <-.
rewrite join_all_shift_local_ofE //. 
by rewrite /join l.

move=> I; rewrite join_all_shift_local_ofE //. 
by rewrite /join l I.
Qed.

Lemma as_inj_shift_mu_trash b b' d' mus' :
  DisjointLS mu_top mu_trash -> 
  All [eta DisjointLS mu_top] [seq (Inj.mu \o frame_mu0) x | x <- mus] -> 
  (forall mu, List.In mu mus' -> List.In mu mus) -> 
  as_inj (join_all mu_trash [seq frame_mu0 x | x <- mus']) b = Some (b', d') ->
  as_inj (join_all mu_trash' 
    [seq frame_mu0 x | x <- mus']) b = Some (b', d').
Proof.
move=> DTT D H I; apply: as_inj_shift=> //.
move: I; rewrite /as_inj /join /=.
rewrite extern_of_trash_join_all_sub //.
rewrite join2_extern_top_trash.
case e: (extern_of _ _)=> [[x y]|] //.
rewrite join_com /join; first by move=> ->.
clear - D H DTT; elim: mus' D H DTT=> //=.
by move=> _ _; move/DisjointLS_disjoint.
move=> a mus0 IH D IN DTT.
have D': DisjointLS mu_top a.
{ have IN': In a mus by apply: (IN _ (or_introl erefl)).
  clear - D IN'; elim: mus D IN'=> //.
  move=> a0 mus0 /= IH []D D2; case; first by move=> <-.
  by move=> IN; apply: IH. }
move=> b; case: (DisjointLS_disjoint D' b); first by move=> ->; left.
move=> H.
have IN' mu: In mu mus0 -> In mu mus.
{ by move=> ?; apply: IN; right. }
case: (IH D IN' DTT b); first by move=> ->; left.
by right; rewrite /join b0 H.
Qed.

Lemma as_inj_shift_mu0_trash b b' d' mus' (mu0 : Inj.t) :
  All [eta DisjointLS mu_top] [seq (Inj.mu \o frame_mu0) x | x <- mus] -> 
  (forall mu, List.In mu mus' -> List.In mu mus) -> 
  Consistent mu_top (join_all mu_trash [seq frame_mu0 x | x <- mus']) -> 
  SM_wd (join_all mu_trash [seq frame_mu0 x | x <- mus']) ->
  In mu0 [seq frame_mu0 x | x <- mus] -> 
  as_inj (join_sm mu0 (join_all mu_trash [seq frame_mu0 x | x <- mus'])) b 
    = Some (b', d') ->
  as_inj (join_sm mu0 (join_all mu_trash' [seq frame_mu0 x | x <- mus'])) b 
    = Some (b', d').
Proof.
move=> D H CC WD mu0_in I. 
move: I; rewrite /as_inj /join /=.
rewrite extern_of_trash_join_all_sub //.
rewrite join2_extern_mu0_trash //.
rewrite extern_of_trash_join_all'_sub //.
rewrite join2_extern_mu0_trash //.
case e: (extern_of _ _)=> [[x y]|] //.
rewrite /join.
case l: (local_of _ _)=> [[x' y']|] //.
rewrite join_all_shift_local_ofE /join.
case lT: (local_of mu_top b)=> [[x'' y'']|//].
have asInj: as_inj mu_top b = Some (x'',y'').
{ by rewrite /as_inj /join (local_some_extern_none lT). }
move=> lA.
have asInjA: as_inj (join_all mu_trash 
  [seq frame_mu0 x | x <- mus']) b = Some (b', d').
{ by apply: (local_in_all _ _ _ _ _ lA). }
by case: (CC _ _ _ _ _ asInj asInjA)=> -> ->.
clear - H D; elim: mus' H D=> // a mus0 IH /= IN H.
have IN': In a mus by apply: (IN _ (or_introl erefl)).
have D': DisjointLS mu_top a.
{ clear - H IN'; elim: mus H IN'=> //.
  move=> a0 mus0 /= IH []D D2; case; first by move=> <-.
  by move=> IN; apply: IH. }
split=> //.
apply: IH; first by move=> ? H2; apply: (IN _ (or_intror H2)).
by move: H; rewrite !map_comp; apply.
Qed.

End trash_inv_lems.

Section trash_minimal_lems.

Context (mu_trash : Inj.t) mu_top mus
  (trmin : trash_minimal mu_trash mu_top mus).

Lemma trash_minimal_sub mus' : 
  (forall mu, In mu mus' -> In mu mus) -> 
  trash_minimal mu_trash mu_top mus'.
Proof.
move=> IN; elim: mus' IN.
by case: trmin=> A B C D E F G H I J IN; apply: Build_trash_minimal.
move=> a mus' /= IH IN.
have IN': (forall mu, In mu mus' -> In mu mus).
{ by move=> mu H; apply: (IN _ (or_intror H)). }
case: trmin=> A B C D E F G H I J; apply: Build_trash_minimal=> //=.
move=> mu; case.
by move=> <-; apply: (C _ (IN _ (or_introl erefl))).
by move=> AA; apply: (trash_ctnd_restS (IH IN') AA).
move=> mu; case.
by move=> <-; apply: (D _ (IN _ (or_introl erefl))).
by move=> AA; apply: (trash_ctnd_restT (IH IN') AA).
move=> mu; case.
by move=> <-; apply: (G _ (IN _ (or_introl erefl))).
by move=> AA; apply: (trash_fctnd_restS (IH IN') AA).
move=> mu; case.
by move=> <-; apply: (H _ (IN _ (or_introl erefl))).
by move=> AA; apply: (trash_fctnd_restT (IH IN') AA).
move=> mu; case.
by move=> <-; apply: (J _ (IN _ (or_introl erefl))).
by move=> AA; apply: (trash_eincr_rest (IH IN') AA).
Qed.

Lemma trash_minimal_join_sm mu_new :
  List.In mu_new mus -> 
  trash_minimal (join_sm mu_new mu_trash) mu_top mus.
Proof.
move=> HIn; case: trmin.
move=> ES ET ErS ErT FS FT FrS FrT eincrT eincrR.
apply: Build_trash_minimal.
by rewrite join_sm_extSrc predIC predI_sub4=> //; apply: (ErS _ HIn).
by rewrite join_sm_extTgt predIC predI_sub4=> //; apply: (ErT _ HIn).
by rewrite join_sm_extSrc predIC predI_sub4=> //; apply: (ErS _ HIn).
by rewrite join_sm_extTgt predIC predI_sub4=> //; apply: (ErT _ HIn).
by rewrite join_sm_frgnSrc predIC predI_sub4=> //; apply: (FrS _ HIn).
by rewrite join_sm_frgnTgt predIC predI_sub4=> //; apply: (FrT _ HIn).
by rewrite join_sm_frgnSrc predIC predI_sub4=> //; apply: (FrS _ HIn).
by rewrite join_sm_frgnTgt predIC predI_sub4=> //; apply: (FrT _ HIn).
by rewrite /= join2C join2_inject_incr //; apply: (eincrR _ HIn).
by rewrite /= join2C join2_inject_incr //; apply: (eincrR _ HIn).
Qed.

Lemma trash_minimal_join_sm_top :
  trash_minimal (join_sm mu_top mu_trash) mu_top mus.
Proof.
case: trmin.
move=> ES ET ErS ErT FS FT FrS FrT eincrT eincrR.
apply: Build_trash_minimal.
by rewrite join_sm_extSrc predIC predI_sub4.
by rewrite join_sm_extTgt predIC predI_sub4.
by rewrite join_sm_extSrc predIC predI_sub4.
by rewrite join_sm_extTgt predIC predI_sub4.
by rewrite join_sm_frgnSrc predIC predI_sub4.
by rewrite join_sm_frgnTgt predIC predI_sub4.
by rewrite join_sm_frgnSrc predIC predI_sub4.
by rewrite join_sm_frgnTgt predIC predI_sub4.
by rewrite /= join2C join2_inject_incr.
by rewrite /= join2C join2_inject_incr.
Qed.

Lemma trash_minimal_replace_top mu_new :
  List.In mu_new mus -> 
  trash_minimal mu_trash mu_new mus.
Proof.
move=> HIn; case: trmin.
move=> ES ET ErS ErT FS FT FrS FrT eincrT eincrR.
apply: Build_trash_minimal=> //.
by apply: (ErS _ HIn).
by apply: (ErT _ HIn).
by apply: (FrS _ HIn).
by apply: (FrT _ HIn).
by apply: (eincrR _ HIn).
Qed.

Lemma trash_minimal_tail :
  trash_minimal mu_trash mu_top (tl mus).
Proof.
case: trmin.
move=> ES ET ErS ErT FS FT FrS FrT eincrT eincrR.
have InIn mu:
  In mu (tl mus) -> 
  In mu mus.
{ by elim: mus mu=> // a mus' /= IH mu IN; right. }
apply: Build_trash_minimal=> //.
by move=> ?; move/InIn; apply: ErS.
by move=> ?; move/InIn; apply: ErT.
by move=> ?; move/InIn; apply: FrS.
by move=> ?; move/InIn; apply: FrT.
by move=> ?; move/InIn; apply: eincrR.
Qed.

End trash_minimal_lems.

Section trash_minimal_ret_lems.

Context (mu_trash : Inj.t) mu_top mu0 (mus : seq.seq Inj.t)
  (trmin : trash_minimal mu_trash mu_top 
           [seq Inj.mu x | x <- [:: mu0 & mus]])
  (joinwd : SM_wd (join_sm mu_top mu_trash)).

Lemma trash_minimal_return :
  trash_minimal (join_sm mu_top mu_trash) mu0 
  [seq Inj.mu x | x <- mus].
Proof.
move: (trash_minimal_join_sm_top trmin)=> H.
have H': trash_minimal (Inj.mk joinwd) mu_top
         [seq Inj.mu x | x <- mu0 :: mus].
{ by apply: H. }
move: (trash_minimal_replace_top H'); move/(_ mu0 (or_introl erefl)).
by move/trash_minimal_tail; apply.
Qed.

End trash_minimal_ret_lems.

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

Lemma trash_inv_sub (mu_trash : Inj.t) mu_top
      (mus mus' : seq.seq frame_pkg) m1 m2 : 
  (forall mu, In mu mus' -> In mu mus) -> 
  trash_inv mu_trash mu_top mus m1 m2 -> 
  trash_inv mu_trash mu_top mus' m1 m2.
Proof.
move=> IN; case=> A B C D E F M.
have IN0: forall mu, In mu [seq (Inj.mu \o frame_mu0) x | x <- mus']
                  -> In mu [seq (Inj.mu \o frame_mu0) x | x <- mus].
{ move=> mu IN0; clear - IN IN0; elim: mus' IN IN0=> // a mus' IH /=.
  move=> IN; case.   
  move=> eq; move: (IN _ (or_introl erefl)); rewrite -eq.
  move=> IN0; clear - IN0.
  elim: mus IN0=> // a0 mus' IH /=; case; first by move=> ->; left.
  by move=> IN0; right; apply: IH.
  move=> IN0; apply: IH=> //.
  by move=> mu0 IN1; apply: (IN _ (or_intror IN1)). }
apply: Build_trash_inv=> //.
apply: (All_listsub 
          (l:=(mu_top :: [seq (Inj.mu \o frame_mu0) x | x <- mus])))=>//.
move=> a /=; case; first by move=> ->; left.
by move=> IN'; right; apply: (IN0 _ IN').
apply: (All_listsub 
          (l:=(mu_top :: [seq (Inj.mu \o frame_mu0) x | x <- mus])))=>//.
move=> a /=; case; first by move=> ->; left.
by move=> IN'; right; apply: (IN0 _ IN').
apply: (All_listsub 
          (l:=(mu_top :: [seq (Inj.mu \o frame_mu0) x | x <- mus])))=>//.
move=> a /=; case; first by move=> ->; left.
by move=> IN'; right; apply: (IN0 _ IN').
by apply: (trash_minimal_sub M).
Qed.

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

Record head_inv cd mu_trash (mu : Inj.t) mus m1 m2 : Type :=
  { head_match : (sims c.(i)).(match_state) cd mu 
                 c.(Core.c) m1 (cast'' pf d.(Core.c)) m2 
  ; head_rel   : All (rel_inv_pred mu) mus 
  ; head_vis   : vis_inv c mu 
  ; head_ctndS : frgnS_contained mu_trash mu mus 
  ; head_ctndT : frgnT_contained mu_trash mu mus 
  ; head_mapdS : frgnS_mapped mu_trash mu mus 
  ; head_ctnsS : if mus is [:: mu' & mus] then 
                   {subset (sharedSrc mu') <= sharedSrc mu} 
                 else True
  ; head_ctnsT : if mus is [:: mu' & mus] then 
                   {subset (sharedTgt mu') <= sharedTgt mu} 
                 else True }.

End head_inv.

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

Section contain_lems2.

Context mu_trash (mu : frame_pkg) mus (ctndS : frgnS_contained mu_trash mu mus).

Variables args1 args2 : list val.

Let j := as_inj mu.
Let domS := DomSrc mu.
Let domT := DomTgt mu.
Let frgnS := exportedSrc mu args1.
Let frgnT := exportedTgt mu args2.

Variable vinj : Forall2 (val_inject (restrict j (sharedSrc mu))) args1 args2.

Variable defs : vals_def args1.

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
case: (getBlocks_frgnpubT vinj defs D).
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

Section rel_inv_init_lems.

Context (mu : Inj.t) pkg (rinv : rel_inv_pred mu pkg).

Lemma relinv_init args1 args2 : 
  val_list_inject (restrict (as_inj mu) (sharedSrc mu)) args1 args2 -> 
  rel_inv_pred 
    (initial_SM 
      (DomSrc mu) (DomTgt mu) 
      (exportedSrc mu args1) (exportedTgt mu args2) (as_inj mu)) pkg.
Proof.
move=> vinj.
apply: Build_rel_inv. 
split; first by rewrite initial_SM_as_inj; case: rinv; case.
split=> b; rewrite /DomSrc /DomTgt /= => H1.
by case: rinv; case=> _ []H2 H3 _ _; apply: H2.
by case: rinv; case=> _ []H2 H3 _ _; apply: H3.
split. 
rewrite initial_SM_as_inj.
case: rinv=> _ []H1 ? _ b1 b2 d H2 H3.
by apply: (H1 _ _ _ H2 H3).
split; rewrite /DomSrc /DomTgt /=.
by case: rinv=> _; case=> _ []H1 H2 _; apply: H1.
by case: rinv=> _; case=> _ []H1 H2 _; apply: H2.

move: (val_list_inject_forall_inject _ _ _ vinj)=> vinj'.
case: rinv=> _ _ []d1 d2 sub frgn cons.
apply: Build_disjinv.
by rewrite /= predI01.
by rewrite /= predI01.
move=> b; rewrite /in_mem /= /in_mem /=; move/andP=> []H1 H2.
rewrite /exportedSrc in H1; case: (orP H1)=> H3.
case: (getBlocks_inject _ _ _ vinj' _ H3)=> b' []d []res get2.
case: (restrictD_Some _ _ _ _ _ res)=> asInj shrdS.
rewrite sharedSrc_iff_frgnpub in shrdS.
case: (orP shrdS)=> H4.
by apply: sub; rewrite /in_mem /= /in_mem /=; apply/andP; split.
move: (pubsrc_sub_locsrc H4); rewrite /in_mem /= => l.
move: d1; rewrite DisjointC; move/DisjointLS_E1.
by move/(_ _ l); rewrite H2.
by apply: Inj_wd.
rewrite sharedSrc_iff_frgnpub in H3.
case: (orP H3)=> H4.
by apply: sub; rewrite /in_mem /= /in_mem /=; apply/andP; split.
move: (pubsrc_sub_locsrc H4); rewrite /in_mem /= => l.
move: d1; rewrite DisjointC; move/DisjointLS_E1.
by move/(_ _ l); rewrite H2.
by apply: Inj_wd.
move=> b1 b2 d /=.
case e: (exportedSrc _ _ _)=> //.
move=> H1; rewrite /in_mem /=; case/orP=> H2.
apply: frgn.
move: e; rewrite /exportedSrc; case/orP.
case/(getBlocks_frgnpubS vinj').
move/pubsrc_sub_locsrc; rewrite /in_mem /= => l.
move: d1; rewrite DisjointC; move/DisjointLS_E1.
by move/(_ _ l); rewrite H2.
case/frgnSrc; first by apply: Inj_wd.
move=> ? []? []fOf _.
by move: (foreign_in_all _ _ _ _ fOf); rewrite H1; case=> -> ->.
rewrite sharedSrc_iff_frgnpub.
case/orP=> H3.
case: (frgnSrc _ _ _ H3); first by apply: Inj_wd.
move=> ? []? []fOf _.
by move: (foreign_in_all _ _ _ _ fOf); rewrite H1; case=> -> ->.
move: (pubsrc_sub_locsrc H3); rewrite /in_mem /= => l.
move: d1; rewrite DisjointC; move/DisjointLS_E1.
by move/(_ _ l); rewrite H2.
by apply: Inj_wd.
by apply/orP; rewrite /in_mem /= H2; left.
apply: frgn.

move: e; rewrite /exportedSrc; case/orP.
case/(getBlocks_frgnpubS vinj').
move/pubsrc_sub_locsrc; rewrite /in_mem /= => l.
have eOf: extern_of mu b1 = None.
{ case e: (extern_of mu b1)=> //[[? ?]].
  case: (extern_DomRng _ (Inj_wd _) _ _ _ e).
  by move/(extBlocksSrc_locBlocksSrc _ (Inj_wd _) _); rewrite l. }  
rewrite /as_inj /join eOf in H1.
case: (local_DomRng _ (Inj_wd _) _ _ _ H1)=> _ lT.
move: d2; rewrite DisjointC; move/DisjointLT_E1; move/(_ _ lT)=> H3.
by rewrite H3 in H2.
case/frgnSrc; first by apply: Inj_wd.
move=> ? []? []fOf _.
by move: (foreign_in_all _ _ _ _ fOf); rewrite H1; case=> -> ->.
rewrite sharedSrc_iff_frgnpub.
case/orP=> H3.
case: (frgnSrc _ _ _ H3); first by apply: Inj_wd.
move=> ? []? []fOf _.
by move: (foreign_in_all _ _ _ _ fOf); rewrite H1; case=> -> ->.
move: (pubsrc_sub_locsrc H3); rewrite /in_mem /= => l.
have eOf: extern_of mu b1 = None.
{ case e: (extern_of mu b1)=> //[[? ?]].
  case: (extern_DomRng _ (Inj_wd _) _ _ _ e).
  by move/(extBlocksSrc_locBlocksSrc _ (Inj_wd _) _); rewrite l. }
rewrite /as_inj /join eOf in H1.
case: (local_DomRng _ (Inj_wd _) _ _ _ H1)=> _ lT.
move: d2; rewrite DisjointC; move/DisjointLT_E1; move/(_ _ lT)=> H4.
by rewrite H4 in H2.
by apply: Inj_wd.
by apply/orP; rewrite /in_mem /= H2; right.
move=> b1 b2 b2' d3 d3' H1; rewrite initial_SM_as_inj=> H2.
by apply: (cons _ _ _ _ _ H1 H2).
Qed.

End rel_inv_init_lems.

Section head_inv_lems.

Context c d pf cd mu_trash mu mus m1 m2 
        (inv : @head_inv c d pf cd mu_trash mu mus m1 m2).

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
  at_external (sem (cores_S (Core.i c))) (Core.c c) 
    = Some (ef,sig,args) -> 
  Mem.inject (as_inj mu) m1 m2.
Proof.
move=> atext; move: (head_match inv)=> mtch.
by case: (core_at_external (sims (Core.i c)) _ _ _ _ _ _ mtch atext).
Qed.

End head_inv_lems.

Import seq.

Fixpoint frame_all mu_trash (mus : seq frame_pkg) m1 m2 s1 s2 :=
  match mus, s1, s2 with
    | Build_frame_pkg mu0 m10 m20 _ :: mus', c :: s1', d :: s2' => 
      [/\ exists (pf : c.(Core.i)=d.(Core.i)) cd0,
          exists e1 ef_sig1 vals1,
          exists e2 ef_sig2 vals2, 
            [/\ @frame_inv c d pf cd0 mu0 
                  m10 m1 e1 ef_sig1 vals1 m20 m2 e2 ef_sig2 vals2
              , frgnS_contained mu_trash mu0 mus' 
              , frgnT_contained mu_trash mu0 mus' 
              , frgnS_mapped mu_trash mu0 mus' 
              , if mus' is [:: mu' & mus''] then 
                  {subset (sharedSrc mu') <= sharedSrc mu0}
                else True
              & if mus' is [:: mu' & mus''] then 
                  {subset (sharedTgt mu') <= sharedTgt mu0}
                else True]
        & frame_all mu_trash mus' m1 m2 s1' s2']
    | nil,nil,nil => True
    | _,_,_ => False
  end.

Definition tail_inv mu_trash mus s1 s2 m1 m2 :=
  [/\ All2 (rel_inv_pred \o frame_mu0) mus 
    & frame_all mu_trash mus m1 m2 s1 s2].

Lemma frame_all_inv mu_trash mu0 m10 m20 x mus m1 m2 s1 s2 :
  frame_all mu_trash (@Build_frame_pkg mu0 m10 m20 x :: mus) 
            m1 m2 s1 s2 -> 
  exists c s1' d s2',
    [/\ s1 = c :: s1'
      , s2 = d :: s2' 
      & exists (pf : c.(Core.i)=d.(Core.i)) cd0,
        exists e1 ef_sig1 vals1,
        exists e2 ef_sig2 vals2, 
          [/\ @frame_inv c d pf cd0 mu0 
                m10 m1 e1 ef_sig1 vals1 m20 m2 e2 ef_sig2 vals2
            , frgnS_contained mu_trash mu0 mus 
            , frgnT_contained mu_trash mu0 mus 
            , frgnS_mapped mu_trash mu0 mus 
            , if mus is [:: mu' & mus'] then 
                {subset (sharedSrc mu') <= sharedSrc mu0}
              else True
            , if mus is [:: mu' & mus'] then 
                {subset (sharedTgt mu') <= sharedTgt mu0}
              else True
            & frame_all mu_trash mus m1 m2 s1' s2']].
Proof.
case: s1=> // c s1'; case: s2=> // d s2' /=.
move=> [][]pf => [][]cd []ef1 []sig1 []vals1 []ef2 []sig2 []vals2. 
case=> A B C D E F.
exists c, s1', d, s2'; split=> //.
by exists pf, cd, ef1, sig1, vals1, ef2, sig2, vals2; split.
Qed.

Lemma frame_all_match mu_trash mu0 m10 m20 x mus m1 m2 s1 s2 :
  frame_all mu_trash (@Build_frame_pkg mu0 m10 m20 x :: mus) 
            m1 m2 s1 s2 -> 
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
by exists pf, cd; case: A.
Qed.

Lemma frame_all_fwd1 mu_trash pkg mus m1 m2 s1 s2 :
  frame_all mu_trash (pkg :: mus) m1 m2 s1 s2 -> 
  mem_forward pkg.(frame_m10) m1.
Proof.
case: pkg=> ? ? ? ?.
move/frame_all_inv=> []? []? []? []? []? ? []? []? []? []? []? []? []? []? [].
by case.
Qed.

Lemma frame_all_fwd2 mu_trash pkg mus m1 m2 s1 s2 :
  frame_all mu_trash (pkg :: mus) m1 m2 s1 s2 -> 
  mem_forward pkg.(frame_m20) m2.
Proof.
case: pkg=> ? ? ? ?.
move/frame_all_inv=> []? []? []? []? []? ? []? []? []? []? []? []? []? []? [].
by case.
Qed.

Lemma frame_all_tail mu_trash pkg mus m1 m2 s1 s2 :
  frame_all mu_trash (pkg :: mus) m1 m2 s1 s2 -> 
  frame_all mu_trash mus m1 m2 (STACK.pop s1) (STACK.pop s2).
Proof.
case: pkg=> ? ? ? ?.
move/frame_all_inv=> []? []? []? []? []-> ->. 
by move=> []? []? []? []? []? []? []? []? [] _.
Qed.

Section frame_all_lems.

Context mu_trash mus m1 m2 s1 s2 
        (frameall : frame_all mu_trash mus m1 m2 s1 s2).

Lemma frame_all_globs :
  All (fun mu0 => forall b, isGlobalBlock my_ge b -> frgnBlocksSrc mu0 b)  
    $ map (Inj.mu \o frame_mu0) mus.
Proof.
move: frameall.
move: m1 m2 s1 s2; elim: mus=> //; case=> mu' ? ? ? mus' IH m1' m2' s1' s2' A.
move: (frame_all_inv A)=> []c []s1'' []d []s2'' []_ _.
move=> []pf []cd []? []? []? []? []? []? []B XS MS XT Y Y' C.
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
move=> []pf []cd []? []? []? []? []? []? []B XS MS XT Y Y' C.
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
move=> []pf []cd []? []? []? []? []? []? []B XS MS XT Y Y' C.
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

Lemma tail_inv_inv mu_trash mu0 m10 m20 x mus s1 s2 m1 m2 :
  tail_inv mu_trash (@Build_frame_pkg mu0 m10 m20 x :: mus) 
           s1 s2 m1 m2 -> 
  exists c s1' d s2',
    [/\ s1 = c :: s1'
      , s2 = d :: s2' 
      , (exists (pf : c.(Core.i)=d.(Core.i)) cd0,
         exists e1 ef_sig1 vals1,
         exists e2 ef_sig2 vals2, 
           @frame_inv c d pf cd0 mu0 
           m10 m1 e1 ef_sig1 vals1 m20 m2 e2 ef_sig2 vals2)
       & tail_inv mu_trash mus (STACK.pop s1) (STACK.pop s2) m1 m2].
Proof.
case; case=> H1 H2; move/frame_all_inv=> []c []s1' []d []s2' []B C.
move=> []pf []cd []ef1 []sig1 []vals1 []ef2 []sig2 []vals2 []D E.
exists c,s1',d,s2'; split=> //.
by exists pf,cd,ef1,sig1,vals1,ef2,sig2,vals2.
by split=> //; rewrite B C.
Qed.

Lemma tail_inv_match mu_trash mu0 m10 m20 x mus s1 s2 m1 m2 :
  tail_inv mu_trash (@Build_frame_pkg mu0 m10 m20 x :: mus) 
           s1 s2 m1 m2 -> 
  exists c s1' d s2',
    [/\ s1 = c :: s1'
      , s2 = d :: s2' 
      & exists (pf : c.(Core.i)=d.(Core.i)) cd0,
        (sims c.(Core.i)).(match_state) cd0 mu0 
        c.(Core.c) m10 (cast'' pf d.(Core.c)) m20].
Proof. by move=> []_; move/frame_all_match. Qed.

Section tail_inv_lems.

Context mu_trash mus s1 s2 m1 m2 
        (tlinv : tail_inv mu_trash mus s1 s2 m1 m2).

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
  (atext1 : at_external (sem (cores_S (Core.i c))) (Core.c c) 
            = Some (e,sig,args1))
  (atext2 : at_external (sem (cores_T (Core.i c))) 
            (cast'' pf (Core.c d)) = Some (e,sig,args2))
  (inj : Mem.inject (as_inj mu) m1 m2)
  (vals_inj : Forall2 (val_inject (restrict (as_inj mu) (vis mu))) args1 args2) 
  (inv : @head_inv c d pf cd mu_trash mu mus m1 m2) :
  tail_inv mu_trash [:: Build_frame_pkg val & mus] [:: c & s1] [:: d & s2] m1 m2.
Proof.
split=> /=.
split; first by apply: (head_rel inv).
by case: tlinv.
split. 
exists pf,cd,e,sig,args1,e,sig,args2; split.
apply: Build_frame_inv=> //.
by apply: (head_match inv).
by apply: (head_vis inv).
by apply: (head_ctndS inv).
by apply: (head_ctndT inv).
by apply: (head_mapdS inv).
by apply: (head_ctnsS inv).
by apply: (head_ctnsT inv).
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
(sep : sm_inject_separated mu mu' m1 m2)
(alloc : sm_locally_allocated mu mu' m1 m2 m1' m2'). 

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

Lemma all_relinv_step mu_trash mus s1 s2 :
  frame_all mu_trash mus m1 m2 s1 s2 -> 
  All (rel_inv_pred mu) mus -> 
  All (rel_inv_pred mu') mus.
Proof.
elim: mus s1 s2=> // pkg mus' IH s1 s2 A /= => [][] B C.
move: (rel_inv_pred_step (frame_all_fwd1 A) (frame_all_fwd2 A) B)=> D.
by split=> //; last by apply: (IH _ _ (frame_all_tail A) C).
Qed.

Lemma frame_all_step mu_trash mus s1 s2 :
  All (rel_inv_pred mu) mus -> 
  frame_all mu_trash mus m1 m2 s1 s2 -> 
  frame_all mu_trash mus m1' m2' s1 s2.
Proof.
elim: mus s1 s2=> // pkg mus' IH s1' s2' E.
simpl in E; case: E=> E F.
case: pkg E=> mu0 m10 m20 val' E.

move/frame_all_inv.
move=> []c []s1'' []d []s2'' []-> ->.
move=> []pf []cd []e1 []sig1 []vals1 []e2 []sig2 []vals2.
move=> []inv containS mapS containT allS allT /=.

split.
exists pf,cd,e1,sig1,vals1,e2,sig2,vals2.

split.
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
have wd: SM_wd mu0'. 
{ apply: replace_reach_wd=> //.
  by apply: (forall_vals_inject_restrictD _ _ _ _ frvinj). }
apply: (@disjinv_unchanged_on_tgt (Inj.mk wd) mu Esrc Etgt 
  m10 m1 m2 m2' fwd1')=> //.
move=> b'; case: val''; move/(_ b')=> I _ Q; apply: I.
by rewrite replace_locals_DOM in Q.

by apply: containS.
by apply: mapS.
by apply: containT.
by move: allS; case: mus' allT IH F containS mapS containT p.
by move: allT; case: mus' allS IH F containS mapS containT p.
by eapply IH; eauto.
Qed.

Lemma tail_inv_step mu_trash mus s1 s2 :
  All (rel_inv_pred mu) mus -> 
  tail_inv mu_trash mus s1 s2 m1 m2 -> 
  tail_inv mu_trash mus s1 s2 m1' m2'.
Proof. 
by move=> A []B C; split=> //; last by apply: frame_all_step. 
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
move: F; rewrite/RC.roots/in_mem/=; move/orP=> [|F].
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
apply: (RC.roots_domains_eq _ H2).
by apply: genvs_domain_eq_sym; apply: (my_ge_S (Core.i c)).
Qed.

Lemma head_inv_step 
    c d (pf : Core.i c=Core.i d) c' (d' : C (cores_T (Core.i d)))
    cd cd' mu_trash mus s1 s2 U :
  head_inv pf cd mu_trash mu mus m1 m2 -> 
  frame_all mu_trash mus m1 m2 s1 s2 -> 
  RC.args (Core.c c)=RC.args c' -> 
  RC.rets (Core.c c)=RC.rets c' -> 
  RC.locs c' = (fun b => RC.locs (Core.c c) b 
    || freshloc m1 m1' b
    || RC.reach_set (ge (cores_S (Core.i c))) (Core.c c) m1 b) ->
  effect_semantics.effstep 
    (sem (cores_S (Core.i c))) (ge (cores_S (Core.i c))) U 
    (Core.c c) m1 c' m1' -> 
  match_state (sims (Core.i (Core.upd c c'))) cd' mu'
    (Core.c (Core.upd c c')) m1'
    (cast'' pf (Core.c (Core.upd d d'))) m2' -> 
  RC.locs c' 
    = (fun b => RC.locs (Core.c c) b
             || freshloc m1 m1' b 
             || RC.reach_set (ge (cores_S (Core.i c))) (Core.c c) m1 b) ->
  @head_inv (Core.upd c c') (Core.upd d d') pf cd' mu_trash mu' mus m1' m2'.
Proof.
move=> hdinv frame args rets mylocs effstep mtch locs.
apply: Build_head_inv=> //.
by apply: (all_relinv_step frame); apply: (head_rel hdinv).
+ case: hdinv=> hdmtch ? A _ _ _ _ _; apply: (vis_inv_step A)=> //.
  by apply match_visible in hdmtch.
by move: (head_ctndS hdinv); rewrite/frgnS_contained -(intern_incr_frgnsrc incr).
by move: (head_ctndT hdinv); rewrite/frgnT_contained -(intern_incr_frgntgt incr).
by move: (head_mapdS hdinv); rewrite/frgnS_mapped -(intern_incr_foreign _ _ incr).
move: (head_ctnsS hdinv); generalize dependent mus; case=> //.
by move=> mu0 ? _ _ A b; move/A; apply: intern_incr_sharedSrc.
move: (head_ctnsT hdinv); generalize dependent mus; case=> //.
by move=> mu0 ? _ _ A b; move/A; apply: intern_incr_sharedTgt.
Qed.

Lemma trash_inv_step (mu_trash : Inj.t) mupkg mupkg' (mus : seq frame_pkg) : 
  frame_mu0 mupkg=mu -> 
  frame_mu0 mupkg'=mu' -> 
  trash_inv mu_trash mupkg mus m1 m2 -> 
  trash_inv mu_trash mupkg' mus m1' m2'.
Proof.
move=> A B; case=> C D E /= []F G []H I []K L Min.
apply: Build_trash_inv=> //=.
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
case: Min=> CtS CtT CrS CrT FS FT FrS FrT EiT EiR.
apply: Build_trash_minimal=> //.
move=> b X; move: (CtS _ X); rewrite /in_mem /=.
by rewrite A B (intern_incr_extsrc incr).
move=> b X; move: (CtT _ X); rewrite /in_mem /=.
by rewrite A B (intern_incr_exttgt incr).
move=> b X; move: (FS _ X); rewrite /in_mem /=.
by rewrite A B (intern_incr_frgnsrc incr).
move=> b X; move: (FT _ X); rewrite /in_mem /=.
by rewrite A B (intern_incr_frgntgt incr).
by rewrite B -(intern_incr_extern incr) -A.
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
    exists (pf : c.(Core.i)=d.(Core.i)) mu_trash (mu_top : Inj.t) mus, 
    let mu_tot := join_all (frame_mu0 mu_trash) $ mu_top :: map frame_mu0 mus in
    [/\ mu = restrict_sm mu_tot (vis mu_tot) 
      , REACH_closed m1 (vis mu)
      , trash_inv mu_trash mu_top mus m1 m2
      , exists pf2 : projT1 data = c.(Core.i),
          @head_inv c d pf (cast_ty (lift_eq _ pf2) (projT2 data)) 
          mu_trash mu_top mus m1 m2 
      & tail_inv mu_trash mus (pop s1) (pop s2) m1 m2] 

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
move: (R_inv pf)=> []A []? []mu_top []? []? _ _ []pf2. 
move/head_match=> MATCH ?.
have ->: (cast'' peek_ieq (Core.c (peekCore x2)) 
         = cast'' A (Core.c (peekCore x2)))
  by f_equal; f_equal; apply proof_irr.
exists (cast_ty (lift_eq _ pf2) (projT2 data)). 
by exists mu_top.
Qed.

Lemma R_AllDisjointS 
    (mu_trash mu_top : frame_pkg) (mus : seq frame_pkg) 
    c d (eq : Core.i c=Core.i d) cd s1 s2 :
  trash_inv mu_trash mu_top mus m1 m2 -> 
  head_inv eq cd mu_trash mu_top mus m1 m2 -> 
  tail_inv mu_trash mus s1 s2 m1 m2 -> 
  AllDisjoint locBlocksSrc \o map (Inj.mu \o frame_mu0) 
    $ mu_trash :: mu_top :: mus.
Proof.
move=> /= A B C; split; first by move: (trash_disj_S A); move=> /= [].
move: (head_AllDisjointLS B)=> D; split=> //. 
by apply: (tail_AllDisjointLS C).
Qed.

Lemma R_AllDisjointT
    (mu_trash mu_top : frame_pkg) (mus : seq frame_pkg) 
    c d (eq : Core.i c=Core.i d) cd s1 s2 :
  trash_inv mu_trash mu_top mus m1 m2 -> 
  head_inv eq cd mu_trash mu_top mus m1 m2 -> 
  tail_inv mu_trash mus s1 s2 m1 m2 -> 
  AllDisjoint locBlocksTgt \o map (Inj.mu \o frame_mu0) 
    $ mu_trash :: mu_top :: mus.
Proof.
move=> /= A B C; split; first by move: (trash_disj_T A); move=> /= [].
move: (head_AllDisjointLT B)=> D; split=> //. 
by apply: (tail_AllDisjointLT C).
Qed.

Lemma R_AllConsistent 
    (mu_trash mu_top : frame_pkg) (mus : seq frame_pkg) 
    c d (eq : Core.i c=Core.i d) cd s1 s2 :
  trash_inv mu_trash mu_top mus m1 m2 -> 
  head_inv eq cd mu_trash mu_top mus m1 m2 -> 
  tail_inv mu_trash mus s1 s2 m1 m2 -> 
  AllConsistent \o map (Inj.mu \o frame_mu0) 
    $ mu_trash :: mu_top :: mus.
Proof.
move=> /= A B C; split; first by move: (trash_consist A); move=> /= [].
move: (head_AllConsistent B)=> D; split=> //. 
by apply: (tail_AllConsistent C).
Qed.

Lemma R_wd : SM_wd mu.
Proof.
move: (R_inv pf)=> []A []mu_trash []mu_top []mus []B C D []pf2 E F.
have valid: sm_valid mu_top m1 m2 by apply: (match_validblocks _ (head_match E)).
have D': trash_inv mu_trash (Build_frame_pkg valid) mus m1 m2 by [].
rewrite B; apply: restrict_sm_WD=> //; apply: join_all_wd.
by move: (R_AllDisjointS D' E F)=> /=; rewrite map_comp.
by move: (R_AllDisjointT D' E F)=> /=; rewrite map_comp.
by move: (R_AllConsistent D' E F)=> /=; rewrite map_comp.
Qed.

Lemma R_isGlob b : isGlobalBlock my_ge b -> frgnBlocksSrc mu b.
Proof.
move: (R_inv pf)=> []A []mu_trash []mu_top []mus []B ? X []pf2 Y Z.
rewrite B restrict_sm_frgnBlocksSrc; apply: join_all_isGlob.
by apply: (trash_isglob X).
split; first by apply: (head_globs Y). 
by apply: (tail_globs Z).
Qed.

Lemma R_presglobs : Events.meminj_preserves_globals my_ge (extern_of mu).
Proof. 
move: (R_inv pf)=> []A []mu_trash []mu_top []mus []B ? X []pf2 Y Z.
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
by move: (R_inv pf)=> []A []mu_trash []mu_top []mus []B H.
Qed.

Lemma R_match_restrict (X : block -> bool) 
  (vis : forall b : block, vis mu b -> X b)
  (reach : REACH_closed m1 X) :
  R data (@restrict_sm_wd  _ (Inj.mk R_wd) _ vis reach) x1 m1 x2 m2.
Proof.
move: (R_inv pf)=> []A []mu_trash []mu_top []mus []B ? Y Z W /=.
rewrite B restrict_sm_com restrict_sm_nest; first by rewrite -B.
by move: vis; rewrite B vis_restrict_sm.
Qed.

Lemma R_match_validblocks : sm_valid mu m1 m2.
Proof. 
move: (R_inv pf)=> []A []mu_trash []mu_top []mus []B ? X []pf2 Y Z.
rewrite B /sm_valid /DOM restrict_sm_DomSrc /RNG restrict_sm_DomTgt.
apply: join_all_valid=> //=; first by apply: (trash_valid X).
split; first by apply: (head_valid Y).
by move: (tail_valid Z); rewrite -!All_comp.
Qed.

Lemma R_len_callStack : size (callStack x1) = size (callStack x2).
Proof.
case: (R_inv pf)=> []pf0 []? []? []? []A B C D.
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

Lemma R_inContext' : inContext x2 -> inContext x1.
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
case: (R_inv inv)=> pf []mu_trash []mu_top []mus []_.
move=> rc _ []pf2; move/head_match.
unfold LinkerSem.at_external0 in atext1.
have atext1':
  at_external 
    (sem (cores_S (Core.i (peekCore st1)))) 
    (Core.c (peekCore st1)) =
  Some (ef,sig,args1) by rewrite /RC.at_external.
move=> hd_match _.
case: (core_at_external (sims (Core.i (c inv))) 
      _ _ _ _ _ _ hd_match atext1').
move=> inj []rc1 []defs []args2 []valinj []atext2 rc2; exists args2.
set T := C \o cores_T.
rewrite /LinkerSem.at_external0.
set P := fun ix (x : T ix) => 
            at_external (sem (cores_T ix)) x
            = Some (ef, sig, args2).
change (P (Core.i (peekCore st2)) (Core.c (peekCore st2))).
have X: (P (Core.i (c inv)) (cast'' pf (Core.c (d inv)))).
{ move: atext2=> /=; rewrite /RC.at_external /P /=.
  have eq: at_external (sem (cores_T (Core.i (c inv))))
            (cast'' pf (Core.c (d inv))) =
           at_external (sem (cores_T (Core.i (d inv))))
            (Core.c (d inv)). 
  { set T' := C \o cores_T.
    set P' := fun ix (x : T' ix) => 
                 at_external (sem (cores_T ix)) x
                 = at_external (sem (cores_T (Core.i (d inv))))
                     (Core.c (d inv)).
    change (P' (Core.i (c inv)) 
               (cast T' (sym_eq pf) (Core.c (d inv)))).
    by apply: cast_indnatdep. }
  by []. }
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
case: (R_inv inv)=> pf []mu_trash []mu_top []mus []mu_eq.
move=> rc trinv []pf2 hdinv tlinv; move: hdl1; rewrite LinkerSem.handleP.
move=> []all_at1 []ix []c1 []fntbl1 init1 st1'_eq.

have atext1': 
  at_external (sem (cores_S (Core.i (c inv)))) (Core.c (c inv)) 
  = Some (ef,sig,args1) by [].

have atext2': 
  at_external (sem (cores_T (Core.i (c inv)))) 
              (cast'' pf (Core.c (d inv)))
  = Some (ef,sig,args2).
 { set T := C \o cores_T.
   set P := fun ix (x : T ix) => 
              at_external (sem (cores_T ix)) x
              = Some (ef, sig, args2).
   have: (P (Core.i (d inv)) (Core.c (d inv)))
     by rewrite /LinkerSem.at_external0.
   by apply: cast_indnatdep. }

have atext2'': 
  at_external (sem (cores_T (Core.i (c inv))))
              (cast'' pf (Core.c (d inv)))
  = Some (ef,sig,args2).
 { set T := C \o cores_T.
   set P := fun ix (x : T ix) => 
              at_external (sem (cores_T ix)) x
              = Some (ef, sig, args2).
   have: (P (Core.i (d inv)) (Core.c (d inv)))
     by rewrite /LinkerSem.at_external0.
   by apply: cast_indnatdep. }

case: (core_at_external (sims (Core.i (c inv))) 
      _ _ _ _ _ _ (head_match hdinv) atext1').
move=> inj []rc_exportedSrc []defs1 []args2' []vinj []atext2'''. 
move=> []rc_exportedTgt defs2.

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
  case: (core_initial _ _ _ _ (sims c1_i) _ args1
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
{ rewrite /mu_new; apply: Build_SM_wd=> //=.
  by move=> ?; left.
  by move=> ?; left.
  rewrite /frgnS /frgnT /exportedSrc /exportedTgt=> b1; case/orP=> get1.
  case: (getBlocks_inject _ _ _ vinj _ get1)=> x' []y' [].
  case/restrictD_Some=> ? ? get2.
  by exists x',y'; split=> //; apply/orP; left.
  rewrite sharedSrc_iff_frgnpub in get1. 
  case: (orP get1)=> H1.
  case: (Inj_wd mu_top)=> _ _ _ _ _; case/(_ b1 H1)=> x' []y' []H2 H3 _ _.
  exists x',y'; rewrite /j /as_inj /join H2; split=> //.
  by apply/orP; rewrite /sharedTgt H3; right; apply/orP; left.
  case: (Inj_wd mu_top)=> _ _ _ _; case/(_ b1 H1)=> x' []y' []H2 H3 _ _ _.
  exists x',y'; rewrite /j /as_inj /join H2; split=> //.
  have ->: extern_of mu_top b1 = None.
  { by rewrite (local_some_extern_none H2). }
  by [].
  by apply/orP; rewrite /sharedTgt H3; right; apply/orP; right.
  by apply: Inj_wd. }

set mu_new' := Inj.mk mu_new_wd.

have cons_trash_j: consistent (as_inj mu_trash) j.
{ rewrite /j /consistent=> b1 b2 b2' d2 d2' eOf asInj.
  case: trinv=> X Y Z W U V; case=> ? ? ? ? ? ? ? ? ? ?.
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
{ move: (head_rel hdinv)=> rel.
  clear - vinj rel; elim: mus rel=> //= mu0 mus' IH []rel1 rel2; split.
  apply: relinv_init=> //.
  by apply: forall_inject_val_list_inject.
  by apply: IH. }

have mu_new_vis_inv: vis_inv c1 mu_new'.
{ apply: Build_vis_inv=> // b; rewrite /in_mem /= => Y.
  rewrite /vis /mu_new /frgnS /exportedSrc /=.
  move: Y; rewrite /RC.roots; case/orP.
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
{ case: trinv=> X Y Z W U V; case=> CtS CtT CrS CrT FS FT FrS FrT EiT EiR.
  apply: Build_trash_inv=> //.
  split=> //=; first by rewrite predI01.
  split=> //=; first by rewrite predI01. 
  by split=> //=; rewrite /mu_new initial_SM_as_inj. 
  apply: Build_trash_minimal=> //.
  move=> b AA; move: (CtS _ AA); rewrite /in_mem /= /domS /DomSrc.
  by move=> ->; apply/orP; right.
  move=> b AA; move: (CtT _ AA); rewrite /in_mem /= /domT /DomTgt.
  by move=> ->; apply/orP; right.
  move=> mu0 /=; case; first by move=> <-. by apply: (CrS mu0).
  move=> mu0 /=; case; first by move=> <-. by apply: (CrT mu0).
  move=> b AA; move: (FS _ AA); rewrite /in_mem /= /frgnS /DomSrc.
  rewrite /exportedSrc sharedSrc_iff_frgnpub. 
  by move=> ->; apply/orP; right.
  by apply: Inj_wd.
  move=> b AA; move: (FT _ AA); rewrite /in_mem /= /frgnT /DomTgt.
  by rewrite /exportedTgt /sharedTgt; move=> ->; apply/orP; right.
  move=> mu0 /=; case; first by move=> <-. by apply: (FrS mu0).
  move=> mu0 /=; case; first by move=> <-. by apply: (FrT mu0). 
  rewrite /mu_new' /= /j.
  apply: (inject_incr_trans 
    (extern_of mu_trash) (extern_of mu_top) (as_inj mu_top))=> //.
  by apply: extern_in_all.
  move=> /= mu0; case; first by move=> <-.
  by apply: EiR. }

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
  apply: init_ctndT=> //.
  by apply: (head_ctndT hdinv). }

have mu_new'_mapd: 
  linkingSimulation.frgnS_mapped mu_trash mu_new' (pkg :: mus).
{ rewrite /mu_new' /= /mu_new /domS /domT /frgnS /frgnT /j.
  cut (
   linkingSimulation.frgnS_mapped mu_trash
     (initial_SM (DomSrc pkg) (DomTgt pkg) (exportedSrc pkg args1)
        (exportedTgt pkg args2) (as_inj pkg)) (pkg :: mus))=> //.
  apply: init_frgnS_mapped=> //.
  by apply: (head_mapdS hdinv). }

have shrdS_pkg_sub_mu_new':
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

have shrdT_pkg_sub_mu_new':
  {subset sharedTgt pkg <= sharedTgt mu_new'}.
{ rewrite /mu_new' /= /mu_new=> b; rewrite /in_mem /= /is_true. 
  rewrite /sharedTgt /frgnT /exportedTgt /sharedTgt /=.
  by case/orP=> ->; rewrite -!(orb_comm true). }

have hdinv_new:
  head_inv pf_new cd_new mu_trash mu_new' (pkg :: mus) m1 m2.
{ by apply: Build_head_inv. }

exists (existT _ (Core.i c1) cd_new),st2'; split.
rewrite LinkerSem.handleP; exists all_at2,ix,c2; split=> //.
by move: fntbl1; rewrite (R_fntbl inv).

have valid_new: sm_valid mu_new' m1 m2. 
{ rewrite /initial_SM /sm_valid /DOM /RNG /DomSrc /DomTgt /=.
  rewrite /domS /domT; split=> b; generalize dependent valid'; case.
  by move=> X ? ? ? ? ? ? ? ? ? H; apply: (X b).
  by move=> ? X ? ? ? ? ? ? ? ? H; apply: (X b). }

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
exists pf_new',mu_trash,mu_new',[:: pkg & mus]; split=> //.
by move: mu_tot_new_eq; rewrite /mu_tot_new /mu_tot=> ->.
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
  Forall2 (val_inject (restrict (as_inj mu_top) (vis mu_top))) args1 args2.
{ apply: restrict_forall_vals_inject=> //.
  rewrite /vis=> b get; case: (getBlocks1_frgnpub _ get).
  by move/pubsrc_sub_locsrc; rewrite /in_mem /= => ->.
  by move=> ->; apply/orP; right. }
move: (head_tail_inv tlinv valid'' atext1' atext2' inj vinj'' hdinv).
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
case: (R_inv inv)=> pf []mu_trash []mu_top []mus []mu_eq.
move=> rc trinv []pf2 hdinv tlinv.
move: hlt1; rewrite /LinkerSem.halted0=> hlt10.
case: (core_halted (sims (Core.i (peekCore st1)))
       _ _ _ _ _ _ (head_match hdinv) hlt10)
       => rv2 []inj12 []rcS []rcT []vinj []vdefs hlt2.
exists rv2.
set T := C \o cores_T.
set P := fun ix (x : T ix) => 
  halted (sem (cores_T ix)) x = Some rv2.
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
  exists rv2 st2'' (st2' : linker N cores_T) cd', 
  [/\ LinkerSem.halted0 st2 = Some rv2
    , inContext st2
    , popCore st2 = Some st2''
    , LinkerSem.after_external (Some rv2) st2'' = Some st2'
    & R cd' mu st1' m1 st2' m2].
Proof.
case: (R_inv inv)=> pf []mu_trash []mu_top []mus []mu_eq.
move=> rc trinv []pf_hd hdinv tlinv.
move: hlt1; rewrite /LinkerSem.halted0=> hlt10.
case: (core_halted (sims (Core.i (peekCore st1)))
       _ _ _ _ _ _ (head_match hdinv) hlt10)
       => rv2 []inj12 []rcS []rcT []vinj []rv_defs hlt2.
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
case=> fr0 ctndS0 ctndT0 mapdS0 sub0S sub0T frametail.

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
  at_external (sem (cores_T (Core.i hd1)))
    (cast'' pf0 (Core.c hd2)) = Some (e0,sig02,vals02).
{ by rewrite /= -at02; f_equal. }

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

set nu' := reestablish nu mu_top.

have restrict_mu_top_nu:
  restrict (as_inj mu_top) (DomSrc nu) = as_inj nu.
{ rewrite /restrict /as_inj /join; extensionality b.
  move: (head_rel hdinv); rewrite mus_eq /= => [][]. 
  case=> /= incr_mu0_top sep_mu0_top disj_mu0_top _.
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
case=> /= incr0_top sep0_top disj0_top _.

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
set mu' := replace_externs nu' frgnSrc' frgnTgt'.

have [hd2' [pf_eq22' [pf_eq12' [cd' [aft2' mtch12']]]]]:
  exists hd2' (pf_eq22' : Core.i hd2 = Core.i hd2') 
              (pf_eq12' : Core.i hd1' = Core.i hd2')
         cd',
  [/\ after_external (sem (cores_T (Core.i hd2)))
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
    after_external (sem (cores_T ix)) (Some rv2) x = Some y.
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

split=> //.

move: hlt2.

set T := C \o cores_T.
set P := fun ix (x : T ix) => 
 halted (sem (cores_T ix)) x = Some rv2.
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
case: mu_trash mu_eq trinv hdinv ctndS0 ctndT0 mapdS0 frametail frameall.
move=> mu_trash x1 x2 xval.
move=> /= mu_eq trinv hdinv ctndS0 ctndT0 mapdS0 frametail frameall.

set mu_trash'' := join_sm mu_top mu_trash.

have mu_trash''_wd : SM_wd mu_trash''.
{ case: trinv=> /= ? ? ? []H1 H2 []H3 H4 []H5 H6; case=> ? ? ? ? ? ? ? ? ? ?.
  apply: join_sm_wd=> //; first by move: H1; rewrite DisjointC; apply.
  by move: H3; rewrite DisjointC; apply.
  by move: H5; move/consistentC; apply. }

set mu_trash' := Inj.mk mu_trash''_wd.

have mu_trash'_val : sm_valid mu_trash' m1 m2.
{ apply: join_sm_valid; first by apply: (head_valid hdinv).
  by apply: (trash_valid trinv). }

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
{ split=> //; split=> b.
  rewrite /DomSrc; case/orP; rewrite /mu' replace_externs_locBlocksSrc /nu'.
  by rewrite reestablish_locBlocksSrc /nu replace_locals_locBlocksSrc=> ->.
  rewrite /mu' replace_externs_extBlocksSrc /nu'.
  rewrite reestablish_extBlocksSrc /nu replace_locals_locBlocksSrc=> E.
  have lN: locBlocksSrc mu0 b = false.
  { by move: (extBlocksSrc_locBlocksSrc _ (Inj_wd _) _ E). }
  rewrite lN; apply/orP; right.
  move: (head_rel hdinv); rewrite mus_eq /=; case; case=> /=; case.
  move=> _; case; move/(_ b)=> H _ _ _ _; apply: H.
  by rewrite /DomSrc E; apply/orP; right.

  rewrite /DomTgt; case/orP; rewrite /mu' replace_externs_locBlocksTgt /nu'.
  by rewrite reestablish_locBlocksTgt /nu replace_locals_locBlocksTgt=> ->.
  rewrite /mu' replace_externs_extBlocksTgt /nu'.
  rewrite reestablish_extBlocksTgt /nu replace_locals_locBlocksTgt=> E.
  have lN: locBlocksTgt mu0 b = false.
  { by move: (extBlocksTgt_locBlocksTgt _ (Inj_wd _) _ E). }
  rewrite lN; apply/orP; right.
  move: (head_rel hdinv); rewrite mus_eq /=; case; case=> /=; case.
  move=> _; case=> _; move/(_ b)=> H _ _ _; apply: H.
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

have subFT: {subset frgnBlocksTgt mu0 <= frgnTgt'}.
{ rewrite /frgnTgt' /nu'=> b; rewrite /in_mem /= => H.
  rewrite /DomTgt reestablish_locBlocksTgt /nu.
  rewrite replace_locals_locBlocksTgt.
  rewrite reestablish_extBlocksTgt.
  rewrite replace_locals_locBlocksTgt.
  have lN: locBlocksTgt mu0 b = false.
  { by move: (extBlocksTgt_locBlocksTgt _ (Inj_wd _) _ (frgntgt_sub_exttgt H)). }
  rewrite lN /=.
  rewrite /exportedTgt /sharedTgt. 
  rewrite reestablish_frgnBlocksTgt replace_locals_frgnBlocksTgt.
  have pub_eq: 
    pubBlocksTgt (reestablish (replace_locals mu0 pubSrc' pubTgt') mu_top)
    = pubBlocksTgt (replace_locals mu0 pubSrc' pubTgt').
  { by rewrite reestablish_pubBlocksTgt. }
  rewrite pub_eq replace_locals_pubBlocksTgt; apply/andP; split.
  case: incr0_top=> _; case; move/(_ b)=> _ H2.
  apply: H2; rewrite /DomTgt.
  move: (frgntgt_sub_exttgt H). 
  by rewrite /in_mem /= => ->; apply/orP; right.
  by apply: REACH_nil; apply/orP; right; apply/orP; left. }

have shrdS_mu0_mu': {subset sharedSrc mu0 <= sharedSrc mu'}.
{ move=> b; rewrite !sharedSrc_iff_frgnpub=> //; case/orP=> F.
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
{ move=> b; rewrite /sharedTgt; case/orP=> F.
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

exists (Build_frame_pkg mu_trash'_val),(Inj.mk mu'_wd),(tl mus).

have frgn_trash_sub_frgnSrc': 
  {subset (frgnBlocksSrc mu_trash) <= frgnSrc'}.
{ move=> b0 F. 
  rewrite /frgnSrc' /in_mem /= /DomSrc /nu'.
  rewrite reestablish_locBlocksSrc /nu replace_locals_locBlocksSrc.
  rewrite reestablish_extBlocksSrc.
  rewrite replace_locals_locBlocksSrc.
  have IN: In (Inj.mu mu0) [seq (Inj.mu \o frame_mu0) x | x <- mus]. 
  { by rewrite mus_eq /=; left. }
  have ll: locBlocksSrc mu0 b0 = false.
  { move: (trash_ctnd_restS (trash_min trinv) IN (frgnsrc_sub_extsrc F)).
    rewrite /in_mem /=.
    by move/(extBlocksSrc_locBlocksSrc _ (Inj_wd _) _)=> ->. }
  clear - F trinv mus_eq nu'_wd ll; apply/andP; split.
  apply/orP; right; rewrite ll; apply/orP; right.
  by apply: (trash_ctnd_topS (trash_min trinv) (frgnsrc_sub_extsrc F)).
  rewrite ll; apply/andP; split=> //.
  apply: REACH_nil.
  rewrite /exportedSrc sharedSrc_iff_frgnpub.
  apply/orP; right; apply/orP; left.
  suff: frgnBlocksSrc (replace_locals mu0 pubSrc' pubTgt') b0.
  by rewrite reestablish_frgnBlocksSrc.
  rewrite replace_locals_frgnBlocksSrc.
  apply: (trash_fctnd_restS (trash_min trinv))=> //.
  by rewrite mus_eq /=; left.
  by apply: nu'_wd. }

have frgn_trash_sub_frgnTgt': 
  {subset (frgnBlocksTgt mu_trash) <= frgnTgt'}.
{ move=> b0 F. 
  rewrite /frgnTgt' /in_mem /= /DomTgt /nu'.
  rewrite reestablish_locBlocksTgt /nu replace_locals_locBlocksTgt.
  rewrite reestablish_extBlocksTgt.
  rewrite replace_locals_locBlocksTgt.
  have IN: In (Inj.mu mu0) [seq (Inj.mu \o frame_mu0) x | x <- mus]. 
  { by rewrite mus_eq /=; left. }
  have ll: locBlocksTgt mu0 b0 = false.
  { move: (trash_ctnd_restT (trash_min trinv) IN (frgntgt_sub_exttgt F)).
    rewrite /in_mem /=.
    by move/(extBlocksTgt_locBlocksTgt _ (Inj_wd _) _)=> ->. }
  clear - F trinv mus_eq nu'_wd ll; apply/andP; split.
  apply/orP; right; rewrite ll; apply/orP; right.
  by apply: (trash_ctnd_topT (trash_min trinv) (frgntgt_sub_exttgt F)).
  rewrite ll; apply/andP; split=> //.
  apply: REACH_nil.
  rewrite /exportedTgt /sharedTgt.
  apply/orP; right; apply/orP; left.
  suff: frgnBlocksTgt (replace_locals mu0 pubSrc' pubTgt') b0.
  by rewrite reestablish_frgnBlocksTgt.
  rewrite replace_locals_frgnBlocksTgt.
  apply: (trash_fctnd_restT (trash_min trinv))=> //.
  by rewrite mus_eq /=; left. }

have eincr_trash_mu': 
  inject_incr (extern_of mu_trash) (extern_of mu').
{ rewrite /mu' replace_externs_extern /nu'.
  rewrite reestablish_extern_of /nu replace_locals_locBlocksSrc.
  move=> b b' d' H /=.
  have l0: locBlocksSrc mu0 b = false.
  { case: (extern_DomRng' _ (Inj_wd _) _ _ _ H)=> _ []_ []_ []_ []eS _.
    move: (trash_ctnd_restS (trash_min trinv) mu0_in eS); rewrite /in_mem /=.
    by move/(extBlocksSrc_locBlocksSrc _ (Inj_wd _) _). }
  rewrite l0.
  have eTop: extern_of mu_top b = Some (b',d').
  { by apply: (trash_eincr_top (trash_min trinv) H). }
  by rewrite /as_inj /join eTop. }

move=> /=; split=> //.

set mu0_pkg := {| frame_mu0 := mu0; frame_m10 := m10; frame_m20 := m20;
                  frame_val := mu0_val |}.

have vis_eq: 
  (vis (join_sm mu_top 
    (join_sm mu0 (join_all mu_trash [seq frame_mu0 i | i <- mus'])))
  = vis (join_sm mu' (join_all mu_trash' [seq frame_mu0 i | i <- mus']))).
{ rewrite /vis /mu_trash' /mu' /join_sm /in_mem /= /in_mem /=; f_equal=> //=.
  extensionality b; rewrite /in_mem /=.
  rewrite replace_externs_locBlocksSrc /nu'.
  rewrite reestablish_locBlocksSrc /nu replace_locals_locBlocksSrc.
  rewrite replace_externs_frgnBlocksSrc.
  rewrite (frgnS_join_all'_sub trinv)=> //.
  have eq: (frgnSrc' b && frgnBlocksSrc mu_trash b) = frgnBlocksSrc mu_trash b.
  { by rewrite andb_comm predI_sub5=> //; apply: frgn_trash_sub_frgnSrc'. }
  rewrite eq.
  rewrite (frgnS_join_all_sub trinv).
  rewrite (andb_comm (frgnBlocksSrc mu0 b)).
  rewrite andb_assoc.
  rewrite (andb_comm (frgnBlocksSrc mu_top b)).
  rewrite predI_sub5.
  rewrite predI_sub5.
  rewrite join_all_shift_locBlocksSrcE /= /in_mem /=.
  rewrite orb_assoc.
  rewrite (orb_comm (locBlocksSrc mu_top b)).
  by rewrite (orb_assoc (locBlocksSrc mu0 b)).
  by apply: (trash_fctnd_topS (trash_min trinv)).
  case/andP=> H1 H2; move: (trash_fctnd_restS (trash_min trinv)).
  by move/(_ mu0 mu0_in); apply.
  by rewrite mus_eq /= => mu1 IN; right. 
  by rewrite mus_eq /= => mu1 IN; right. }

rewrite mu_eq mus_eq; f_equal=> /=.

{ extensionality b. 
  rewrite join_all_shift_locBlocksSrc.
  rewrite /= /in_mem /= /mu' /nu' /nu /mu_trash' /in_mem /=.
  rewrite replace_externs_locBlocksSrc.
  rewrite reestablish_locBlocksSrc.
  by rewrite replace_locals_locBlocksSrc. }

{ extensionality b. 
  rewrite join_all_shift_locBlocksTgt.
  rewrite /= /in_mem /= /mu' /nu' /nu /mu_trash' /in_mem /=.
  rewrite replace_externs_locBlocksTgt.
  rewrite reestablish_locBlocksTgt.
  by rewrite replace_locals_locBlocksTgt. }

{ have inj_eq: 
  (join (local_of mu_top)
    (join (local_of mu0) 
          (local_of (join_all mu_trash [seq frame_mu0 i | i <- mus'])))
  = (join (local_of mu') 
          (local_of (join_all mu_trash' [seq frame_mu0 i | i <- mus'])))).
  { rewrite join_all_shift_local_of.
    rewrite /= /in_mem /= /mu' /nu' /nu /mu_trash' /in_mem /=.
    rewrite !replace_externs_local.
    rewrite !reestablish_local_of.
    by rewrite !replace_locals_local. 
    have mu_top_valid: sm_valid mu_top m1 m2
      by apply: (match_validblocks _ (head_match hdinv)).
    set mupkg' := Build_frame_pkg mu_top_valid.
    have val': sm_valid mupkg' m1 m2 by apply: (head_valid hdinv).
    set mupkg := Build_frame_pkg val'.
    set mutrash := Build_frame_pkg (trash_valid trinv).
    have trinv': trash_inv mutrash mupkg mus m1 m2.
      by apply: trinv.
    have hdinv': 
      head_inv pf 
        (cast (fun ix : 'I_N => core_data (sims ix)) pf_hd (projT2 cd))
        mutrash mupkg mus m1 m2.
      by apply: hdinv.
    have tlinv': tail_inv mutrash mus (hd1::tl1) (hd2::tl2) m1 m2.
    { by split. }
    move: (R_AllDisjointS trinv' hdinv' tlinv').
    by rewrite /comp !map_comp mus_eq /= !map_id. }
  by rewrite inj_eq vis_eq. }

{ extensionality b.
  rewrite join_all_shift_extBlocksSrc.
  rewrite /= /in_mem /= /mu' /nu' /nu /mu_trash' /in_mem /=.
  rewrite replace_externs_extBlocksSrc.
  rewrite reestablish_extBlocksSrc.
  rewrite replace_locals_locBlocksSrc. 
  cut ((extBlocksSrc mu0 b /\
        extBlocksSrc (join_all (Inj.mk mu_trash''_wd) 
          [seq frame_mu0 i | i <- mus']) b) 
       <-> ((if locBlocksSrc mu0 b then false else DomSrc mu_top b) /\
           (extBlocksSrc (join_all (Inj.mk mu_trash''_wd) 
             [seq frame_mu0 i | i <- mus']) b))).

  case.
  case: (extBlocksSrc _ _)=> //.
  case: (extBlocksSrc _ _)=> //.
  case/(_ (conj erefl erefl)).
  case: (locBlocksSrc _ _)=> //.
  by move=> ->.
  move=> /=.
  case: (locBlocksSrc _ _)=> //.
  by rewrite andb_false_r.
  case: (extBlocksSrc _ _)=> //.
  case: (locBlocksSrc _ _)=> //. 
  case: (DomSrc _ _)=> //=.
  by move=> _; move/(_ (conj erefl erefl)); case.
  by symmetry; rewrite andb_false_r.

  rewrite join_all_extBlocksSrc /= /in_mem /=.
  case lSrc0: (locBlocksSrc mu0 b).
  have eSrc0_f: extBlocksSrc mu0 b = false. 
  { case eOf: (extBlocksSrc mu0 b)=> //.
    by rewrite (extBlocksSrc_locBlocksSrc _ (Inj_wd _) _ eOf) in lSrc0. }
  by rewrite eSrc0_f; split.
  split; case=> H1 []H2 H3; split=> //.
  by case: (andP H2)=> AA BB; rewrite /DomSrc AA; apply/orP; right.
  case: (andP H2)=> AA BB. 
  move: (trash_min trinv); rewrite mus_eq; move/trash_ctnd_restS.
  by move/(_ mu0_pkg); apply=> //=; left. }

{ extensionality b.
  rewrite join_all_shift_extBlocksTgt.
  rewrite /= /in_mem /= /mu' /nu' /nu /mu_trash' /in_mem /=.
  rewrite replace_externs_extBlocksTgt.
  rewrite reestablish_extBlocksTgt.
  rewrite replace_locals_locBlocksTgt. 
  cut ((extBlocksTgt mu0 b /\
        extBlocksTgt (join_all (Inj.mk mu_trash''_wd) 
          [seq frame_mu0 i | i <- mus']) b) 
       <-> ((if locBlocksTgt mu0 b then false else DomTgt mu_top b) /\
           (extBlocksTgt (join_all (Inj.mk mu_trash''_wd) 
             [seq frame_mu0 i | i <- mus']) b))).

  case.
  case: (extBlocksTgt _ _)=> //.
  case: (extBlocksTgt _ _)=> //.
  case/(_ (conj erefl erefl)).
  case: (locBlocksTgt _ _)=> //.
  by move=> ->.
  move=> /=.
  case: (locBlocksTgt _ _)=> //.
  by rewrite andb_false_r.
  case: (extBlocksTgt _ _)=> //.
  case: (locBlocksTgt _ _)=> //. 
  case: (DomTgt _ _)=> //=.
  by move=> _; move/(_ (conj erefl erefl)); case.
  by symmetry; rewrite andb_false_r.

  rewrite join_all_extBlocksTgt /= /in_mem /=.
  case lTgt0: (locBlocksTgt mu0 b).
  have eTgt0_f: extBlocksTgt mu0 b = false. 
  { case eOf: (extBlocksTgt mu0 b)=> //.
    by rewrite (extBlocksTgt_locBlocksTgt _ (Inj_wd _) _ eOf) in lTgt0. }
  by rewrite eTgt0_f; split.
  split; case=> H1 []H2 H3; split=> //.
  by case: (andP H2)=> AA BB; rewrite /DomTgt AA; apply/orP; right.
  case: (andP H2)=> AA BB. 
  move: (trash_min trinv); rewrite mus_eq; move/trash_ctnd_restT.
  by move/(_ mu0_pkg); apply=> //=; left. }

{ rewrite (frgnS_join_all_sub trinv).
  rewrite (frgnS_join_all'_sub trinv).
  rewrite (predIC (frgnBlocksSrc mu0)) predIA. 
  rewrite (predIC (frgnBlocksSrc mu_top)) -predIA.
  set rest := [predI frgnBlocksSrc mu_top & _].
  rewrite predI_sub4.
  rewrite (predIC (frgnBlocksSrc mu')) predI_sub4; first by [].
  by rewrite /mu'; rewrite replace_externs_frgnBlocksSrc.
  rewrite /rest=> b; rewrite /in_mem /= /in_mem /= => H; apply/andP; split.
  by apply: (trash_fctnd_topS (trash_min trinv)).
  by apply: (trash_fctnd_restS (trash_min trinv) mu0_in H).  
  by rewrite mus_eq=> mu1 /= H; right.
  by rewrite mus_eq=> mu1 /= H; right. }

{ rewrite (frgnT_join_all_sub trinv).
  rewrite (frgnT_join_all'_sub trinv).
  rewrite (predIC (frgnBlocksTgt mu0)) predIA. 
  rewrite (predIC (frgnBlocksTgt mu_top)) -predIA.
  set rest := [predI frgnBlocksTgt mu_top & _].
  rewrite predI_sub4.
  rewrite (predIC (frgnBlocksTgt mu')) predI_sub4; first by [].
  by rewrite /mu'; rewrite replace_externs_frgnBlocksTgt.
  rewrite /rest=> b; rewrite /in_mem /= /in_mem /= => H; apply/andP; split.
  by apply: (trash_fctnd_topT (trash_min trinv)).
  by apply: (trash_fctnd_restT (trash_min trinv) mu0_in H).  
  by rewrite mus_eq=> mu1 /= H; right.
  by rewrite mus_eq=> mu1 /= H; right. }

{ have inj_eq: 
  (join2 (extern_of mu_top)
    (join2 (extern_of mu0) 
          (extern_of (join_all mu_trash [seq frame_mu0 i | i <- mus'])))
  = (join2 (extern_of mu') 
          (extern_of (join_all mu_trash' [seq frame_mu0 i | i <- mus'])))).
  { rewrite (extern_of_trash_join_all_sub trinv).
    rewrite (extern_of_trash_join_all'_sub trinv).
    rewrite (@join2C (extern_of mu0)).
    rewrite (@join2_inject_incr (extern_of mu_trash)).
    rewrite join2C join2_inject_incr.
    rewrite join2C join2_inject_incr=> //.
    by apply: (trash_eincr_top (trash_min trinv)). 
    by apply: (trash_eincr_rest (trash_min trinv) mu0_in). 
    by rewrite mus_eq=> /= mu1; right.
    by rewrite mus_eq=> /= mu1; right. }
  by rewrite inj_eq vis_eq. }

apply: Build_trash_inv.
{ rewrite /mu_trash'' /join_sm /= join2C join2_inject_incr.
  apply: (trash_presglob trinv).
  by apply: (trash_eincr_top (trash_min trinv)). }
{ rewrite /mu_trash'' join_sm_frgnSrc predIC predI_sub4.
  by move=> b isGlob; move: (trash_isglob trinv isGlob).
  by apply: (trash_fctnd_topS (trash_min trinv)). }
{ rewrite /mu_trash''; apply: join_sm_valid.
  apply: (head_valid hdinv).
  by apply: (trash_valid trinv). }
{ move: (trash_disj_S trinv). 
  rewrite /mu_trash'' /mu' /nu' /=. 
  rewrite replace_externs_locBlocksSrc reestablish_locBlocksSrc.
  move=> []D10 AD1.
  have D1: DisjointLS mu_trash mu0.
  { clear - AD1 mu0_in.
    elim: mus AD1 mu0_in=> // a mus' /= IH []D1 AD1; case.
    by move=> <-; apply: D1.
    by move=> IN; apply: IH. }
  have D2: DisjointLS mu_top mu0.
  { move: (head_AllDisjointLS hdinv)=> AD2; clear - mu0_in AD2.
    elim: mus AD2 mu0_in=> // a mus' /= IH []D1 AD1; case.
    by move=> <-.
    by move=> IN; apply: IH. }
  split.
  rewrite /nu replace_locals_locBlocksSrc DisjointP=> a.
  move: D1 D2; rewrite /DisjointLS /= !DisjointP /in_mem /=. 
  move/(_ a)=> D1; move/(_ a)=> D2; move: D1 D2.
  by case: (locBlocksSrc mu_top a).
  move: (head_AllDisjointLS hdinv).
  move: AD1; rewrite mus_eq /= => [][]D3 AD1 []D4 AD2.
  clear - AD1 AD2; elim: mus' AD1 AD2=> // a mus' /= IH.
  move=> []D1 AD1 []D2 AD2; split.
  move: D1 D2; rewrite !DisjointP=> D1 D2 a0 /=; move: (D1 a0) (D2 a0).
  by rewrite /in_mem /=; case: (locBlocksSrc mu_top a0).
  by apply: IH. }
{ move: (trash_disj_T trinv). 
  rewrite /mu_trash'' /mu' /nu' /=. 
  rewrite replace_externs_locBlocksTgt reestablish_locBlocksTgt.
  move=> []D10 AD1.
  have D1: DisjointLT mu_trash mu0.
  { clear - AD1 mu0_in.
    elim: mus AD1 mu0_in=> // a mus' /= IH []D1 AD1; case.
    by move=> <-; apply: D1.
    by move=> IN; apply: IH. }
  have D2: DisjointLT mu_top mu0.
  { move: (head_AllDisjointLT hdinv)=> AD2; clear - mu0_in AD2.
    elim: mus AD2 mu0_in=> // a mus' /= IH []D1 AD1; case.
    by move=> <-.
    by move=> IN; apply: IH. }
  split.
  rewrite /nu replace_locals_locBlocksTgt DisjointP=> a.
  move: D1 D2; rewrite /DisjointLT /= !DisjointP /in_mem /=. 
  move/(_ a)=> D1; move/(_ a)=> D2; move: D1 D2.
  by case: (locBlocksTgt mu_top a).
  move: (head_AllDisjointLT hdinv).
  move: AD1; rewrite mus_eq /= => [][]D3 AD1 []D4 AD2.
  clear - AD1 AD2; elim: mus' AD1 AD2=> // a mus' /= IH.
  move=> []D1 AD1 []D2 AD2; split.
  move: D1 D2; rewrite !DisjointP=> D1 D2 a0 /=; move: (D1 a0) (D2 a0).
  by rewrite /in_mem /=; case: (locBlocksTgt mu_top a0).
  by apply: IH. }
{ rewrite /= as_inj_mu'_mu_top /mu_trash''; split.
  apply: consistentC.
  apply: join_sm_consistent.
  by move=> b1 b2 b2' d2 d2' ->; case=> -> ->.
  by move: (trash_consist trinv)=> /= []; move/consistentC.
  move: (trash_consist trinv) (head_AllConsistent hdinv)=> /=.
  rewrite mus_eq /=; move=> []C1 []C2 AC1 []C3 AC2.
  clear - AC1 AC2; elim: mus' AC1 AC2=> // a mus' /= IH.
  move=> []C1 AC1 []C2 AC2; split.
  apply: consistentC; apply: join_sm_consistent.
  by apply: consistentC.
  by apply: consistentC.
  by apply: IH. }

have trmin0: 
  trash_minimal mu_trash'' mu0 
  [seq (Inj.mu \o frame_mu0) x | x <- tl mus].
{ move: (@trash_minimal_return mu_trash mu_top mu0 
         [seq frame_mu0 x | x <- tl mus]).
  rewrite -map_comp /comp; apply=> //.
  by move: (trash_min trinv); rewrite mus_eq !map_comp /= -!map_comp /funcomp. }
case: trmin0=> ES ET ErS ErT FS FT FrS FrT eincrT eincrR.
case: (trash_min trinv)=> ES' ET' ErS' ErT' FS' FT' FrS' FrT' eincrT' eincrR'.
apply: Build_trash_minimal=> //=.
{ rewrite predIC predI_sub4=> //.
  rewrite /mu' replace_externs_extBlocksSrc /nu' reestablish_extBlocksSrc /nu.
  rewrite replace_locals_locBlocksSrc=> b; rewrite /in_mem /= /in_mem /= => H.
  have lN: locBlocksSrc mu0 b = false.
  { move: (trash_ctnd_restS (trash_min trinv) mu0_in H); rewrite /in_mem /=.
    by move/(extBlocksSrc_locBlocksSrc _ (Inj_wd _) _). }
  by rewrite lN; apply/orP; right; apply: ES'. }
{ rewrite predIC predI_sub4=> //.
  rewrite /mu' replace_externs_extBlocksTgt /nu' reestablish_extBlocksTgt /nu.
  rewrite replace_locals_locBlocksTgt=> b; rewrite /in_mem /= /in_mem /= => H.
  have lN: locBlocksTgt mu0 b = false.
  { move: (trash_ctnd_restT (trash_min trinv) mu0_in H); rewrite /in_mem /=.
    by move/(extBlocksTgt_locBlocksTgt _ (Inj_wd _) _). }
  by rewrite lN; apply/orP; right; apply: ET'. }
{ rewrite predIC predI_sub4=> //.
  rewrite /mu' replace_externs_frgnBlocksSrc /nu'.
  by apply: frgn_trash_sub_frgnSrc'. } 
{ rewrite predIC predI_sub4=> //.
  rewrite /mu' replace_externs_frgnBlocksTgt /nu'.
  by apply: frgn_trash_sub_frgnTgt'. } 
{ by rewrite join2C join2_inject_incr. }

{(* head_inv *)
exists erefl.

move: (head_rel hdinv) (head_ctnsS hdinv) (head_ctnsT hdinv). 
rewrite mus_eq /= => rel ctnsS ctnsT. 
case: rel; case=> /= incr1 sep1 disj1 rel. 

have vinj'': 
 Forall2 (val_inject (restrict (as_inj mu_top) (sharedSrc mu_top))) 
 [:: rv1] [:: rv2].
{ by apply: Forall2_cons. }

have vinj''': 
 val_list_inject (restrict (as_inj mu_top) (sharedSrc mu_top)) 
 [:: rv1] [:: rv2].
{ by apply: val_cons_inject. }

have REACH_subS: 
  {subset REACH m1 (fun b => getBlocks [:: rv1] b || sharedSrc mu_top b)
  <= sharedSrc mu_top}. 
{ move=> b RC; move: (rcS b RC); case/orP=> //.
  by move/getBlocks_inject; case/(_ _ _ vinj'')=> x []y []; case/restrictD_Some. }  

have REACH_subT: 
  {subset REACH m2 (fun b => getBlocks [:: rv2] b || sharedTgt mu_top b)
  <= sharedTgt mu_top}. 
{ move=> b RC; move: (rcT b RC); case/orP=> //.
  have defs1: vals_def [:: rv1].
  { by move: rv_defs=> /=; case/andP=> ->. }
  move=> get2; case: (vals_def_getBlocksTS vinj''' defs1 get2)=> x []y []get1.
  case/restrictD_Some=> asInj shrd1.
  case: (shared_SrcTgt _ (Inj_wd _) _ shrd1)=> ? []? []shrdOf shrd2.
  move: (shared_in_all _ (Inj_wd _) _ _ _ shrdOf); rewrite asInj; case.
  by move=> ->. }

have RRSrc b0:
  REACH m10 (exportedSrc mu0 vals01) b0 -> b0 \in sharedSrc mu0.
{ case: (core_at_external (sims (Core.i hd1)) 
        _ _ _ _ _ _ mtch0 at01)=> inj []rc_expSrc []? []vals02' []vinj' _.
  move/rc_expSrc; case/orP=> //.
  by move/getBlocks_inject; case/(_ _ _ vinj')=> x []y []; case/restrictD_Some. }

have RRTgt b0:
  REACH m20 (exportedTgt mu0 vals02) b0 -> b0 \in sharedTgt mu0.
{ case: (core_at_external (sims (Core.i hd1)) 
        _ _ _ _ _ _ mtch0 at01)=> 
    inj []rc_expSrc []defs1 []vals02' []vinj' []at02'' []rc_expTgt defs2.
  have vals_eq: vals02 = vals02'.
  { by rewrite at02' in at02''; case: at02''=> ? ? ->. }
  rewrite vals_eq; move/rc_expTgt; case/orP=> //.
  move: (forall_inject_val_list_inject _ _ _ vinj')=> vinj'''' get2.
  case: (vals_def_getBlocksTS vinj'''' defs1 get2)=> x []y []get1.
  case/restrictD_Some=> asInj shrd1.
  case: (shared_SrcTgt _ (Inj_wd _) _ shrd1)=> ? []? []shrdOf shrd2.
  move: (shared_in_all _ (Inj_wd _) _ _ _ shrdOf); rewrite asInj; case.
  by move=> ->. }

have eq: sharedSrc (reestablish nu mu_top) = sharedSrc nu.
{ rewrite !sharedSrc_iff_frgnpub=> //; extensionality b.
  by rewrite reestablish_frgnBlocksSrc reestablish_pubBlocksSrc. }

have sub_nu_topS b0: 
   sharedSrc nu b0 
-> sharedSrc mu_top b0.
{ move: (ctnsS)=> ctnsS'; rewrite sharedSrc_iff_frgnpub=> //.
  rewrite replace_locals_frgnBlocksSrc /nu replace_locals_pubBlocksSrc.
  case/orP=> H8; apply: ctnsS'; rewrite /in_mem /= sharedSrc_iff_frgnpub.
  by rewrite H8.
  by apply: Inj_wd.
  move: H8; rewrite /pubSrc'; case/andP=> H8; move/RRSrc. 
  by rewrite sharedSrc_iff_frgnpub. 
  by apply: Inj_wd. }

have sub_nu_topT b0: 
   sharedTgt nu b0 
-> sharedTgt mu_top b0.
{ rewrite /sharedTgt; case/orP.
  rewrite replace_locals_frgnBlocksTgt=> F. 
  by apply: ctnsT; rewrite /in_mem /= /sharedTgt F.
  rewrite replace_locals_pubBlocksTgt.
  by case/andP=> H I; move: (RRTgt _ I); move/ctnsT; apply. }

have subS b0: 
   (getBlocks [:: rv1] b0 || sharedSrc nu b0)
-> (getBlocks [:: rv1] b0 || sharedSrc mu_top b0).
{ case/orP; first by move=> ->; apply/orP; left.
  by move/sub_nu_topS=> ->; apply/orP; right. }

have subT b0: 
   (getBlocks [:: rv2] b0 || sharedTgt nu b0)
-> (getBlocks [:: rv2] b0 || sharedTgt mu_top b0).
{ case/orP; first by move=> ->; apply/orP; left.
  by move/sub_nu_topT=> ->; apply/orP; right. }

have frgnSrc'_pub_frgn: 
  {subset frgnSrc' <= [predU pubBlocksSrc mu_top & frgnBlocksSrc mu_top]}.
{ rewrite /frgnSrc' /nu' /exportedSrc eq.
  move=> b; rewrite /in_mem /= /in_mem /=; case/andP=> XX YY.
  case: {YY}(andP YY)=> H5 H6.
  have RR: REACH m1 (fun b => getBlocks [:: rv1] b || sharedSrc mu_top b) b.
  { by apply: (REACH_mono (fun b => getBlocks [:: rv1] b || sharedSrc nu b)). }
  move: (REACH_subS _ RR); rewrite sharedSrc_iff_frgnpub /in_mem /=.
  case/orP; first by move=> ->; apply/orP; right.
  by move=> ->; apply/orP; left.
  by apply: Inj_wd. }

have frgnTgt'_pub_frgn: 
  {subset frgnTgt' <= [predU pubBlocksTgt mu_top & frgnBlocksTgt mu_top]}.
{ rewrite /frgnTgt' /nu' /exportedTgt.
  move=> b; rewrite /in_mem /= /in_mem /=; case/andP=> XX YY.
  case: {YY}(andP YY)=> H5 H6.
  rewrite reestablish_DomTgt in XX.
  have RR: REACH m2 (fun b => getBlocks [:: rv2] b || sharedTgt mu_top b) b.
  { apply: (REACH_mono (fun b => getBlocks [:: rv2] b || sharedTgt nu b))=> //. 
    move: H6; rewrite /sharedTgt. 
    by rewrite reestablish_frgnBlocksTgt reestablish_pubBlocksTgt. }
  move: (REACH_subT _ RR); rewrite /sharedTgt /in_mem /=.
  case/orP; first by move=> ->; apply/orP; right.
  by move=> ->; apply/orP; left.
  rewrite replace_locals_locBlocksTgt=> b0 H7.
  by case: incr1=> _ []_; move/(_ b0); apply; rewrite /DomTgt H7. }

apply: Build_head_inv=> //.
{(*All (rel_inv_pred ...) mus'*)
  move {mus_eq allinv sub0S sub0T ctndS0 ctndT0 mapdS0 frametail}.
  elim: mus' all0 rel=> // a mus' IH.
  move=> /= []H1 H2 []H3 H4; split; last by apply: IH.
  case: H3=> incr3 sep3 disj3.

  have frgnSrc'_loc_pub: 
    {subset [predI frgnSrc' & locBlocksSrc a] <= pubBlocksSrc a}.
  { rewrite /frgnSrc' /nu' /exportedSrc eq.
    move=> b; rewrite /in_mem /= /in_mem /=; case/andP=> XX YY.
    case: disj3=> A B C D E.
    case: {XX}(andP XX)=> H5; case/andP=> H6 H7.
    rewrite reestablish_locBlocksSrc replace_locals_locBlocksSrc in H6.
    rewrite reestablish_DomSrc in H5.
    have RR: REACH m1 (fun b => getBlocks [:: rv1] b || sharedSrc mu_top b) b.
    { by apply: (REACH_mono (fun b => getBlocks [:: rv1] b || sharedSrc nu b)). }
    move: (REACH_subS _ RR); rewrite sharedSrc_iff_frgnpub /in_mem /=.
    case/orP=> H9; apply: C. 
    rewrite /in_mem /= /in_mem /=; apply/andP; split=> //.
    elimtype False.
    move: A; move/DisjointP; move/(_ b); rewrite YY.
    by move: (pubsrc_sub_locsrc H9); rewrite /in_mem /= => ->; case.
    by apply: Inj_wd.
    rewrite /nu replace_locals_locBlocksSrc=> b0 H8.
    by case: incr0_top=> _ []H9 _; apply: (H9 b0); apply/orP; left; rewrite H8. }

  apply: Build_rel_inv=> //; first by apply: (incr_trans incr3).
  { case: mu_top_mu'_incr=> AA []BB CC; case: sep3=> XX []YY ZZ; split.
  move=> b1 b2 d1 asInj asInj'.  
  case e: (as_inj mu_top b1)=> [[x y]|].
  move: (AA _ _ _ e); rewrite asInj'; case=> -> _.
  by apply: (XX _ _ _ asInj e).
  by rewrite as_inj_mu'_mu_top in asInj'; rewrite asInj' in e.
  by rewrite DomSrc_mu'_mu_top DomTgt_mu'_mu_top; split. }

  {(*disjinv a mu'*) 
  case: H1=> _ _ disj4.
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

  { move: (frgnSrc'_pub_frgn _ AA); rewrite /in_mem /= /in_mem /=; case/orP.
    { move=> CC; case: disj3=> DS _ _ W' U'; case: sep3=> DD []EE FF.
      case e: (as_inj a b1)=> [[? ?]|].
      move: (as_inj_locBlocks _ _ _ _ (Inj_wd _) e)=> eq'.
      move: (U' _ _ _ _ _ e aOf) eq'; case=> -> _; rewrite L=> L'.
      move: (pubsrc_sub_locsrc CC); rewrite /in_mem /= => CC'.
      by move: DS; move/DisjointP; move/(_ b1); rewrite L' CC'; case.
      by case: (DD _ _ _ e aOf)=> _; rewrite /DomTgt L /=; discriminate. }
    { move=> FF.
      have fOft: foreign_of mu_top b1 = Some (b2,d1).
      { case: (frgnSrc _ (Inj_wd _) _ FF)=> ? []? []G H.
        by move: (foreign_in_all _ _ _ _ G); rewrite aOf; case=> -> ->. }
      case: disj3=> _ _ _; move/(_ _ _ _ fOft)=> G H.
      by apply: G; apply/orP; right. }}

  move=> b1 b2 b2' d1 d1' AA BB.
  rewrite as_inj_mu'_mu_top in BB.
  case: disj3=> _ _ _ _ Catop.
  by apply: (Catop b1 b2 b2' d1 d1' AA BB). }(*END disjinv a mu'*)
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
{(*{subset RC.roots ...}*)
  move: aft1'=> /= aft1'.
  move: (RC.after_external_rc_basis (ge (cores_S (Core.i hd1))) aft1').
  move=> eq_hd1' b; rewrite /in_mem /= => H.
  have eq_hd1'': 
    RC.roots (ge (cores_S (Core.i hd1'))) (Core.c hd1')
    = (fun b => 
         getBlocks [:: rv1] b
      || RC.roots (ge (cores_S (Core.i hd1))) (Core.c hd1) b).
  { move: eq_hd1'. 
    set T := C \o cores_S.
    set P := fun ix (x : T ix) => 
               RC.roots (ge (cores_S ix)) x 
           = (fun b0 => 
              getBlocks [:: rv1] b0
              || RC.roots (ge (cores_S (Core.i hd1))) (Core.c hd1) b0).
    change (P (Core.i hd1) (cast T (sym_eq e1) (Core.c hd1'))
         -> P (Core.i hd1') (Core.c hd1')).
    by apply: cast_indnatdep'. }
  have eq_hd1''': 
    RC.roots my_ge (Core.c hd1') 
    = (fun b =>
         getBlocks [:: rv1] b
         || RC.roots (ge (cores_S (Core.i hd1))) (Core.c hd1) b).
  { rewrite -eq_hd1'' /RC.roots; extensionality b0.
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
    by apply: (sharedsrc_sub_domsrc J).
    rewrite /nu replace_locals_locBlocksSrc=> b0 M.
    case: incr1=> _ []; move/(_ b0)=> O _; apply: O.
    by apply/orP; left.
    apply/andP; split; first by rewrite eqL l.
    by apply: REACH_nil; apply/orP; left. }
  { move=> RB; case: (frame_vis fr0)=> vis_sub. 
    have vis0_b: vis mu0 b.
    { apply: vis_sub.
      rewrite /in_mem /=; move: RB; rewrite /RC.roots.
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
}(*END {subset RC.roots ...}*)
}(*END vis_inv*)

{ move=> b; rewrite frgnBlocksSrc_mu'_eq=> H1; apply/orP.
  move: (frgnSrc'_pub_frgn _ H1); rewrite /in_mem /= /in_mem /=; case/orP=> PT.
  left; rewrite join_all_locBlocksSrc; left.
  by rewrite /=; apply/orP; left; apply: (pubsrc_sub_locsrc PT).
  move: (head_ctndS hdinv PT); rewrite mus_eq /=; case/orP.
  case/orP=> L.
  move: H1; rewrite /frgnSrc'; case/andP=> _; case/andP.
  rewrite reestablish_locBlocksSrc replace_locals_locBlocksSrc.
  by move: L; rewrite /in_mem /= => ->.
  by left; rewrite join_all_shift_locBlocksSrcE; apply/orP; right.
  case/andP=> _ F; right.
  rewrite join_all_shift_frgnBlocksSrcE; rewrite /in_mem /= /in_mem /=.
  by apply/andP; split.
  refine mu0. (*an unnecessary assumption in lemma statement*) }

{ move=> b; rewrite frgnBlocksTgt_mu'_eq=> H1; apply/orP.
  move: (frgnTgt'_pub_frgn _ H1); rewrite /in_mem /= /in_mem /=; case/orP=> PT.
  left; rewrite join_all_locBlocksTgt; left.
  by rewrite /=; apply/orP; left; apply: (pubtgt_sub_loctgt PT).
  move: (head_ctndT hdinv PT); rewrite mus_eq /=; case/orP.
  case/orP=> L.
  move: H1; rewrite /frgnTgt'; case/andP=> _; case/andP.
  rewrite reestablish_locBlocksTgt replace_locals_locBlocksTgt.
  by move: L; rewrite /in_mem /= => ->.
  by left; rewrite join_all_shift_locBlocksTgtE; apply/orP; right.
  case/andP=> _ F; right.
  rewrite join_all_shift_frgnBlocksTgtE; rewrite /in_mem /= /in_mem /=.
  by apply/andP; split.
  refine mu0. (*an unnecessary assumption in lemma statement*) }

{ move=> b b' d' /=; move: (mapdS0 b b' d').
  move: (@head_mapdS _ _ _ _ _ _ _ _ _ hdinv b b' d')=> mapH map0.
  rewrite /mu' replace_externs_foreign; case e: (frgnSrc' b)=> //.
  rewrite reestablish_extern_of replace_locals_locBlocksSrc.
  case f: (locBlocksSrc mu0 b)=> // asInj.
  move: (frgnSrc'_pub_frgn _ e); rewrite /in_mem /=; case/orP.
  move=> PS; case: (pubSrcAx _ (Inj_wd _) _ PS)=> x []y []lOf PT.
  rewrite /as_inj /join; case g: (extern_of _ _)=> [[? ?]|].
  rewrite join_all_shift_extern_ofE in g; move: g; move/join2P; case=> H1 H2. 
  by rewrite (extern_in_all _ _ _ _ H1) in asInj; case: asInj=> -> ->.
  have lOf': local_of mu_top b = Some (b',d').
  { rewrite (local_in_all _ _ _ _ _ lOf) in asInj. 
    by case: asInj=> <- <-.
    by apply: Inj_wd. }
  rewrite join_all_shift_local_ofE /join; first by rewrite lOf'.
  move: (relinv_AllDisjointLS rel).
  rewrite !map_comp /= -list_map_compose /= => D; clear - D. 
  { by elim: mus' D=> //= a mus' IH []D E; split=> //; apply: IH. }
  rewrite /in_mem /= => F. 
  have fOf: foreign_of mu_top b = Some (b',d').
  { case: (frgnSrc _ (Inj_wd _) _ F)=> ? []? []H I.
    by move: (foreign_in_all _ _ _ _ H); rewrite asInj; case=> -> ->. }
  move: (mapH fOf)=> /=; rewrite mus_eq /= /as_inj /=.
  have IN: (forall mu, In mu mus' -> In mu mus).
  { by rewrite mus_eq /= => ? ?; right. }
  rewrite (extern_of_trash_join_all_sub trinv) //.
  rewrite (join2_extern_mu0_trash trinv).
  rewrite (extern_of_trash_join_all'_sub trinv) //.
  rewrite /join.
  case g: (extern_of _ _)=> [//|].
  have lN: local_of mu0 b = None.
  { case h: (local_of mu0 b)=> // [[? ?]].
    by case: (local_DomRng _ (Inj_wd _) _ _ _ h); rewrite f. }
  rewrite lN join_all_shift_local_ofE /=.
  have ltopN: local_of mu_top b = None.
  { case h: (local_of mu_top b)=> // [[? ?]].
    have i: locBlocksSrc mu_top b = false.
    { move: (frgnsrc_sub_extsrc F).
      move/extBlocksSrc_locBlocksSrc.
      by move/(_ (Inj_wd _)). }
    by case: (local_DomRng _ (Inj_wd _) _ _ _ h); rewrite i. }
  by move=> H; rewrite /join ltopN; apply: H.
  move: (head_AllDisjointLS hdinv); rewrite mus_eq.
  by move=> /= []D; rewrite -map_comp; apply.
  by rewrite mus_eq /=; left. }

{ move: sub0S=> /=; clear - shrdS_mu0_mu'; elim: mus'=> // a mus' IH shrd.
  by move=> b H; move: (shrd _ H); apply: shrdS_mu0_mu'. }

{ move: sub0T=> /=; clear - shrdT_mu0_mu'; elim: mus'=> // a mus' IH shrd.
  by move=> b H; move: (shrd _ H); apply: shrdT_mu0_mu'. }
}(*END head_inv*)

split; first by move: allinv; rewrite mus_eq.

{(*frame_all mu_trash' ...*)
  rewrite mus_eq /=; move: frametail.
  move: st1''_eq st2''_eq pop1 pop2; move=> -> ->.
  case/popCoreE=> wff []in_st1; rewrite /updStack; case; move=> fntbl1_eq st1_eq.
  case/popCoreE=> wfg []in_st2; rewrite /updStack; case; move=> fntbl2_eq st2_eq. 

  have D: All [eta DisjointLS mu_top] [seq (Inj.mu \o frame_mu0) x | x <- mus].
  { by apply: (head_AllDisjointLS hdinv). }

  rewrite mus_eq /= in hdinv; clear - mus_eq hdinv trinv sub0S sub0T D.
  move: (head_ctnsS hdinv) (head_ctnsT hdinv)=> ctnsS ctnsT; clear hdinv.
  elim: mus' sub0S sub0T tl1 tl2 mus mus_eq trinv D=> // a mus' IH; case: a.
  move=> mua m1a m2a vala sub0S sub0T tl1 tl2 mus mus_eq trinv D.
  case/frame_all_inv=> ca []tl1' []da []tl2'.
  case=> -> -> []pfa []cda []e1a []sig1a []vals1a []e2a []sig2a []vals2a.
  case=> AA BB CC DD EE FF GG /=; split.
  exists pfa,cda,e1a,sig1a,vals1a,e2a,sig2a,vals2a.
  split=> //.
  
  { move=> b F; move: (BB _ F)=> /=; case/orP.
  rewrite join_all_shift_locBlocksSrcE=> G; rewrite /in_mem /=; apply/orP.
  by left; apply/orP; right.
  have G: (sharedSrc mu_top b).
  { apply: ctnsS; apply: sub0S=> /=; rewrite /in_mem /= sharedSrc_iff_frgnpub.
    by rewrite F. 
    by apply: Inj_wd. }
  rewrite sharedSrc_iff_frgnpub in G. 
  case: (orP G)=> H.
  move=> I; apply/orP; right.
  rewrite join_all_shift_frgnBlocksSrcE; rewrite /in_mem //=; apply/andP.
  by split.
  move=> I; apply/orP; left.
  rewrite join_all_shift_locBlocksSrcE; rewrite /in_mem /=; apply/orP; left.
  by apply: (pubsrc_sub_locsrc H).
  by apply: Inj_wd. }

  { move=> b F; move: (CC _ F)=> /=; case/orP.
  rewrite join_all_shift_locBlocksTgtE=> G; rewrite /in_mem /=; apply/orP.
  by left; apply/orP; right.
  have G: (sharedTgt mu_top b).
  { apply: ctnsT; apply: sub0T=> /=; rewrite /in_mem /= /sharedTgt.
    by rewrite F. }
  case: (orP G)=> H.
  move=> I; apply/orP; right.
  rewrite join_all_shift_frgnBlocksTgtE; rewrite /in_mem //=; apply/andP.
  by split.
  move=> I; apply/orP; left.
  rewrite join_all_shift_locBlocksTgtE; rewrite /in_mem /=; apply/orP; left.
  by apply: (pubtgt_sub_loctgt H). }

  { move=> b b' d' F; move: (DD _ _ _ F)=> /= => G.
    apply: (as_inj_shift_mu_trash trinv)=> //.
    by case: (trash_disj_S trinv); rewrite/DisjointLS /= DisjointC.
    by rewrite mus_eq=> ? ? /=; right; right. }

  { apply: IH=> //. 
    clear - sub0S EE; elim: mus' sub0S EE=> //= a mus' IH A B.
    by move=> ? C; apply: A; apply: B.    
    clear - sub0T FF; elim: mus' sub0T FF=> //= a mus' IH A B.
    by move=> ? C; apply: A; apply: B. 
    move: trinv; rewrite mus_eq.
    apply: trash_inv_sub.
    move=> mu1 /= [].
    by move=> <-; left.
    by move=> IN; right; right.
    apply: (All_listsub (l:=[seq (Inj.mu \o frame_mu0) x | x <- mus]))=> //.
    move=> a /= => []; case.
    by move=> <-; rewrite mus_eq /=; left.                     
    by rewrite mus_eq /=; right; right. } 
}(*END frame_all mu_trash' ...*)

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
case: (R_inv inv)=> pf []mu_trash []mu_top []mus []mu_eq.
move=> rc trinv hdinv tlinv.
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

  set fS := mapped j.
  
  set fT := (fun b : block => valid_block_dec m2 b).

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
  move: (H1 main vals1 c m1 j vals2  m2 fS fT dS dT).
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

  { rewrite /fS=> b0 H; move: (inject_REACH_closed _ _ _ inj); apply.
    move: H; apply: REACH_mono=> b1.
    rewrite -(genvs_domain_eq_isGlobal _ _ (my_ge_S ix)); case/orP.
    move=> isGlob; move: (meminj_preserves_globals_isGlobalBlock _ _ pres _ isGlob).
    by rewrite /mapped=> ->.
    move=> get1; case: (getBlocks_inject _ _ _ vinj _ get1)=> x []y []map get2.
    by rewrite /mapped map. }

  { rewrite /fT=> b0 H. 
    have r2: REACH m2 (fun b' =>
         isGlobalBlock my_ge b' || getBlocks vals2 b') b0.
    { suff ->: 
      (fun b' => isGlobalBlock my_ge b' || getBlocks vals2 b')
    = (fun b' => isGlobalBlock (ge (cores_T ix)) b' || getBlocks vals2 b'). 
      by apply: H. 
      extensionality b1; rewrite orbC (orbC (isGlobalBlock (ge (cores_T ix)) _)).
      case l: (getBlocks _ _)=> //=.
      suff: is_true (isGlobalBlock my_ge b1) <-> 
            is_true (isGlobalBlock (ge (cores_T ix)) b1).
      case m: (isGlobalBlock my_ge _).
      by case; move/(_ erefl)=> ->.
      case n: (isGlobalBlock _ _)=> //.
      by case=> _; move/(_ erefl). 
      by rewrite -isGlob_iffT. }
    by apply: valid_dec; apply: reach. }

  { by apply: (inject_REACH_closed _ _ _ inj). }

  { rewrite /fS /dS /mapped=> b0; case l: (j b0)=> [[x y]|//].
    apply Mem.valid_block_inject_1 with (m1:=m1) (m2:=m2) in l=> //. 
    by move=> _; apply: valid_dec. }

  { rewrite /fS /dS /mapped=> b1; case l: (j b1)=> [[x y]|//]=> _.
    exists x,y; split=> //.
    apply Mem.valid_block_inject_2 with (m1:=m1) (m2:=m2) in l=> //. 
    by apply: valid_dec. }

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
    move=> b1; rewrite /fS /mapped; case l: (j b1)=> [[x y]|//].
    exists x,y; split=> //.
    apply Mem.valid_block_inject_2 with (m1:=m1) (m2:=m2) in l=> //.
    by apply: valid_dec.
    rewrite /fS /dS /mapped=> b0; case l: (j b0)=> [[x y]|//].
    apply Mem.valid_block_inject_1 with (m1:=m1) (m2:=m2) in l=> //.    
    by move=> _; apply: valid_dec. }

  set mu_top := Inj.mk mu_top_wd.
  
  have mu_top_val: sm_valid mu_top m1 m2.
  { split.
    by move=> b1; rewrite /DOM /DomSrc; case/orP=> //=; apply: valid_dec'.
    by move=> b2; rewrite /RNG /DomTgt; case/orP=> //=; apply: valid_dec'. }

  set mu_trash := Build_frame_pkg mu_top_val.

  apply: Build_R=> /=.
  exists erefl,mu_trash,mu_top,[::]=> /=.
  split=> //.
  rewrite /mu_top0 /initial_SM; f_equal.
  by rewrite /restrict; extensionality b0; case: (vis _ _).
  by rewrite predI_refl.
  by rewrite predI_refl.
  by rewrite predI_refl.
  by rewrite predI_refl.
  rewrite /restrict; extensionality b0.
  rewrite /vis /= /fS /mapped /in_mem /=.  
  case k: (j b0)=> [[? ?]/=|//].
  by rewrite /join2 k Pos.eqb_refl Zeq_bool_refl /=.
  by apply: (inject_REACH_closed _ _ _ inj).

  apply: Build_trash_inv=> //.
  rewrite /= /fS /mapped=> b0 isGlob.
  move: (meminj_preserves_globals_isGlobalBlock _ _ pres _ isGlob).
  by rewrite /mapped=> ->.
  split=> //; first by move=> b1 b2 b2' d2 d2'=> ->; case=> -> ->.  
  by apply: Build_trash_minimal.

  exists erefl; apply: Build_head_inv=> //.
  apply: Build_vis_inv; rewrite /= /RC.roots /vis /mu_top0 /= /fS.

  have ->: RC.args c = vals1.
  { by apply: (RC.initial_core_args g). }

  have ->: RC.rets c = [::].
  { by apply: (RC.initial_core_rets g). }

  have ->: RC.locs c = (fun _ => false).
  { by apply: (RC.initial_core_locs g). }

  move=> /=; rewrite /in_mem {2}/getBlocks /= => b1.
  suff: isGlobalBlock my_ge b1 || getBlocks vals1 b1 -> mapped j b1.
  move=> H2; case/orP=> H3; apply: H2.
  case: (orP H3)=> //. discriminate.  

  case/orP.
  move=> isGlob. 
  move: (meminj_preserves_globals_isGlobalBlock _ _ pres _ isGlob).
  by rewrite /mapped=> ->.
  move=> get1; case: (getBlocks_inject _ _ _ vinj _ get1)=> x []y []map get2.
  by rewrite /mapped map. 

  rewrite /frgnS_mapped /= => b0 b' d'.
  case k: (fS b0)=> //.
  by rewrite /as_inj /join /mu_top0 /= => ->.

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
         (t := effect_instance (sem (cores_S (Core.i c1)))) 
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
    (sem (cores_S (Core.i c1)))
    (ge (cores_S (Core.i c1))) U1 (Core.c c1) m1 c1' m1'.

  { move: (STEP_EFFSTEP STEP); rewrite/effstep0=> [][] c1'' [] STEP0' ST1''. 
    by rewrite ST1'' in ST1'; rewrite -(updCore_inj_upd ST1'). }

(* specialize core diagram at module (Core.i c1) *)
move: (effcore_diagram _ _ _ _ (sims (Core.i c1))).  
move/(_ _ _ _ _ _ EFFSTEP).
case: (R_inv INV)=> pf []mu_trash []mupkg []mus []mu_eq.
move=> rclosed trinv []pf2 hdinv tlinv.

have U1_DEF': forall b ofs, U1 b ofs -> vis mupkg b. 

  { case: hdinv=> mtch ?; case=> visinv _ _ _ _ _ b ofs A; move: (U1'_EQ _ _ A).
    rewrite/RC.reach_set=> B; apply match_visible in mtch; apply: mtch.
    move: B; apply REACH_mono with (B1 := RC.roots _ _)=> b'=> B.
    apply: (visinv b'); move: B; apply: RC.roots_domains_eq.
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
set c2''   := cast' (peek_ieq INV) c2'.
set st2'   := updCore st2 (Core.upd c2 c2'').
set data'  := (existT (fun ix => core_data (sims ix)) (Core.i c1) cd'). 
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

 exists pf, mu_trash, mupkg', mus; split=> //.

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
   exists erefl=> /=.
   apply: (@head_inv_step 
     mupkg m1 m2 mu_top' m1' m2' (head_valid hdinv) INCR SEP LOCALLOC
     (c INV) (d INV) pf c1' c2'' _ _ _ mus
     (STACK.pop (CallStack.callStack (s1 INV))) 
     (STACK.pop (CallStack.callStack (s2 INV))) U1 hdinv frameall)=> //=.
   have ->: cast'' pf c2'' = c2' by apply: cast_cast_eq'.
   by []. }

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
     exists n, effstepN (sem (cores_T (Core.i c1)))
               (ge (cores_T (Core.i c1))) n U2 
               (cast'' pf (Core.c (d INV))) m2 c2' m2'.
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
  effstep_plus (sem (cores_T (Core.i c2)))
  (ge (cores_T (Core.i c2))) U2 (Core.c (d INV)) m2 c2'' m2'. 

 { set T := C \o cores_T.
   set P := fun ix (x : T ix) (y : T ix) => 
             effstep_plus (sem (cores_T ix))
             (ge (cores_T ix)) U2 x m2 y m2'.
   change (P (Core.i c2) (Core.c c2) c2''); apply: cast_indnatdep2.
   by move: STEP'; have ->: pf = peek_ieq INV by apply: proof_irr. }

by left; move: STEP''; apply: stepPLUS_STEPPLUS.

have STEP'': 
  effstep_star (sem (cores_T (Core.i c2)))
  (ge (cores_T (Core.i c2))) U2 (Core.c c2) m2 c2'' m2'. 

 { set T := C \o cores_T.
   set P := fun ix (x : T ix) (y : T ix) => 
             effstep_star (sem (cores_T ix))
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

have mu_wd: SM_wd mu. 
{ by apply: (R_wd INV). }

have INV': R data (Inj.mk mu_wd) st1 m1 st2 m2.
{ by apply: INV. }

case: (aft2 HLT1 POP1 AFT1 INV')=> 
  rv2 []st2'' []st2' []cd' []HLT2 CTX2 POP2 AFT2 INV''.
exists st2',m2,cd',mu.
split; first by apply: intern_incr_refl.
split; first by apply: sm_inject_separated_refl.
split; first by apply: sm_locally_allocated_refl.
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
case: (R_inv inv')=> pf []mu_trash []mupkg []mus []mu_eq.
move=> rclosed trinv []pf2 hdinv tlinv; move: (head_match hdinv)=> mtch0.

have hlt10: 
  halted (sem (cores_S (Core.i (c inv')))) (Core.c (c inv)) 
= Some v1.
{ move: hlt1; rewrite /= /LinkerSem.halted.
  case inCtx1: (inContext c1)=> //=.
  case hlt10: (LinkerSem.halted0 c1)=> [v1'|//]; case=> <-.
  by move: hlt10; rewrite /LinkerSem.halted0 /c /= /RC.halted=> ->. }

case: (core_halted (sims (Core.i (c inv'))) _ _ _ _ _ _ mtch0 hlt10).
move=> v2' []inj []rc1 []rc2 []vinj []vdef hlt2'.

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
have g: halted (sem (cores_T (Core.i (c inv'))))
               (cast'' pf (Core.c (d inv')))  
      = Some rv.
{ set T := C \o cores_T.
  set P := fun ix (x : T ix) => 
             halted (sem (cores_T ix)) x  
           = Some rv.
  change (P (Core.i (c inv')) (cast T (sym_eq pf) (Core.c (d inv')))).
  by apply: cast_indnatdep; rewrite /P; rewrite -f. }
by rewrite -g. }(*END Case: halted*)

Qed.

End linkingSimulation.

Print Assumptions link.