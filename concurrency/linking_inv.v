(* standard Coq libraries *)

Require Import JMeq.

(* msl imports *)

Require Import Axioms. (*for proof_irr*)

(* sepcomp imports *)

Require Import sepcomp. Import SepComp. 
Require Import arguments.

Require Import pos.
Require Import stack.
Require Import cast.
Require Import pred_lemmas.
Require Import seq_lemmas.
Require Import wf_lemmas.
Require Import reestablish.
Require Import inj_lemmas.
Require Import join_sm.
Require Import reach_lemmas.
Require Import compcert_linking.
Require Import compcert_linking_lemmas.
Require Import disjointness.
Require Import rc_semantics.
Require Import rc_semantics_lemmas.


(* compcert imports *)

Require Import AST.    (*for ident*)
Require Import Globalenvs.   
Require Import Memory.   

(* ssreflect *)

Require Import ssreflect ssrbool ssrfun seq eqtype fintype.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Values.   
Require Import nucular_semantics.

(** * Linking Invariant *)

(** This file states the simulation invariant used in Theorem 2. *)

Import Wholeprog_sim.
Import SM_simulation.
Import Linker. 
Import Modsem.
 
Section typingInv.

Variable N : pos.

Variable cores : 'I_N -> Modsem.t.

Variable fun_tbl : ident -> option 'I_N.

Let linker := effsem N cores fun_tbl.

Definition sig_of (c : Core.t cores) := 
  match at_external (cores c.(Core.i)).(sem) c.(Core.c) with
    | None => None 
    | Some (ef,sg,args) => Some (ef_sig ef)
  end.

Fixpoint tys_agree_rec (sg : signature) (s : seq.seq (Core.t cores)) :=
  if s is [:: c & s'] then 
    if sig_of c is Some sg' then [/\ sg=sg' & tys_agree_rec c.(Core.sg) s']
    else False
  else True.

Definition tys_agree (s : seq.seq (Core.t cores)) :=
  if s is [:: c & s'] then tys_agree_rec c.(Core.sg) s'
  else True.

End typingInv.

Section linkingInv.

  Variable N : pos.

Variable cores_S cores_T : 'I_N -> Modsem.t. 
Variable rclosed_S : forall i : 'I_N, RCSem.t (cores_S i).(sem) (cores_S i).(ge).
Variable nucular_T : forall i : 'I_N, Nuke_sem.t (cores_T i).(sem).

Variable fun_tbl : ident -> option 'I_N.

Variable sims : forall i : 'I_N, 
  let s := cores_S i in
  let t := cores_T i in
  SM_simulation_inject s.(sem) t.(sem) s.(ge) t.(ge).

Variable my_ge : ge_ty.
Variable my_ge_S : forall (i : 'I_N), genvs_domain_eq my_ge (cores_S i).(ge).
Variable my_ge_T : forall (i : 'I_N), genvs_domain_eq my_ge (cores_T i).(ge).

(*Four new assumptions*)
Variable find_symbol_up_S: forall i id b,
    Genv.find_symbol (cores_S i).(ge) id = Some b ->
    Genv.find_symbol my_ge id = Some b.

Variable find_symbol_up_T: forall i id b,
    Genv.find_symbol (cores_T i).(ge) id = Some b ->
    Genv.find_symbol my_ge id = Some b.

Variable all_gvars_includedS: forall i b,
     gvars_included (Genv.find_var_info (cores_S i).(ge) b) (Genv.find_var_info my_ge b).

Variable all_gvars_includedT: forall i b,
     gvars_included (Genv.find_var_info (cores_T i).(ge) b) (Genv.find_var_info my_ge b).  

Let types := fun i : 'I_N => (sims i).(core_data).
Let ords : forall i : 'I_N, types i -> types i -> Prop 
  := fun i : 'I_N => (sims i).(core_ord).

Let linker_S := effsem N cores_S fun_tbl.
Let linker_T := effsem N cores_T fun_tbl.

Let ord := @Lex.ord N types ords.

Notation cast'  pf x := (cast (C \o cores_T) pf x).
Notation cast'' pf x := (cast (C \o cores_T) (sym_eq pf) x).
Notation rc_cast'  pf x := (cast (RC.state \o C \o cores_T) pf x).
Notation rc_cast'' pf x := (cast (RC.state \o C \o cores_T) (sym_eq pf) x).

Section frame_inv.

Import Core.

Variables (c : t cores_S) (d : t cores_T). 
Variable  pf : c.(i)=d.(i).

Require Import Coqlib. (*for Forall2*)

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

(** Initial core asserts that we match w/ SM_injection
  [initial_SM DomS DomT
    (REACH m1 (fun b => isGlobalBlock ge1 b || getBlocks vals1 b))
    (REACH m2 (fun b => isGlobalBlock ge2 b || getBlocks vals2 b)) j)]
where the clauses beginning REACH... give frgnSrc/Tgt respectively. *)

(** I.e., we establish initially that
  [fun b => isGlobalBlock ge1 b || getBlocks vals1 b]
is a subset of the visible set for the injection of the initialized
core. *)

(** We record this fact (really, a slight modification of the invariant
that accounts for return values as well) as an invariant of execution
for both the head and tail cores. Then the guarantees we get from RC
executions (that write effects are limited to blocks in the RC of
initial args, rets, local blocks) imply that effects are also a
subset of the visible region for each core. *)

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

Lemma findSym_findSym_down_S ix id b :
  Genv.find_symbol my_ge id = Some b -> 
  exists id', Genv.find_symbol (ge (cores_S ix)) id' = Some b.
Proof.
  move=> H.
  eapply invSym_findSymS. apply Genv.find_invert_symbol. apply H. 
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

Lemma findSym_findSym_down_T ix id b :
  Genv.find_symbol my_ge id = Some b -> 
  exists id', Genv.find_symbol (ge (cores_T ix)) id' = Some b.
Proof.
  move=> H.
  eapply invSym_findSymT. apply Genv.find_invert_symbol. apply H. 
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

Lemma findVar_findVarS ix inf b :
  Genv.find_var_info my_ge b = Some inf -> 
  exists inf', Genv.find_var_info (ge (cores_S ix)) b = Some inf'.
Proof.
case: (my_ge_S ix)=> H1 H2.
rewrite /genv2blocks /= in H2; case: H2=> H2 H3.
case: {H2}(H2 b)=> H2 H4 H5.
case: H2; first by exists inf.
by move=> x H6; exists x.
Qed.

Lemma findVar_findVarT ix inf b :
  Genv.find_var_info my_ge b = Some inf -> 
  exists inf', Genv.find_var_info (ge (cores_T ix)) b = Some inf'.
Proof.
case: (my_ge_T ix)=> H1 H2.
rewrite /genv2blocks /= in H2; case: H2=> H2 H3.
case: {H2}(H2 b)=> H2 H4 H5.
case: H2; first by exists inf.
by move=> x H6; exists x.
Qed.

Lemma findVar_findVarS_None ix b :
  Genv.find_var_info my_ge b = None -> 
  Genv.find_var_info (ge (cores_S ix)) b = None.
Proof.
case: (my_ge_S ix)=> H1 H2.
rewrite /genv2blocks /= in H2; case: H2=> H2 H3.
case: {H2}(H2 b)=> H2 H4 H5.
case g: (Genv.find_var_info _ _)=> //[gv].
case: H4; first by exists gv.
by move=> x; rewrite H5.
Qed.

Lemma findVar_findVarT_None ix b :
  Genv.find_var_info my_ge b = None -> 
  Genv.find_var_info (ge (cores_T ix)) b = None.
Proof.
case: (my_ge_T ix)=> H1 H2.
rewrite /genv2blocks /= in H2; case: H2=> H2 H3.
case: {H2}(H2 b)=> H2 H4 H5.
case g: (Genv.find_var_info _ _)=> //[gv].
case: H4; first by exists gv.
by move=> x; rewrite H5.
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
case: (findVar_findVarS ix j)=> x=> ->; split=> //=.
by move=> _; apply/orP; right.
move: (@invSym_findSymS_None ix _ i)=> H1.
case k: (Genv.invert_symbol _ _)=> [id|].
move: (Genv.invert_find_symbol _ _ k)=> H2. 
by elimtype False; apply: (H1 _ H2).
case l: (Genv.find_var_info _ _)=> [inf|].
by rewrite (findVar_findVarS_None _ j) in l.
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
case: (findVar_findVarT ix j)=> x=> ->; split=> //=.
by move=> _; apply/orP; right.
move: (@invSym_findSymT_None ix _ i)=> H1.
case k: (Genv.invert_symbol _ _)=> [id|].
move: (Genv.invert_find_symbol _ _ k)=> H2. 
by elimtype False; apply: (H1 _ H2).
case l: (Genv.find_var_info _ _)=> [inf|].
by rewrite (findVar_findVarT_None _ j) in l.
by [].
Qed.

Lemma isGlob_iffS' ix1 ix2 b :
  isGlobalBlock (ge (cores_S ix1)) b <-> isGlobalBlock (ge (cores_S ix2)) b. 
Proof. by split; rewrite -!isGlob_iffS. Qed.

Lemma isGlob_iffST' ix1 ix2 b :
  isGlobalBlock (ge (cores_S ix1)) b <-> isGlobalBlock (ge (cores_T ix2)) b. 
Proof. by split; rewrite -isGlob_iffS -isGlob_iffT. Qed.

Lemma find_symbol_down_S i id b:
  Genv.find_symbol my_ge id = Some b ->
  Genv.find_symbol (ge (cores_S i)) id = Some b.
Proof.
  move=> GF. destruct (findSym_findSym_down_S i GF).
  destruct (ident_eq x id); subst; trivial.
  apply find_symbol_up_S in H.
  elim (Genv.global_addresses_distinct _ n H GF). trivial. 
Qed.

Lemma find_symbol_down_T i id b:
  Genv.find_symbol my_ge id = Some b ->
  Genv.find_symbol (ge (cores_T i)) id = Some b.
Proof.
  move=> GF. destruct (findSym_findSym_down_T i GF).
  destruct (ident_eq x id); subst; trivial.
  apply find_symbol_up_T in H.
  elim (Genv.global_addresses_distinct _ n H GF). trivial. 
Qed.

Lemma load_store_init_S m b i: forall il k,
      Genv.load_store_init_data my_ge m b k il ->
      Genv.load_store_init_data (ge (cores_S i)) m b k il.
Proof.
  induction il; simpl; intros z LDI; trivial.
  destruct a; try destruct LDI; eauto.
  destruct H as [b' [FS LD]].
  apply (find_symbol_down_S i) in FS. 
  split; eauto. 
Qed.

Lemma load_store_init_T m b i: forall il k,
      Genv.load_store_init_data my_ge m b k il ->
      Genv.load_store_init_data (ge (cores_T i)) m b k il.
Proof.
  induction il; simpl; intros z LDI; trivial.
  destruct a; try destruct LDI; eauto.
  destruct H as [b' [FS LD]].
  apply (find_symbol_down_T i) in FS. 
  split; eauto. 
Qed.

Lemma mrr_down_S: forall m, mem_respects_readonly my_ge m ->
                     forall i, mem_respects_readonly (cores_S i).(ge) m.
 Proof. move=> m MRR i b gv FV P. 
     destruct (@gvars_cohereD _ _ _ _ _ _ (all_gvars_includedS i) _ _ FV) as [gv2 [? [? [? ?]]]].
     rewrite H1 H2 in P.
     destruct (MRR _ _ H P) . split; trivial. destruct H4 as [? _].
     rewrite H0. clear H0. 
     eapply load_store_init_S; eauto. 
Qed. 

Lemma mrr_down_T: forall m, mem_respects_readonly my_ge m ->
                     forall i, mem_respects_readonly (cores_T i).(ge) m.
 Proof. move=> m MRR i b gv FV P. 
     destruct (@gvars_cohereD _ _ _ _ _ _ (all_gvars_includedT i) _ _ FV) as [gv2 [? [? [? ?]]]].
     rewrite H1 H2 in P.
     destruct (MRR _ _ H P) . split; trivial. destruct H4 as [? _].
     rewrite H0. clear H0. 
     eapply load_store_init_T; eauto. 
Qed. 

End glob_lems.

Section vis_inv.

Import Core.

Record vis_inv (c : t cores_S) (B : block -> bool) mu : Type :=
  { vis_sup : {subset (RC.roots (cores_S c.(i)).(ge) (RC.mk c.(Core.c) B)) <= vis mu} }.

End vis_inv.

(** ** Callstack Frame Invariant *)

(** [frame_inv] is the invariant that relates a pair of (source--target) cores 
  at a given frame on the source--target callstacks. *)

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
  ; frame_vis   : exists B, 
                  [/\ vis_inv c B mu0
                    & RCSem.I (rclosed_S c.(i)) c.(Core.c) m10 B]

    (* target mu invariants *)
  ; frame_domt  : DomTgt mu0 = valid_block_dec m20
  ; frame_nukeI : Nuke_sem.I (nucular_T d.(i)) d.(Core.c) m20

    (* invariants relating m10,m20 to active memories m1,m2*)
  ; frame_fwd1  : mem_forward m10 m1
  ; frame_fwd2  : mem_forward m20 m2

  ; frame_rdoS: RDOnly_fwd m10 m1 (ReadOnlyBlocks my_ge)
  ; frame_rdoT: RDOnly_fwd m20 m2 (ReadOnlyBlocks my_ge)

  ; frame_unch1 : Mem.unchanged_on [fun b ofs => 
                    [/\ locBlocksSrc nu0 b & pubBlocksSrc nu0 b=false]] m10 m1
  ; frame_unch2 : Mem.unchanged_on (local_out_of_reach nu0 m10) m20 m2 }.

End frame_inv.

Definition local_inv mu0 mu: Prop :=
  local_of mu0 = restrict (as_inj mu) (locBlocksSrc mu0).


(*The following invariant shall hold amongst cores, not within them*)
Definition sm_inject_separated' (mu mu' : SM_Injection) (m1 m2 : Memory.mem) :=
(forall (b1 b2 : block) (d : Z),
 as_inj mu b1 = None ->
 as_inj mu' b1 = Some (b2, d) -> DomSrc mu b1 = false /\ DomTgt mu b2 = false) /\
(forall b1 : block,
 locBlocksSrc mu' b1 = true -> ~ Mem.valid_block m1 b1) /\
(forall b2 : block,
 locBlocksTgt mu' b2 = true -> ~ Mem.valid_block m2 b2).

Record rel_inv mu0 mu m10 m20 m1 (*new*) : Prop :=
  { (* invariants relating mu0,mu *)    
    frame_incr       : incr mu0 mu
  ; new_sep          : sm_inject_separated' mu0 mu m10 m20                          
(*NOTE: my_ge has the same domain as any ge*)
  ; frame_gsep       : globals_separate my_ge mu0 mu 
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
Proof. by case: rinv=> _ _ _; case; move/DisjointC. Qed.

Lemma relinv_DisjointLT : DisjointLT mu (frame_mu0 pkg).
Proof. by case: rinv=> _ _ _; case=> _; move/DisjointC. Qed.

Lemma relinv_consistent : Consistent mu (frame_mu0 pkg).
Proof. by case: rinv=> _ _ _; case=> _ _ _ _; move/consistentC. Qed.

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

(** ** Running Cores Invariant *)

Record head_inv cd (mu : Inj.t) mus m1 m2 : Prop :=
  { head_match : (sims c.(i)).(match_state) cd mu 
                 c.(Core.c) m1 (cast'' pf d.(Core.c)) m2 
  ; head_rel   : All (rel_inv_pred m1 mu) mus 
  ; head_vis   : exists B, 
                 [/\ vis_inv c B mu 
                   & RCSem.I (rclosed_S c.(i)) c.(Core.c) m1 B]
  ; head_domt  : DomTgt mu = valid_block_dec m2 
  ; head_nukeI : Nuke_sem.I (nucular_T d.(i)) d.(Core.c) m2
  ; head_gfi   : globalfunction_ptr_inject my_ge (as_inj mu)
  }.

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
by case: inv=> // A _ _ _ _ _; apply: (match_validblocks _ A).
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
(*Edited: Santiago*)
(* locinv:
by rewrite /init_mu /initial_SM /local_inv /as_inj join_None_rightneutral /=; apply rel.*)
case: rel=> _ newsep (*gsep*) _ _; move: newsep.
rewrite /sm_inject_separated' /init_mu /j initial_SM_as_inj => //=. 
case => sep1 [seplocS seplocT] //=.

case: rel=> _. move=> loc gsep0 disj0 sub0.
move => p b2 d0 H HH.
unfold globals_separate in gsep0.
eapply gsep0.
+ by apply H.
+ unfold init_mu, initial_SM, as_inj, join, j in HH; simpl in HH.
  destruct (as_inj mu p) eqn:map1; try (destruct p0); inversion HH. by eauto.
(*End Edit*)
apply: Build_disjinv.
by rewrite predI01.
by rewrite predI01.
{
move=> b; move/andP=> /= []fS lS.
case: rel=> _ _ _; case=> d1 d2; move/(_ b)=> H _ _ _; apply: H.
apply/andP; split=> //=.
move: (frgnS_sub_vis fS); case/orP=> H.
move: d1; move/DisjointP; move/(_ b); rewrite H.
by move: lS; rewrite /in_mem /= => ->; case.
by []. }
move=> b1 b2 d0; rewrite /foreign_of /=.
case: rel=> _ _ _; case=> d1 d2 _ H _ _.
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
case: rel=> _ _ _; case=> _ _ _ _.
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
case: rel=> _ _ _; case=> d1 _ p1 _ _ _; apply: p1; apply/andP; split=> //.
case: (orP H3)=> // H4; move: d1; move/DisjointP; move/(_ b).
by move: H2 H4; rewrite /in_mem /= => -> ->; case.
by apply: IH.
Qed.

Let lo' := replace_locals mu pubS' pubT'.

Lemma lo_wd : SM_wd lo'.
Proof.
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

Lemma local_asinj_restrict: forall mu,
                              SM_wd mu ->
                              local_of mu = restrict (as_inj mu) (locBlocksSrc mu).
  move => mu0 smwd; extensionality b.
  rewrite /restrict /as_inj /join.
  case (disjoint_extern_local _ smwd b).
  move => extF; rewrite extF.
  destruct (local_of mu0 b) eqn:locb.
  + destruct p. apply smwd in locb; case locb => locS locT.
    rewrite locS; by reflexivity.      
      by (destruct (locBlocksSrc mu0 b); reflexivity).
  + move => locF; rewrite locF.
    destruct (locBlocksSrc mu0 b) eqn:locB.
    destruct (extern_of mu0 b) eqn:ext. destruct p.
    apply smwd in ext; case ext.
    case smwd => locVSext _.
    case (locVSext b); move => H; move: locB; rewrite H; discriminate.
    reflexivity.
    reflexivity.
Qed.

Lemma init_rel_inv_mu : rel_inv_pred m1 init_mu $ Build_frame_pkg lo_valid.
Proof.
apply: Build_rel_inv.
split=> /=.
by rewrite replace_locals_as_inj initial_SM_as_inj; apply: inject_incr_refl.
split=> b.
by rewrite replace_locals_DomSrc initial_SM_DomSrc.
  by rewrite replace_locals_DomTgt initial_SM_DomTgt.
  (*Edited: Santiago*)
  (* locinv 
rewrite /init_mu /local_inv /as_inj join_None_rightneutral /= /lo'
          replace_locals_local replace_locals_locBlocksSrc /j.
  apply: local_asinj_restrict => //=.
  case mu => //=.*)

  rewrite /sm_inject_separated'  /= replace_locals_as_inj initial_SM_as_inj /j.
  split; last by auto.
  by move => b1 b2 d0 H; rewrite H //=.

 rewrite /globals_separate /lo' /= replace_locals_as_inj initial_SM_as_inj /j. 
  by move => b1 b2 d0 H; rewrite H //=.
  (*End of edited*)
  
apply: Build_disjinv=> /=.
by rewrite predI01.
by rewrite predI01.
move=> b; move/andP=> /= []fS lS.
rewrite replace_locals_pubBlocksSrc eq1.
rewrite replace_locals_locBlocksSrc in lS.
apply/andP; split=> //.
apply: (REACH_mono 
  (fun b0 : block =>
    isGlobalBlock (ge (cores_S new_ix)) b0 || getBlocks vals1 b0))=> //.
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
    isGlobalBlock (ge (cores_S new_ix)) b0 || getBlocks vals1 b0))=> //.
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
case: inv=> mtch all vis domt nuk gfi.
apply: Build_head_inv=> //.
clear - all; elim: mus all=> // mu0 mus' IH /= []rel rall.
split; last by apply: IH.
apply: Build_rel_inv.
split; first by rewrite replace_locals_as_inj; case: rel; case.
split=> b H; move: H.
rewrite lo_DomSrc; case: rel; case=> _; case; move/(_ b)=> H _ _ _ _ H2.
by apply: H.
rewrite lo_DomTgt; case: rel; case=> _; case=> _; move/(_ b)=> H _ _ _ H2.
  by apply: H.
  (*Edited: Santiago*)
 (*locinv rewrite /lo' /local_inv replace_locals_as_inj.
 by apply rel.*)
 {
 case: rel=> _. move=> newsep (*gsep0*) disj0 sub0.
 by rewrite /lo' /sm_inject_separated'
         replace_locals_as_inj replace_locals_locBlocksSrc replace_locals_locBlocksTgt //=.  
 }
 {        case: rel=> _. move=> loc gsep0 disj0 sub0.
 move => p b2 d0 H HH.
 unfold globals_separate in gsep0.
 eapply gsep0.
   by apply H.
   unfold lo' in HH; rewrite replace_locals_as_inj in HH.
     by eapply HH. }
(*End Edit*)

case: rel=> _ _ _ ; case=> d1 d2 p1 p2 cons rc.
apply: Build_disjinv.
by rewrite replace_locals_locBlocksSrc.
by rewrite replace_locals_locBlocksTgt.
by rewrite replace_locals_frgnBlocksSrc.
by rewrite replace_locals_foreign.
by rewrite /Consistent /= replace_locals_as_inj.
case: rel=> _ _ _ _ H b; case/andP=> /= H2 H3; apply: H. 
by apply/andP; split=> //=; move: H2; rewrite lo_vis.
case: vis=> B; case=> H ?; exists B; split=> //. 
by apply: Build_vis_inv; rewrite lo_vis; case: H.
by rewrite replace_locals_DomTgt.
by rewrite /lo /= /lo' /= replace_locals_as_inj.
Qed.

End head_inv_leakout.

Import seq.

Fixpoint frame_all (mus : seq frame_pkg) m1 m2 s1 s2 :=
  match mus, s1, s2 with
    | Build_frame_pkg mu0 m10 m20 _ :: mus', c :: s1', d :: s2' => 
      [/\ exists (pf : c.(Core.i)=d.(Core.i)) 
                 (sig_pf : c.(Core.sg)=d.(Core.sg)) cd0,
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
      & exists (pf : c.(Core.i)=d.(Core.i)) 
               (sig_pf : c.(Core.sg)=d.(Core.sg)) cd0,
        exists e1 ef_sig1 vals1,
        exists e2 ef_sig2 vals2, 
          [/\ @frame_inv c d pf cd0 mu0 
                m10 m1 e1 ef_sig1 vals1 m20 m2 e2 ef_sig2 vals2
            & frame_all mus m1 m2 s1' s2']].
Proof.
case: s1=> // c s1'; case: s2=> // d s2' /=.
move=> [][]pf => [][]sig_pf []cd []ef1 []sig1 []vals1 []ef2 []sig2 []vals2. 
case=> A B C D E F.
exists c, s1', d, s2'; split=> //.
by exists pf, sig_pf, cd, ef1, sig1, vals1, ef2, sig2, vals2; split.
Qed.

Lemma frame_all_match mu0 m10 m20 x mus m1 m2 s1 s2 :
  frame_all (@Build_frame_pkg mu0 m10 m20 x :: mus) m1 m2 s1 s2 -> 
  exists c s1' d s2',
    [/\ s1 = c :: s1'
      , s2 = d :: s2' 
      & exists (pf : c.(Core.i)=d.(Core.i)) 
               (sig_pf : c.(Core.sg)=d.(Core.sg)) cd0,
        (sims c.(Core.i)).(match_state) cd0 mu0 
        c.(Core.c) m10 (cast'' pf d.(Core.c)) m20].
Proof.
case: s1=> // c s1'; case: s2=> // d s2' /=.
move=> [][]pf => [][]sig_pf []cd []ef1 []sig1 []vals1 []ef2 []sig2 []vals2 []A B C.
exists c, s1', d, s2'; split=> //.
by exists pf, sig_pf, cd. 
Qed.

Lemma frame_all_fwd1 pkg mus m1 m2 s1 s2 :
  frame_all (pkg :: mus) m1 m2 s1 s2 -> 
  mem_forward pkg.(frame_m10) m1.
Proof.
case: pkg=> ? ? ? ?.
move/frame_all_inv=> []? []? []? []? []? ? []? []? []? []? []? []? []? []? []? [].
by case.
Qed.

Lemma frame_all_fwd2 pkg mus m1 m2 s1 s2 :
  frame_all (pkg :: mus) m1 m2 s1 s2 -> 
  mem_forward pkg.(frame_m20) m2.
Proof.
case: pkg=> ? ? ? ?.
move/frame_all_inv=> []? []? []? []? []? ? []? []? []? []? []? []? []? []? []? [].
by case.
Qed.

Lemma frame_all_tail pkg mus m1 m2 s1 s2 :
  frame_all (pkg :: mus) m1 m2 s1 s2 -> 
  frame_all mus m1 m2 (STACK.pop s1) (STACK.pop s2).
Proof.
case: pkg=> ? ? ? ?.
move/frame_all_inv=> []? []? []? []? []-> ->. 
by move=> []? []? []? []? []? []? []? []? []? []_.
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
move=> []pf []cd []? []? []? []? []? []? []? []B C. 
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
move=> []pf []cd []? []? []? []? []? []? []? []B C.
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
move=> []pf []cd []? []? []? []? []? []? []? []B C.
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
      , (exists (pf : c.(Core.i)=d.(Core.i)) 
                (sig_pf : c.(Core.sg)=d.(Core.sg)) cd0,
         exists e1 ef_sig1 vals1,
         exists e2 ef_sig2 vals2, 
           @frame_inv c d pf cd0 mu0 
           m10 m1 e1 ef_sig1 vals1 m20 m2 e2 ef_sig2 vals2)
       & tail_inv mus (STACK.pop s1) (STACK.pop s2) m1 m2].
Proof.
case; case=> H1 H2; move/frame_all_inv=> []c []s1' []d []s2' []B C.
move=> []pf []sg_pf []cd []ef1 []sig1 []vals1 []ef2 []sig2 []vals2 []D E.
exists c,s1',d,s2'; split=> //.
by exists pf,sg_pf,cd,ef1,sig1,vals1,ef2,sig2,vals2.
by split=> //; rewrite B C.
Qed.

Lemma tail_inv_match mu0 m10 m20 x mus s1 s2 m1 m2 :
  tail_inv (@Build_frame_pkg mu0 m10 m20 x :: mus) 
           s1 s2 m1 m2 -> 
  exists c s1' d s2',
    [/\ s1 = c :: s1'
      , s2 = d :: s2' 
      & exists (pf : c.(Core.i)=d.(Core.i)) 
               (sig_pf : c.(Core.sg)=d.(Core.sg)) cd0,
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

Lemma head_tail_inv c d (sig_pf : c.(Core.sg)=d.(Core.sg)) 
                    pf cd (mu : frame_pkg) e sig args1 args2
  (val : sm_valid mu m1 m2)
  (atext1 : at_external (sem (cores_S (Core.i c))) (Core.c c) 
            = Some (e,sig,args1))
  (atext2 : at_external (sem (cores_T (Core.i c))) 
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
exists pf,sig_pf,cd,e,sig,args1,e,sig,args2.
apply: Build_frame_inv=> //.
by apply: (head_match inv).
by apply: (head_vis inv).
by apply: (head_domt inv).
by apply: (head_nukeI inv).
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

Lemma globalfunction_ptr_inject_intern_incr F V (mu mu' : Inj.t) (ge : Genv.t F V) :
  intern_incr mu mu' -> 
  globalfunction_ptr_inject ge (as_inj mu) ->
  globalfunction_ptr_inject ge (as_inj mu').
Proof.
move/intern_incr_as_inj; move/(_ (Inj_wd _)).
rewrite /globalfunction_ptr_inject=> H H2 b f Hfind.
by case: (H2 _ _ Hfind); split=> //; apply: H.
Qed.

Section step_lems.

Lemma DisjointLS_intern_step mu0 (mu mu' : Inj.t) m1 m2 m1' m2' :
  DisjointLS mu0 mu -> 
  intern_incr mu mu' -> 
  sm_locally_allocated mu mu' m1 m2 m1' m2'  -> 
  sm_valid mu0 m1 m2 -> 
  (*sm_valid mu m1 m2 -> *)
  DisjointLS mu0 mu'.
Proof.
  move=> disj incr loca val1 (*val2*).
  have B: Disjoint (locBlocksSrc mu0) [pred b | ~~ validblock m1 b].
  apply: smvalid_locsrc_disjoint=> //. 
    by apply: (sm_valid_smvalid_src _ _ _ val1).
  have C: {subset [predD (locBlocksSrc mu') & locBlocksSrc mu]
           <= [pred b | ~~ validblock m1 b]}.
  by apply: (sminj_alloc_locsrc incr loca).
  have D: Disjoint (locBlocksSrc mu0) 
                     [predD (locBlocksSrc mu') & locBlocksSrc mu].
   by apply: (Disjoint_sub1 B C).
by apply: (Disjoint_incr disj D).
Qed.

Lemma DisjointLS_intern_step' mu0 (mu mu' : Inj.t) m1 m2 m1' m2' :
  DisjointLS mu0 mu ->
    inject_incr (as_inj mu0) (as_inj mu) ->
  sm_locally_allocated mu mu' m1 m2 m1' m2'  -> 
  intern_incr mu mu' -> 
  sm_valid mu0 m1 m2 -> 
  (*sm_valid mu m1 m2 -> *)
  DisjointLS mu0 mu'.
Proof.
  move=> disj incr loca incr' val1 (*val2*).
  have B: Disjoint (locBlocksSrc mu0) [pred b | ~~ validblock m1 b].
  apply: smvalid_locsrc_disjoint=> //. 
    by apply: (sm_valid_smvalid_src _ _ _ val1).
  have C: {subset [predD (locBlocksSrc mu') & locBlocksSrc mu]
           <= [pred b | ~~ validblock m1 b]}.
  by apply: (sminj_alloc_locsrc incr' loca).
  have D: Disjoint (locBlocksSrc mu0) 
                     [predD (locBlocksSrc mu') & locBlocksSrc mu].
   by apply: (Disjoint_sub1 B C).
by apply: (Disjoint_incr disj D).
Qed.

Lemma DisjointLT_intern_step mu0 (mu mu' : Inj.t) m1 m2 m1' m2' :
  DisjointLT mu0 mu -> 
  intern_incr mu mu' -> 
  sm_locally_allocated mu mu' m1 m2 m1' m2'  -> 
  sm_valid mu0 m1 m2 -> 
  (*sm_valid mu m1 m2 -> *)
  DisjointLT mu0 mu'.
Proof.
  move=> disj incr loca val1 (*val2*).
  have B: Disjoint (locBlocksTgt mu0) [pred b | ~~ validblock m2 b].
  apply: smvalid_loctgt_disjoint=> //. 
    by apply: (sm_valid_smvalid_tgt _ _ _ val1).
  have C: {subset [predD (locBlocksTgt mu') & locBlocksTgt mu]
           <= [pred b | ~~ validblock m2 b]}.
  by apply: (sminj_alloc_loctgt incr loca).
  have D: Disjoint (locBlocksTgt mu0) 
                     [predD (locBlocksTgt mu') & locBlocksTgt mu].
    by apply: (Disjoint_sub1 B C).
      by apply: (Disjoint_incr disj D).
Qed.

  Lemma disjinv_localloc_step (mu0 mu mu' : Inj.t) m10 m20 m1 m2 m1' m2':
    disjinv mu0 mu ->
    inject_incr (as_inj mu0) (as_inj mu) ->
      intern_incr mu mu' ->
      mem_forward m10 m1 ->
      mem_forward m20 m2 ->
      sm_locally_allocated mu mu' m1 m2 m1' m2' ->
      sm_valid mu0 m10 m20 ->
      sm_valid mu m1 m2 ->
      disjinv mu0 mu'.
Proof.
move=> inv incr' incr mf1 mf2 loca VAL VAL'.
have VAL2: sm_valid mu0 m1 m2 by apply: (sm_valid_fwd VAL mf1 mf2).
apply: Build_disjinv.  
+ have A: Disjoint (locBlocksSrc mu0) (locBlocksSrc mu) by case: inv.
   by apply: (DisjointLS_intern_step A incr loca VAL2).
+ have A: Disjoint (locBlocksTgt mu0) (locBlocksTgt mu) by case: inv.
  by apply: (DisjointLT_intern_step A incr loca VAL2).
+ have A: [predI (frgnBlocksSrc mu') & locBlocksSrc mu0]
          = [predI (frgnBlocksSrc mu) & locBlocksSrc mu0].
    by rewrite (intern_incr_frgnsrc incr).  
  by rewrite A; case: inv.
+ case: inv; rewrite/foreign_of. 
  generalize dependent mu; generalize dependent mu'.
  case; case=> /= ? ? ? ? ? ? ? ? ? ? ?. 
  case; case=> /= ? ? ? ? ? ? ? ? ? ? ? ? incr.
  move: (intern_incr_frgnsrc incr) (intern_incr_frgntgt incr)=> /= -> ->.
  by move: (intern_incr_extern incr)=> /= ->.
+ have wd: SM_wd mu' by destruct mu' => //.
  eapply intern_incr_as_inj in incr => //.                                 
  by apply (consistent_incr incr' incr).
Qed.

(*Lemma sm_sep_step' (mu0 mu : SM_Injection) (mu' : Inj.t) m10 m20 m1 m2
  (val : sm_valid mu0 m10 m20)
  (sep1 : sm_inject_separated' mu0 mu)
  (sep2 : sm_inject_separated' mu mu')
  (fwd1 : mem_forward m10 m1)
  (fwd2 : mem_forward m20 m2)
  (incr : Values.inject_incr (as_inj mu) (as_inj mu')) :
  sm_inject_separated' mu0 mu'.
Proof.
move=> b1 b2 d Inj1 Inj2; case S: (as_inj mu b1)=> [[b2' d']|].
move: (incr _ _ _ S); rewrite Inj2; case=> b2b2' dd'; subst b2' d'.
by apply: (sep1 _ _ _ Inj1 S).
case: (sep2 _ _ _ S Inj2)=> D E; split.
+ have D': DomSrc mu' b1. 
    by case: (as_inj_DomRng _ _ _ _ Inj2)=> //; apply: (Inj_wd mu').
  move: (B' _ D D')=> V1.
  have V0: ~Memory.Mem.valid_block m10 b1 
    by move=> ?; apply: V1; case: (fwd1 b1).
  by case F: (DomSrc mu0 b1)=> //; case: val; move/(_ b1 F).
+ have E': DomTgt mu' b2. 
    by case: (as_inj_DomRng _ _ _ _ H2)=> //; apply: (Inj_wd mu').
  move: (C' _ E E')=> V2.
  have V0: ~Memory.Mem.valid_block m20 b2 
    by move=> ?; apply: V2; case: (fwd2 b2).
  by case F: (DomTgt mu0 b2)=> //; case: val=> _; move/(_ b2 F).
case: sep2=> A' []B' C'; split.
+ move=> b1 D E.
  case F: (DomSrc mu b1); first by apply: (B _ D F).
  by move: (B' _ F E)=> V1 V0; apply: V1; case: (fwd1 b1).
+ move=> b2 D E.
  case F: (DomTgt mu b2); first by apply: (C _ D F).
  by move: (C' _ F E)=> V1 V0; apply: V1; case: (fwd2 b2).
Qed. *)


Lemma intern_incr_local mu mu':
  forall b1 p,
    intern_incr mu mu' ->
    as_inj mu b1 = None ->
    as_inj mu' b1 = Some p ->
    local_of mu' b1 = Some p.
rewrite /as_inj /join; move => b1 p II.
case ext:(extern_of mu b1) => [[b0 d'] | ] //=.
case II => LI []EE _.
rewrite <- EE; rewrite  ext //=.
Qed.

Lemma localloc_stepSrc mu mu' m1 m2 m1' m2':
  sm_locally_allocated mu mu' m1 m2 m1' m2' ->
  forall b1, locBlocksSrc mu' b1 ->
             locBlocksSrc mu b1 \/ ~Mem.valid_block m1 b1.
case mu; case mu' =>  /=.
move => locS locT _ _ _ ? ? _ _ _ locS' locT'? ? ? ? ? _ _ _ [] locs_eq [] loct_eq _.
rewrite locs_eq => b1.
case/orP; first by auto.
case/andP. move => H.
move => HH; right; move => valid.
apply (negP HH); apply: valid_dec => //=.
Qed.

Lemma localloc_stepTgt mu mu' m1 m2 m1' m2':
  sm_locally_allocated mu mu' m1 m2 m1' m2' ->
  forall b2, locBlocksTgt mu' b2 ->
             locBlocksTgt mu b2 \/ ~Mem.valid_block m2 b2.
case mu; case mu' =>  /=.
move => locS locT _ _ _ ? ? _ _ _ locS' locT'? ? ? ? ? _ _ _ [] locs_eq [] loct_eq _.
rewrite loct_eq => b1.
case/orP; first by auto.
case/andP. move => H.
move => HH; right; move => valid.
apply (negP HH); apply: valid_dec => //=.
Qed.
  
Context
(mu : Inj.t) m1 m2
(Esrc Etgt : Values.block -> BinNums.Z -> bool) 
(mu' : Inj.t) m1' m2'
(unch1 : Memory.Mem.unchanged_on (fun b ofs => Esrc b ofs=false) m1 m1')
(unch2 : Memory.Mem.unchanged_on (fun b ofs => Etgt b ofs=false) m2 m2')
(fwd1 : mem_forward m1 m1')
(fwd2 : mem_forward m2 m2')
(rdo1: forall b, Mem.valid_block m1 b -> readonly m1 b m1')
(rdo2: forall b, Mem.valid_block m2 b -> readonly m2 b m2')
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
(gsep : globals_separate my_ge mu mu')
(*sep : sm_inject_separated mu mu' m1 m2*) (*Change this! *)
(alloc : sm_locally_allocated mu mu' m1 m2 m1' m2')
(visrc : REACH_closed m1' (vis mu')).


Lemma rel_inv_pred_step pkg
  (fwd10 : mem_forward pkg.(frame_m10) m1)
  (fwd20 : mem_forward pkg.(frame_m20) m2) :
  rel_inv_pred m1 mu pkg -> rel_inv_pred m1' mu' pkg.
Proof.
move=> []incr' sep' gsep' disj.
split; first by apply: (incr_trans incr' (intern_incr_incr incr)).
{
  have incr'': inject_incr (as_inj mu) (as_inj mu').
  apply: intern_incr_as_inj=> /=; first by apply: incr.
    by generalize dependent mu'; case.
    case sep' => HH0 [HH1 HH2].
    have valid_block_stepSrc: (forall b1 : block,
         locBlocksSrc mu' b1 = true -> ~ Mem.valid_block (frame_m10 pkg) b1).
    {move => b1 locS.
     case (localloc_stepSrc alloc locS ).
        move => LocS.
        apply HH1 in LocS.
        contradict LocS; auto.
        move => H; contradict H.
        case (fwd10 _ H) => //=.
    }
    have valid_block_stepTgt:  (forall b2 : block,
    locBlocksTgt mu' b2 = true -> ~ Mem.valid_block (frame_m20 pkg) b2).
    { move => b2 locT.
      case (localloc_stepTgt alloc locT).
        move => LocT.
        apply HH2 in LocT.
        contradict LocT; auto.
        move => H; contradict H.
        case (fwd20 _ H) => //=.
    }
    split.
  - move => b1 b2 d map1 map2.
    destruct (as_inj mu b1) eqn: mub1.
    + destruct p. eapply sep'; eauto.
      rewrite mub1; apply incr'' in mub1.
      rewrite map2 in mub1; inversion mub1; by reflexivity.
    + have WD':SM_wd mu' by case mu'=>  //=.
      split.
      * have locMap: local_of mu' b1 = Some (b2, d) by eapply intern_incr_local; eauto.
        case WD'=> _ _ locDom _ _ _ _ _.
        case (locDom _ _ _ locMap) => locS locD.
        case DS:(DomSrc pkg b1); last by reflexivity.
        apply pkg in DS.
        by contradict DS; auto.

      * have locMap: local_of mu' b1 = Some (b2, d) by eapply intern_incr_local; eauto.
        case WD'=> _ _ locDom _ _ _ _ _.
        case (locDom _ _ _ locMap) => locS locT.
        case DT:(DomTgt pkg b2); last by reflexivity.
        apply pkg in DT.
        by contradict DT; auto.
  -  by split => //=.
    }


have incr'': inject_incr (as_inj mu) (as_inj mu').
  apply: intern_incr_as_inj=> /=; first by apply: incr.
    by generalize dependent mu'; case.

(*{ move => b1 b2 d map1 map2. eapply gsep'; auto. apply map1.
  destruct (as_inj mu b1) eqn: mub1.
+ destruct p. eapply gsep'; eauto.
  rewrite mub1; apply incr'' in mub1.
  rewrite HH in mub1; inversion mub1; by reflexivity.
+ eapply gsep; eauto.
  
}*)
    Lemma gsep_incr {F V}: forall (ge: Genv.t F V) mu nu nu',
                       globals_separate ge mu nu' ->
                       inject_incr (as_inj nu) (as_inj nu') ->
                       globals_separate ge mu nu.
      clear; intros ? ? ? ? gsep incr.
      intros b1 b2 d0 H HH.
      eapply gsep; eauto.
    Qed.
  move => b1 b2 d map1 map2.
  destruct (as_inj mu b1) eqn: mub1.
+ destruct p. eapply gsep'; eauto.
  rewrite mub1; apply incr'' in mub1.
  rewrite map2 in mub1; inversion mub1; by reflexivity.
+ eapply gsep; by eauto.
  (*End edit*) 
+ case incr' => inj_incr' dom_incr'.
  by apply: (disjinv_localloc_step disj inj_incr' incr fwd10 fwd20 alloc (frame_val pkg)).
      
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
move=> relinv []incr' sep' gsep' disj' rc'; split=> //.
move=> b; case/andP=> /= H H2. 
case: relinv=> _ _  gsep'' disj rc.
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
move=> []pf []sig_pf []cd []e1 []sig1 []vals1 []e2 []sig2 []vals2.
move=> []inv all.

split.
exists pf,sig_pf,cd,e1,sig1,vals1,e2,sig2,vals2.

case: inv=> ? ? ? ? val'' frmatch ? ?. 
move=> frvinj visinv domt nuke fwd1' fwd2' rdo1' rdo2' ? ?. 
apply: Build_frame_inv=> //.

by apply: (mem_forward_trans _ _ _ fwd1' fwd1). 
by apply: (mem_forward_trans _ _ _ fwd2' fwd2). 

 move=> b RDO. eapply readonly_trans. apply (rdo1' _ RDO). apply rdo1. eapply fwd1'.
   assert (WDmu0:= match_sm_wd frmatch).
   apply match_genv in frmatch; destruct frmatch as [PG_b Glob_b].
   apply  ReadOnlyBlocks_global in RDO. rewrite <- (genvs_domain_eq_isGlobal _ _ (my_ge_S _ )) in Glob_b. 
   destruct (frgnSrcAx _ WDmu0 _ (Glob_b _ RDO)) as [? [? [? ?]]].
   eapply Mem.valid_block_inject_1.  apply extern_in_all; eauto.  eassumption. 

 move=> b RDO. eapply readonly_trans. apply (rdo2' _ RDO). apply rdo2. eapply fwd2'.
   assert (WDmu0:= match_sm_wd frmatch).
   apply match_genv in frmatch; destruct frmatch as [PG_b Glob_b].
   apply  ReadOnlyBlocks_global in RDO.
   specialize (meminj_preserves_globals_isGlobalBlock _ _ PG_b b);   
   rewrite <- (genvs_domain_eq_isGlobal _ _ (my_ge_S _ )); intros. 
   eapply Mem.valid_block_inject_2.  apply extern_in_all; eauto.  eassumption. 


apply: (mem_lemmas.unchanged_on_trans m10 m1 m1')=> //.
set pubSrc' := [predI locBlocksSrc mu0 & REACH m10 (exportedSrc mu0 vals1)].
set pubTgt' := [predI locBlocksTgt mu0 & REACH m20 (exportedTgt mu0 vals2)].
set mu0'    := replace_locals mu0 pubSrc' pubTgt'.
have wd: SM_wd mu0'. 
{ apply: replace_reach_wd=> //.
  by apply: (forall_vals_inject_restrictD _ _ _ _ frvinj). }
have J: disjinv mu0' mu by case: E=> /= ? ? ? ? ?; apply: disjinv_call.
apply: (@disjinv_unchanged_on_src (Inj.mk wd) mu Esrc)=> //.
move: (sm_valid_smvalid_src _ _ _ val')=> ?.
apply: smvalid_src_replace_locals=> //=.
by apply: (smvalid_src_fwd fwd1').
by move=> x y H _; apply (val H).

apply: (mem_lemmas.unchanged_on_trans m20 m2 m2')=> //.
set pubSrc' := [predI locBlocksSrc mu0 & REACH m10 (exportedSrc mu0 vals1)].
set pubTgt' := [predI locBlocksTgt mu0 & REACH m20 (exportedTgt mu0 vals2)].
set mu0'    := replace_locals mu0 pubSrc' pubTgt'.
have J: disjinv mu0' mu by case: E=> /= ? ? ? ? ?; apply: disjinv_call.
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

Lemma vis_inv_step (c c' : Core.t cores_S) B :
  vis_inv c B mu -> 
  REACH_closed m1 (vis mu) -> 
  Core.i c = Core.i c' ->
  vis_inv c' (REACH m1' (fun b => structured_injections.freshloc m1 m1' b
                || RC.reach_set (ge (cores_S (Core.i c))) (RC.mk (Core.c c) B) m1 b)) mu'.
Proof.
move=> E rc Heq; move: E.
case=> E; apply: Build_vis_inv=> b F.
move: F; rewrite/RC.roots/in_mem/=; move/orP=> [|F].
move=> F.
by apply: (intern_incr_vis _ _ incr); apply: E; apply/orP; left; rewrite Heq.
case G: (B b).
by apply: (intern_incr_vis _ _ incr); apply: E; apply/orP; right.
move: F=> H.
apply: visrc; apply: (REACH_mono _ _ _ _ _ H)=> b0 H2. 
case: {H2}(orP H2)=> H2.
move: alloc; rewrite sm_locally_allocatedChar /vis; case. 
by move=> _ []_ []-> _; rewrite H2 -orb_assoc orb_comm.
suff: vis mu b0. 
rewrite /vis; case: incr=> _ []_ []sub1 []_ []_ []_ []<- _; case/orP.
by move/sub1=> ->.
by move=> ->; rewrite orb_comm.
apply: rc; apply: (REACH_mono _ _ _ _ _ H2)=> b2 H3. 
move: (E b2); rewrite /in_mem /=; apply.
apply: (RC.roots_domains_eq _ H3).
by apply: genvs_domain_eq_refl.
Qed.

Lemma head_inv_step 
    c d (pf : Core.i c=Core.i d) c' (d' : C (cores_T (Core.i d)))
    cd cd' mus s1 s2 U n V :
  head_inv pf cd mu mus m1 m2 -> 
  frame_all mus m1 m2 s1 s2 -> 
  effect_semantics.effstep 
    (sem (cores_S (Core.i c))) (ge (cores_S (Core.i c))) U 
    (Core.c c) m1 c' m1' -> 
  effect_semantics.effstepN 
    (sem (cores_T (Core.i d))) (ge (cores_T (Core.i d))) n V 
    (Core.c d) m2 d' m2' -> 
  mem_welldefined.valid_genv (ge (cores_T (Core.i d))) m2 ->
  match_state (sims (Core.i (Core.upd c c'))) cd' mu'
    (Core.c (Core.upd c c')) m1'
    (cast'' pf (Core.c (Core.upd d d'))) m2' -> 
  @head_inv (Core.upd c c') (Core.upd d d') pf cd' mu' mus m1' m2'.
Proof.
move=> hdinv frame effstep effstepN vgenv mtch.
apply: Build_head_inv=> //.
by apply: (all_relinv_step frame); apply: (head_rel hdinv).
case: hdinv=> hdmtch ?; case=> B0 []?????.
set B := REACH m1' 
  (fun b => structured_injections.freshloc m1 m1' b
         || RC.reach_set (ge (cores_S (Core.i c))) 
              (RC.mk (Core.c c) B0) m1 b).
{ exists B; rewrite /B; move {B}; split=> //. 
  by apply: vis_inv_step=> //; apply match_visible in hdmtch. 
  apply RCSem.step_ax=> //.
  by apply effax1 in effstep; case: effstep. }
move: alloc; case/sm_locally_allocatedChar=> _ []-> []_ []H1 []_ H2.
rewrite (head_domt hdinv); extensionality b.
case e: (freshloc m2 m2' b). 
rewrite orb_comm /=; move: e; rewrite freshloc_charT; case.
by move/valid_dec.
rewrite orb_comm /=; move: e; rewrite freshloc_charF; case.
by move=> v; move: (valid_dec v)=> v'; case: (fwd2 v); move/valid_dec=> ->.
move=> H3; case e: (valid_block_dec m2' b)=> [x|x].
by elimtype False; apply: H3; apply: x.
case f: (valid_block_dec m2 b)=> [y|//].
by case: (fwd2 y)=> H4; elimtype False; apply: H3; apply: H4.
apply effstepN_corestepN in effstepN; simpl.
by apply: (Nuke_sem.nucular_stepN _ _ effstepN)=> //; apply: (head_nukeI hdinv).
by case: hdinv=> *; apply: (globalfunction_ptr_inject_intern_incr incr).
Qed.

End step_lems.

Section R.

Import CallStack.
Import Linker.
Import STACK.

Require Import mem_welldefined.

(** ** Top-Level Invariant *)

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
    exists (pf : c.(Core.i)=d.(Core.i)) 
           (pf_sig : c.(Core.sg)=d.(Core.sg)) 
           (mu_top : Inj.t) mus, 
    [/\ mu = mu_top
      , exists pf2 : projT1 data = c.(Core.i),
        @head_inv c d pf (cast_ty (lift_eq _ pf2) (projT2 data)) mu_top mus m1 m2 
      & tail_inv mus (pop s1) (pop s2) m1 m2] 

    (* side conditions *)
  ; R_fntbl : x1.(fn_tbl)=x2.(fn_tbl) 
  ; R_ge    : forall ix : 'I_N, valid_genv (ge (cores_T ix)) m2 
  ; R_ro1  : forall ix : 'I_N, mem_respects_readonly (ge (cores_S ix)) m1
  ; R_ro2  : forall ix : 'I_N, mem_respects_readonly (ge (cores_T ix)) m2

  ; frame_mmr1: mem_respects_readonly my_ge m1
  ; frame_mmr2: mem_respects_readonly my_ge m2


    (* typing conditions *)
  ; R_tys1  : tys_agree (callStack s1)
  ; R_tys2  : tys_agree (callStack s2)
  }.

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
move: (R_inv pf)=> []A []pf_sig []mu_top []mus []eq []pf2.
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
case: (R_inv pf)=> pf2 []pf_sig []mu_top []mus []eq []pf3 [].
by move/match_sm_wd=> wd _ _ _ _ _ _; rewrite eq.
Qed.

End R_lems.

Section initCore_lems.

Context (my_cores : 'I_N -> t) c1 sg ix v vs 
        (init1 : initCore my_cores sg ix v vs = Some c1).

Lemma initCore_ix : ix = Core.i c1.
Proof.
move: init1; rewrite /init1 /initCore.
by case: (semantics.initial_core _ _ _ _)=> // c;
  case; case: c1=> ? ? ?; case.
Qed.

End initCore_lems.

End linkingInv.

Lemma vis_sub_DomSrc (mu0 : Inj.t) : {subset vis mu0 <= DomSrc mu0}.
Proof.
move=> b; case/orP; rewrite /DomSrc.
by rewrite /in_mem /= => ->.
by move/frgnsrc_sub_extsrc=> H; apply/orP; right.
Qed.
