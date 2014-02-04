(* standard Coq libraries *)

Require Import JMeq.

(* msl imports *)

Require Import msl.Axioms. (*for proof_irr*)

(* sepcomp imports *)

Require Import sepcomp.mem_lemmas.
Require Import sepcomp.core_semantics.
Require Import sepcomp.StructuredInjections.
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
Require Import sepcomp.linking.
Require Import sepcomp.linking_lemmas.
Require Import sepcomp.disjointness.
Require Import sepcomp.arguments.

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

(** * Linking simulation proof 

This file states and proves the main linking simulation result.

*)

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

(** Frame Invariant: 
    ~~~~~~~~~~~~~~~~

   The frame invariant applies to cores in caller positions in the
   call stack.  I.e, to cores that are waiting [at_external] for the
   environment to return. Main arguments are:

   * Existentially quantified when [frame_inv] is applied:
   -[mu0]: [SM_injection] at point of external call

   -[nu0]: [SM_injection] derived from [mu0] by restricting [pubSrc]
   and [pubTgt] to reachable local blocks.  [nu0] is used primarily to
   state the [unchOn] invariants assumable by THIS core.

   -[m10], [m20]: Source and target memories active at call point. 

   * True parameters: 
   -[mu]: The [SM_injection] of the currently running core (/not/ this
    one).  Things to note:

     + Resuming a core:
     ~~~~~~~~~~~~~~~~~~

     When we resume a core, we do not use [mu] directly.  Instead, we
     employ the derived [SM_injection]:
       mu' := { local_of  := local_of mu0
              ; extern_of := extern_of mu0 
                             + {extern_of mu | REACH m1' m2' ret1 ret2}
              ; ... }
     This [SM_injection] satisfies [extern_incr mu0 mu'], among other
     properties required by the [after_external] clause of structured
     simulations.


     + The [frame_dom] invariant [dominv mu0 mu]: 
     ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

     [mu0] is always disjoint, in the way specified by [dominv], 
     from the active injection [mu].  This is to ensure that we can 
     re-establish over steps of the active core the [frame_unch1] 
     and [frame_unch2] invariants given below (which in turn are 
     required by [after_external]).
     
     In order to re-establish [dominv] when a core returns to its
     context, we track as an additional invariant that [dominv mu0
     mu_head], where [mu_head] is the existentially quantified
     injection of the callee.

   -[m1], [m2]: Active memories. 
*)

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
                    c.(Core.c) m10 (cast pf d.(Core.c)) m20 
  ; frame_at1   : at_external (cores_S c.(i)).(coreSem) c.(Core.c) 
                    = Some (e1, ef_sig1, vals1) 
  ; frame_at2   : at_external (cores_T c.(i)).(coreSem) (cast pf d.(Core.c)) 
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

Section head_inv.

Import Core.

Variables (c : t cores_S) (d : t cores_T). 
Variable  (pf : c.(i)=d.(i)).

Record head_inv cd mu m1 m2 : Type :=
  { head_match : (sims c.(i)).(match_state) cd mu 
                 c.(Core.c) m1 (cast pf d.(Core.c)) m2 }.

End head_inv.

Section head_inv_lems.

Context c d pf cd mu m1 m2 (inv : @head_inv c d pf cd mu m1 m2).

Lemma head_inv_restrict (X : block -> bool) : 
  (forall b : block, vis mu b -> X b) -> 
  REACH_closed m1 X -> 
  @head_inv c d pf cd (restrict_sm mu X) m1 m2.
Proof.
case: inv=> H H2 H3; apply: Build_head_inv.
by apply: (match_restrict _ _ _ _ _ (sims (Core.i c))).
Qed.

End head_inv_lems.

Import seq.

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

Definition tail_inv mus mu s1 s2 m1 m2 :=
  [/\ All2 (rel_inv_pred \o frame_mu0) (mu :: mus)
    & frame_all mus m1 m2 s1 s2].

Lemma all_wrt_callers_switch T P (a b : T) (l : seq T) :
  All2_aux P b l -> All2 P (a :: l) ->All2 P (b :: l).
Proof. by elim: l a b=> // a' l' IH a b /= []A B [][]C D []E F. Qed.

Definition restrict_sm_wd m1
  (mu : Inj.t) (X : block -> bool)
  (vis_pf : forall b : block, vis mu b -> X b)
  (rc_pf  : REACH_closed m1 X) : Inj.t :=
  Inj.mk (restrict_sm_WD _ (Inj_wd mu) X vis_pf).

(* Lemma tail_len_eq (mus : seq frame_pkg) (mu : Inj.t) s1 s2 m1 m2 : *)
(*   tail_inv mus mu s1 s2 m1 m2 -> length s1 = length s2. *)
(* Proof. *)
(* move: s1 s2 mu; elim: mus. *)
(* case; case=> //; first by move=> ? ? ?; case. *)
(* by move=> ? ? ? ? ?; case. *)
(* move=> pkg mus' IH s1' s2' mu'. *)
(* case: s1'; first by case: s2'=> // ? ?; case; case: pkg. *)
(* move=> x s1'; case: s2'; first by case; case: pkg. *)
(* move=> y s2' /=; case=> A B. *)
(* move: B A; case: pkg=> /= mu0 m10 m20. *)
(* move=> [][]eq_ab []cd0 []e1 []sig1 []vals1 []e2 []sig2 []vals2. *)
(* case=> ? ? ? ? ? frmatch ? ? ? fwd1 fwd2 ? ? A [][]B C. *)
(* have mu0_wd: SM_wd mu0. *)
(*   move: (sims (Core.i x)).(match_sm_wd _ _ _ _ _).  *)
(*   by move/(_ _ _ _ _ _ _ frmatch). *)
(* have C': tail_inv mus' (Inj.mk mu0_wd) s1' s2' m1 m2. *)
(*   split=> //. *)
(* by rewrite (IH _ _ _ C'). *)
(* Qed. *)

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
          c.(Core.c) m10 (cast pf d.(Core.c)) m20].
Proof.
case: s1=> // c s1'; case: s2=> // d s2' /=.
move=> [][]pf => [][]cd []ef1 []sig1 []vals1 []ef2 []sig2 []vals2 A B.
exists c, s1', d, s2'; split=> //.
by exists pf, cd; case: A.
Qed.

Lemma tail_inv_inv mu0 m10 m20 x mus mu_top s1 s2 m1 m2 :
  tail_inv (@Build_frame_pkg mu0 m10 m20 x :: mus) mu_top s1 s2 m1 m2 -> 
  exists c s1' d s2',
    [/\ s1 = c :: s1'
      , s2 = d :: s2' 
      , rel_inv_pred mu_top (@Build_frame_pkg mu0 m10 m20 x)
      , (exists (pf : c.(Core.i)=d.(Core.i)) cd0,
         exists e1 ef_sig1 vals1,
         exists e2 ef_sig2 vals2, 
           @frame_inv c d pf cd0 mu0 
           m10 m1 e1 ef_sig1 vals1 m20 m2 e2 ef_sig2 vals2)
       & tail_inv mus (@Build_frame_pkg mu0 m10 m20 x) 
                      (STACK.pop s1) (STACK.pop s2) m1 m2].
Proof.
case; case: s1=> // c s1'; case: s2=> // d s2'=> /= [][][]? ? ?.
move=> [][]pf => [][]cd []ef1 []sig1 []vals1 []ef2 []sig2 []vals2 A B.
exists c, s1', d, s2'; split=> //.
by exists pf,cd,ef1,sig1,vals1,ef2,sig2,vals2.
Qed.

Lemma tail_inv_match mu0 m10 m20 x mus mu_top s1 s2 m1 m2 :
  tail_inv (@Build_frame_pkg mu0 m10 m20 x :: mus) mu_top s1 s2 m1 m2 -> 
  exists c s1' d s2',
    [/\ s1 = c :: s1'
      , s2 = d :: s2' 
      & exists (pf : c.(Core.i)=d.(Core.i)) cd0,
        (sims c.(Core.i)).(match_state) cd0 mu0 
          c.(Core.c) m10 (cast pf d.(Core.c)) m20].
Proof. by move=> []_; move/frame_all_match. Qed.

Lemma tail_inv_preserves_globals mus mu_top s1 s2 m1 m2 :
  tail_inv mus mu_top s1 s2 m1 m2 -> 
  All (Events.meminj_preserves_globals my_ge \o extern_of \o Inj.mu)
    [seq frame_mu0 x | x <- mus].
Proof.
move: mu_top s1 s2; elim: mus=> // mu0 mus' IH mu_top s1 s2.
case: mu0=> ? ? ? ?; move/tail_inv_inv=> []c []? []d []? []_ _ _ []pf []cd.
move=> []? []? []? []? []? []? []? ? ? ? ?.
move/match_genv=> [] /= X ? ? ? ? ? ? ? ? TL; split.
rewrite -meminj_preserves_genv2blocks; move: X.
rewrite (genvs_domain_eq_match_genvs (my_ge_S (Core.i c))).
by rewrite meminj_preserves_genv2blocks.
by apply: (IH _ _ _ TL).
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
  All2_aux (rel_inv_pred \o frame_mu0) mu mus -> 
  All2_aux (rel_inv_pred \o frame_mu0) mu' mus.
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

Lemma all_wrt_callers_step 
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
  All2 (rel_inv_pred \o frame_mu0) (mu :: mus) -> 
  All2 (rel_inv_pred \o frame_mu0) (mu' :: mus).
Proof.
elim: mus mu mu' s1 s2=> // pkg mus' IH mu mu' s1' s2'.
move=> H1 H2 H3 H4 A B C D E F /= []G H.
move: F G H; case: s1'=> //; first by case: s2'; case: pkg.
move=> a s1'; case: s2'; first by case: pkg.
move=> b s2'; case: pkg=> ? ? ? ? /= [].
move=> []eq_ab []cd0 []e1 []sig1 []vals1 []e2 []sig2 []vals2.
case=> ? ? ? ? ? frmatch ? ? ? fwd1 fwd2 ? ? ? []? ? ?; split.
split; first by eapply rel_inv_pred_step; eauto.
by eapply wrt_callers_step; eauto.
by [].
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
  intern_incr mu mu' -> 
  mem_forward m1 m1' -> 
  mem_forward m2 m2' ->   
  sm_inject_separated mu mu' m1 m2  -> 
  sm_valid mu m1 m2 -> 
  All2 (rel_inv_pred \o frame_mu0) (mu :: mus) -> 
  frame_all mus m1 m2 s1 s2 -> 
  frame_all mus m1' m2' s1 s2.
Proof.
elim: mus mu mu' s1 s2=> // pkg mus' IH mu mu' s1' s2'.
move=> H1 H2 H3 H4 A B C D E.
case: s1'=> // a s1'; case: s2'=> // b s2'; case: pkg=> mu0 m10 m20 val. 
move=> /= [][]F G H [] []eq_ab []cd0 []e1 []sig1 []vals1 []e2 []sig2 []vals2.
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

eapply IH; eauto.
by eapply all_wrt_callers_switch; eauto.
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
  intern_incr mu mu' -> 
  mem_forward m1 m1' -> 
  mem_forward m2 m2' ->   
  sm_inject_separated mu mu' m1 m2  -> 
  sm_valid mu m1 m2 -> 
  tail_inv mus mu s1 s2 m1 m2 -> 
  tail_inv mus mu' s1 s2 m1' m2'.
Proof.
move=> ? ? ? ? ? ? ? ? ? []A B; split.
by eapply all_wrt_callers_step; eauto.
by eapply frame_all_step; eauto.
Qed.

(*Lemma tail_inv_restrict (X : block -> bool) mus mu s1 s2 m1 m2 :
  tail_inv mus mu s1 s2 m1 m2 -> 
  tail_inv (map (restrict_sm^~ X) mus) (restrict_sm mu X) s1 s2 m1 m2.
Proof.
move: mu s1 s2; elim: mus=> // mu0 mus' IH mu'.
case=> // a s1'; case=> // b s2'.
move=> [][pf][cd][m10][e1][sig1][vals1][m20][e2][sig2][vals2][]; split; 
 last by apply: IH.
exists pf, cd, m10, e1, sig1, vals1, m20, e2, sig2, vals2. 
apply: Build_frame_inv=> //.
Admitted. (*likely true*) 

Lemma tail_inv_restrict (X : block -> bool) (mu : Inj.t) s1 s2 m1 m2 
  (vis : forall b : block, vis mu b -> X b)
  (reach : REACH_closed m1 X) :
  let: mu' := Inj.mk (restrict_sm_WD mu (Inj_wd mu) X vis) in
  tail_inv mu s1 s2 m1 m2 ->
  tail_inv mu' s1 s2 m1 m2.
Proof. 
move=> []mus []A B C. 
exists (map (restrict_sm^~ X) mus); split=> //.
by apply: one_disjoint_r_restrict.
by apply: all_disjoint_restrict.
by apply: tail_inv_restrict.
Qed.*)

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
    [/\ mu = join_all (frame_mu0 mu_trash) $ map frame_mu0 (mu_top :: mus)
      , Events.meminj_preserves_globals my_ge $ extern_of mu_trash
      , All2_aux DisjointLS mu_trash $ map (Inj.mu \o frame_mu0) $ mu_top :: mus
      , All2_aux DisjointLT mu_trash $ map (Inj.mu \o frame_mu0) $ mu_top :: mus
      , All2_aux Consistent mu_trash $ map (Inj.mu \o frame_mu0) $ mu_top :: mus
      , @head_inv c d pf (Lex.get c.(Core.i) data) mu_top m1 m2 
      & tail_inv mus mu_top (pop s1) (pop s2) m1 m2] }.

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
  (cast peek_ieq (Core.c (peekCore x2))) m2.
Proof.
move: (R_inv pf)=> []A []? []mu_top []? []? _ _ _ _. 
move/head_match=> MATCH ?.
have ->: (cast peek_ieq (Core.c (peekCore x2)) = cast A (Core.c (peekCore x2)))
  by f_equal; f_equal; apply proof_irr.
by exists (Lex.get (Core.i (peekCore x1)) data), mu_top.
Qed.

Lemma R_match :
  exists (pf0 : (c pf).(Core.i)=(d pf).(Core.i)) mu_trash mu_top mus, 
  [/\ mu = join_all (frame_mu0 mu_trash) $ map frame_mu0 (mu_top :: mus)
    , Events.meminj_preserves_globals my_ge $ extern_of mu_trash
    , All2_aux DisjointLS mu_trash $ map (Inj.mu \o frame_mu0) $ mu_top :: mus
    , All2_aux DisjointLT mu_trash $ map (Inj.mu \o frame_mu0) $ mu_top :: mus
    , All2_aux Consistent mu_trash $ map (Inj.mu \o frame_mu0) $ mu_top :: mus
    , @head_inv (c pf) (d pf) pf0 (Lex.get (c pf).(Core.i) data) mu_top m1 m2 
    & tail_inv mus mu_top (STACK.pop x1.(stack)) (STACK.pop x2.(stack)) m1 m2].
Proof.
case: (R_inv pf)=> pf0 []mu_trash []mu_top []mus []A B C D.
by exists pf0, mu_trash, mu_top, mus; split.
Qed.

Lemma R_match' :
  exists (pf0 : (c pf).(Core.i)=(d pf).(Core.i)) mu_top,
    match_state (sims (Core.i (c pf))) (Lex.get (c pf).(Core.i) data) mu_top
    (Core.c (c pf)) m1 (cast pf0 (Core.c (d pf))) m2.
Proof.
case: R_match=> []pf0 []? []mu_top []? []A B _ _ _. 
move/head_match=> C D.
by exists pf0, mu_top.
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
by move: (All2_sub B PC); split=> //; rewrite -All2_comp'.
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
by move: (All2_sub B PC); split=> //; rewrite -All2_comp'.
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
by move: (All2_sub B PC); split=> //; rewrite -All2_comp'.
Qed.

Lemma R_wd : SM_wd mu.
Proof.
move: (R_inv pf)=> []A []mu_trash []mu_top []mus []B _ C D E F []G H.
rewrite B; apply: join_all_wd. 
by move: (R_AllDisjointS C G)=> /=; rewrite map_comp.
by move: (R_AllDisjointT D G)=> /=; rewrite map_comp.
by move: (R_AllConsistent E G)=> /=; rewrite map_comp.
Qed.

Arguments genvs_domain_eq_match_genvs {_ _ _ _ _ _} _.

Lemma R_pres_globs : Events.meminj_preserves_globals my_ge (extern_of mu).
Proof. 
move: (R_inv pf)=> []A []mu_trash []mu_top []mus []B H X Y Z W []U V. 
rewrite B; apply: join_all_preserves_globals=> //.
by move: (R_AllDisjointS X U)=> /=; rewrite map_comp.
by move: (R_AllDisjointT Y U)=> /=; rewrite map_comp.
by move: (R_AllConsistent Z U)=> /=; rewrite map_comp.
move: (tail_inv_preserves_globals (conj U V)); split=> //.

(* HERE! *)

case: X=> X; case: (match_genv X); rewrite -meminj_preserves_genv2blocks.
rewrite -(genvs_domain_eq_match_genvs (my_ge_S (Core.i (c pf)))).
by rewrite meminj_preserves_genv2blocks.
by apply: (tail_inv_preserves_globals Y).
Qed.

Lemma R_match_genv :
  Events.meminj_preserves_globals my_ge (extern_of mu) /\
  forall b : block, isGlobalBlock my_ge b -> frgnBlocksSrc mu b.
Proof.
split; first by apply: R_pres_globs.
move: R_match=> []? []mu_trash []mu_top []mus []A _. 
move/head_match/match_genv=> []_.
rewrite -(genvs_domain_eq_isGlobal _ _ (my_ge_S (Core.i (c pf)))).
move=> H _ b H2; move: (H _ H2); rewrite A.


Lemma R_match_visible : REACH_closed m1 (vis mu).
move: (R_head pf)=> [A]; move/head_match=> H. 
by apply: (@match_visible _ _ _ _ _ _ _ _ _ _ _ 
          (sims (Core.i (c pf))) _ _ _ _ _ _ H).
Qed.

Lemma R_match_restrict (X : block -> bool) 
  (vis : forall b : block, vis mu b -> X b)
  (reach : REACH_closed m1 X) :
  R data (@restrict_sm_wd  _ (Inj.mk R_wd) _ vis reach) x1 m1 x2 m2.
Proof.
move: (R_head pf)=> [A] C; move: (head_inv_restrict C vis reach)=> H.
apply: Build_R; first by exists A.
(*by apply: tail_inv_restrict=> //; apply: (R_tail pf).*)
(*Qed.*)
Admitted. (*TODO*)

Lemma R_match_validblocks : sm_valid mu m1 m2.
Proof. 
move: (R_head pf)=> [A]; move/head_match. 
by apply: match_validblocks. 
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
- by move=> ??; apply: R_match_validblocks.

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
            (ge (cores_S (Core.i c1))) (Core.c c1) m1 c' m1' 
         /\ st1' = updCore st1 (Core.upd c1 c').
  { by move: STEP; rewrite/Sem.corestep0=> [][]c' []B C; exists c'; split. }

 have EFFSTEP: 
        effect_semantics.effstep (coreSem (cores_S (Core.i c1))) 
        (ge (cores_S (Core.i c1))) U1 (Core.c c1) m1 c1' m1'.
  { move: (STEP_EFFSTEP STEP); rewrite/effstep0=> [][] c1'' [] STEP0' ST1''.
    by rewrite ST1'' in ST1'; rewrite -(updCore_inj_upd ST1'). }

 (* specialize core diagram at module (Core.i c1) *)
 move: (effcore_diagram _ _ _ _ _ (sims (Core.i c1))).  
 move/(_ _ _ _ _ _ EFFSTEP).
 move/(_ _ _ _ _ U1_DEF).
 move: (peek_match INV)=> []cd MATCH.
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


