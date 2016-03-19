Require Import Axioms.

Add LoadPath "../compcomp" as compcomp.

Require Import sepcomp. Import SepComp.
Require Import core_semantics_lemmas.

Require Import pos.
(* Require Import stack.  *)
(* Require Import cast. *)
Require Import concurrent_machine.
Require Import pos.
Require Import Program.
Require Import ssreflect Ssreflect.seq ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.

(*NOTE: because of redefinition of [val], these imports must appear 
  after Ssreflect eqtype.*)
Require Import AST.     (*for typ*)
Require Import Values. (*for val*)
Require Import Globalenvs. 
Require Import Memory.
Require Import Integers.

Require Import ZArith.

Notation EXIT := 
  (EF_external "EXIT" (mksignature (AST.Tint::nil) None)). 

Notation CREATE_SIG := (mksignature (AST.Tint::AST.Tint::nil) (Some AST.Tint) cc_default).
Notation CREATE := (EF_external "CREATE" CREATE_SIG).

Notation READ := 
  (EF_external "READ"
               (mksignature (AST.Tint::AST.Tint::AST.Tint::nil) (Some AST.Tint) cc_default)).
Notation WRITE := 
  (EF_external "WRITE"
               (mksignature (AST.Tint::AST.Tint::AST.Tint::nil) (Some AST.Tint) cc_default)).

Notation MKLOCK := 
  (EF_external "MKLOCK" (mksignature (AST.Tint::nil) (Some AST.Tint) cc_default)).
Notation FREE_LOCK := 
  (EF_external "FREE_LOCK" (mksignature (AST.Tint::nil) (Some AST.Tint) cc_default)).

Notation LOCK_SIG := (mksignature (AST.Tint::nil) (Some AST.Tint) cc_default).
Notation LOCK := (EF_external "LOCK" LOCK_SIG).
Notation UNLOCK_SIG := (mksignature (AST.Tint::nil) (Some AST.Tint) cc_default).
Notation UNLOCK := (EF_external "UNLOCK" UNLOCK_SIG).

Require Import (*compcert_linking*) permissions.

Module ThreadPool.
  Section ThreadPool.
    
    Variable cT : Type.
    
    Record t := mk
                  { num_threads : pos
                    ; pool :> 'I_num_threads -> cT
                    ; perm_maps : 'I_num_threads -> access_map
                    ; counter : nat
                  }.
    
  End ThreadPool.
End ThreadPool.

Notation pool := ThreadPool.t.

Section poolDefs.

  Variable cT : Type.

  Variable (tp : ThreadPool.t cT).

  Import ThreadPool.

  Notation num_threads := (ThreadPool.num_threads tp).
  Notation thread_pool := (t cT).
  
  (* Per-thread disjointness definition*)
  Definition race_free tp :=
    forall tid0 tid0' (Htid0 : tid0 < (@ThreadPool.num_threads cT tp))
      (Htid0' : tid0' < (@ThreadPool.num_threads cT tp)) (Htid: tid0 <> tid0'),
      permMapsDisjoint (perm_maps tp (Ordinal Htid0))
                       (perm_maps tp (Ordinal Htid0')).

  Definition newPermMap_wf pmap :=
    forall tid0 (Htid0 : tid0 < num_threads),
      permMapsDisjoint ((perm_maps tp) (Ordinal Htid0)) pmap.

  Require Import fintype.

  Lemma unlift_m_inv : forall tid (Htid : tid < num_threads.+1) ord
                         (Hunlift: unlift (ordinal_pos_incr num_threads)
                                          (Ordinal (n:=num_threads.+1) (m:=tid) Htid)
                                   = Some ord),
                         nat_of_ord ord = tid.
  Proof.
    intros.
    assert (Hcontra: unlift_spec (ordinal_pos_incr num_threads)
                                 (Ordinal (n:=num_threads.+1) (m:=tid) Htid) (Some ord)).
    rewrite <- Hunlift.
    apply/unliftP.
    inversion Hcontra; subst.
    inversion H0.
    unfold bump.
    assert (pf: ord < num_threads)
      by (by rewrite ltn_ord).
    assert (H: num_threads <= ord = false).
    rewrite ltnNge in pf.
    rewrite <- Bool.negb_true_iff. auto.
    rewrite H. simpl. rewrite add0n. reflexivity.
  Defined.
  
  Definition addThread (c : cT) (pmap : access_map) : thread_pool :=
    let: new_num_threads := pos_incr num_threads in
    let: new_tid := ordinal_pos_incr num_threads in
    @mk cT new_num_threads
        (fun (n : 'I_new_num_threads) => 
           match unlift new_tid n with
             | None => c
             | Some n' => tp n'
           end)
        (fun (n : 'I_new_num_threads) => 
           match unlift new_tid n with
             | None => pmap
             | Some n' => (perm_maps tp) n'
           end)
        ((counter tp).+1).

  Lemma addThread_racefree :
    forall c p (Hwf: newPermMap_wf p) (Hrace: race_free tp),
      race_free (addThread c p).
  Proof.
    unfold race_free in *. intros.
    simpl.
    match goal with
      | [ |- context[ match ?Expr with _ => _ end]] =>
        destruct Expr as [ord0|] eqn:Hget0
    end;
      match goal with
        | [ |- context[ match ?Expr with _ => _ end]] =>
          destruct Expr as [ord1|] eqn:Hget1
      end; simpl in *.
    - apply unlift_m_inv in Hget0.
      apply unlift_m_inv in Hget1. subst.
      destruct ord0 as [tid0 pf0], ord1 as [tid1 pf1]; simpl in Htid.
      eapply Hrace; eauto.
    - apply unlift_m_inv in Hget0.
      subst. unfold newPermMap_wf in Hwf.
      destruct ord0. eapply Hwf; eauto.
    - apply unlift_m_inv in Hget1.
      subst. unfold newPermMap_wf in Hwf.
      destruct ord1. apply permMapsDisjoint_comm. eapply Hwf; eauto.
    - destruct (tid0 == num_threads) eqn:Heq0.
      + move/eqP:Heq0=>Heq0. subst.
        assert (Hcontra: (ordinal_pos_incr num_threads) !=
                                                        (Ordinal (n:=num_threads.+1) (m:=tid0') Htid0')).
        { apply/eqP. intros Hcontra.
          unfold ordinal_pos_incr in Hcontra.
          inversion Hcontra; auto.
        }
        exfalso. apply unlift_some in Hcontra. rewrite Hget1 in Hcontra.
        destruct Hcontra. discriminate.
      + move/eqP:Heq0=>Heq0.
        assert (Hcontra: (ordinal_pos_incr num_threads) !=
                                                        (Ordinal (n:=num_threads.+1) (m:=tid0) Htid0)).
        { apply/eqP. intros Hcontra.
          unfold ordinal_pos_incr in Hcontra. inversion Hcontra. subst. auto. }
        exfalso. apply unlift_some in Hcontra. rewrite Hget0 in Hcontra. destruct Hcontra.
        discriminate.
  Defined.
  
  Definition updThreadC (tid : 'I_num_threads) (c' : cT) : thread_pool :=
    @mk cT num_threads (fun (n : 'I_num_threads) =>
                          if n == tid then c' else tp n) (perm_maps tp)
        (counter tp).

  Definition updThreadP (tid : 'I_num_threads) (pmap' : access_map) : thread_pool :=
    @mk cT num_threads (pool tp) (fun (n : 'I_num_threads) =>
                                    if n == tid then pmap' else (perm_maps tp) n)
        (counter tp).

  Definition permMap_wf pmap tid :=
    forall tid0 (Htid0 : tid0 < num_threads) (Hneq: tid <> tid0),
      permMapsDisjoint ((perm_maps tp) (Ordinal Htid0)) pmap.
  
  Definition updThread (tid : 'I_num_threads) (c' : cT)
             (pmap : access_map) (counter' : nat) : thread_pool :=
    @mk cT num_threads
        (fun (n : 'I_num_threads) =>
           if n == tid then c' else tp n)
        (fun (n : 'I_num_threads) =>
           if n == tid then pmap else (perm_maps tp) n) 
        counter'.

  Lemma updThread_wf : forall tid (pf : tid < num_threads) pmap
                         (Hwf: permMap_wf pmap tid)
                         c'  counter'
                         (Hrace_free: race_free tp),
                         race_free (updThread (Ordinal pf) c' pmap counter').
  Proof.
    intros.
    unfold race_free. intros.
    simpl.
    destruct (Ordinal (n:=num_threads) (m:=tid0) Htid0 ==  Ordinal (n:=num_threads) (m:=tid) pf) eqn:Heq0,
                                                                                                     (Ordinal (n:=num_threads) (m:=tid0') Htid0' == Ordinal (n:=num_threads) (m:=tid) pf) eqn:Heq0'.
    - move/eqP:Heq0 => Heq0. subst.
      move/eqP:Heq0' => Heq0'. inversion Heq0'. inversion Heq0; subst. exfalso; auto.
    - move/eqP:Heq0=>Heq0. inversion Heq0. subst. 
      apply permMapsDisjoint_comm.
      eapply Hwf. simpl; auto.
    - move/eqP:Heq0'=>Heq0'. inversion Heq0'. subst.
      eapply Hwf. simpl; auto.
    - simpl in *. eapply Hrace_free; eauto.
  Defined.
  
  Definition getThreadC (tid : 'I_num_threads) : cT := tp tid.
  
  Definition getThreadPerm (tid : 'I_num_threads) : access_map := (perm_maps tp) tid.

  Import Maps.

  Definition perm_compatible p :=
    forall tid (b : positive) (ofs : Z) ,
      Mem.perm_order'' (Maps.PMap.get b p ofs)
                       (Maps.PMap.get b (getThreadPerm tid) ofs).

  Record mem_compatible m :=
    { perm_comp: perm_compatible (getMaxPerm m);
      mem_canonical: isCanonical (getMaxPerm m)
    }.

End poolDefs.

Arguments updThread {_} tp tid c' pmap counter'.
Arguments addThread {_} tp c pmap.

Section poolLemmas.

  Context {cT : Type} (tp : ThreadPool.t cT).

  Import ThreadPool.

  Lemma gssThreadCode (tid : 'I_(num_threads tp)) c' p' counter' : 
    getThreadC (updThread tp tid c' p' counter') tid = c'.
  Proof. by rewrite /getThreadC /updThread /= eq_refl. Defined.

  Lemma gsoThread (tid tid' : 'I_(num_threads tp)) c' p' counter':
    tid' != tid -> getThreadC (updThread tp tid c' p' counter') tid' = getThreadC tp tid'.
  Proof. by rewrite /getThreadC /updThread /=; case Heq: (tid' == tid). Defined.

  Lemma gssThreadPerm (tid : 'I_(num_threads tp)) c' p' counter' : 
    getThreadPerm (updThread tp tid c' p' counter') tid = p'.
  Proof. by rewrite /getThreadC /updThread /= eq_refl. Defined.

  Lemma gsoThreadPerm (tid tid' : 'I_(num_threads tp)) c' p' counter':
    tid' != tid -> getThreadPerm (updThread tp tid c' p' counter') tid' = getThreadPerm tp tid'.
  Proof. by rewrite /getThreadPerm /updThread /=; case Heq: (tid' == tid). Defined.

  Lemma getAddThread c pmap tid :
    tid = ordinal_pos_incr (num_threads tp) ->
    getThreadC (addThread tp c pmap) tid = c.
  Proof. by rewrite /getThreadC /addThread /= => <-; rewrite unlift_none. Qed.

  Lemma permMapsInv_lt : forall p (Hinv: perm_compatible tp p) tid,
                           permMapLt (getThreadPerm tp tid) p.
  Proof.
    intros. 
    unfold permMapLt; auto.
  Qed.

  Definition restrPermMap p' m (Hlt: permMapLt p' (getMaxPerm m)) : mem.
  Proof.
    refine ({|
               Mem.mem_contents := Mem.mem_contents m;
               Mem.mem_access :=
                 (fun ofs k =>
                    match k with
                      | Cur => None
                      | Max => fst (Mem.mem_access m) ofs k
                    end, Maps.PTree.map (fun b f =>
                                           fun ofs k =>
                                             match k with
                                               | Cur =>
                                                 (Maps.PMap.get b p') ofs
                                               | Max =>
                                                 f ofs Max
                                             end) (Mem.mem_access m).2);
               Mem.nextblock := Mem.nextblock m;
               Mem.access_max := _;
               Mem.nextblock_noaccess := _;
               Mem.contents_default := Mem.contents_default m |}).
    - unfold permMapLt in Hlt.
      assert (Heq: forall b ofs, Maps.PMap.get b (getMaxPerm m) ofs =
                            Maps.PMap.get b (Mem.mem_access m) ofs Max).
      { unfold getMaxPerm. intros.
        rewrite Maps.PMap.gmap. reflexivity. }
      intros.
      specialize (Hlt b ofs).
      specialize (Heq b ofs).
      unfold getMaxPerm in Hlt.
      unfold Maps.PMap.get in *. simpl in *.
      rewrite Maps.PTree.gmap; simpl.
      match goal with
        | [|- context[match Coqlib.option_map ?Expr1 ?Expr2  with _ => _ end]] =>
          destruct (Coqlib.option_map Expr1 Expr2) as [f|] eqn:?
      end; auto; unfold Coqlib.option_map in Heqo.
      destruct (Maps.PTree.get b (Mem.mem_access m).2) eqn:?; try discriminate.
      + inversion Heqo; subst; clear Heqo.
        rewrite Heq in Hlt. auto.
      + unfold Mem.perm_order''. by destruct ((Mem.mem_access m).1 ofs Max).
    - intros b ofs k Hnext.
    - unfold permMapLt in Hlt.
      assert (Heq: forall b ofs, Maps.PMap.get b (getMaxPerm m) ofs =
                            Maps.PMap.get b (Mem.mem_access m) ofs Max).
      { unfold getMaxPerm. intros.
        rewrite Maps.PMap.gmap. reflexivity. }
      specialize (Hlt b ofs).
      specialize (Heq b ofs).
      unfold Maps.PMap.get in *.
      simpl in *.
      rewrite Maps.PTree.gmap; simpl.
      assert (H := Mem.nextblock_noaccess m).
      specialize (H b). unfold Maps.PMap.get in H.
      match goal with
        | [|- context[match Coqlib.option_map ?Expr1 ?Expr2  with _ => _ end]] =>
          destruct (Coqlib.option_map Expr1 Expr2) as [f|] eqn:?
      end; auto; unfold Coqlib.option_map in Heqo;
      destruct (Maps.PTree.get b (Mem.mem_access m).2) eqn:Heqo2; try discriminate.
      inversion Heqo. subst f. clear Heqo.
      destruct k; auto.
      rewrite Heq in Hlt.
      specialize (H ofs Max). rewrite H in Hlt; auto.
      unfold Mem.perm_order'' in Hlt. destruct (Maps.PTree.get b p'.2).
      destruct (o0 ofs); tauto.
      destruct (p'.1 ofs); tauto.
      rewrite H; auto. destruct k; auto.
  Defined.
  
  Lemma restrPermMap_nextblock :
    forall p' m (Hlt: permMapLt p' (getMaxPerm m)),
      Mem.nextblock (restrPermMap Hlt) = Mem.nextblock m.
  Proof.
    intros. unfold restrPermMap. reflexivity.
  Qed.

  Lemma restrPermMap_irr : forall p' p'' m
                             (Hlt : permMapLt p' (getMaxPerm m))
                             (Hlt': permMapLt p'' (getMaxPerm m))
                             (Heq_new: p' = p''),
                             restrPermMap Hlt = restrPermMap Hlt'.
  Proof.
    intros. subst.
    apply f_equal. by apply proof_irr.
  Qed.

  Lemma restrPermMap_disjoint_inv:
    forall (mi mj m : mem) (pi pj : access_map)
      (Hcan_m: isCanonical (getMaxPerm m))
      (Hltj: permMapLt pj (getMaxPerm m))
      (Hlti: permMapLt pi (getMaxPerm m))
      (Hdisjoint: permMapsDisjoint pi pj)
      (Hrestrj: restrPermMap Hltj = mj)
      (Hrestri: restrPermMap Hlti = mi),
      permMapsDisjoint (getCurPerm mi) (getCurPerm mj).
  Proof.
    intros. rewrite <- Hrestri. rewrite <- Hrestrj.
    unfold restrPermMap, getCurPerm, permMapsDisjoint. simpl in *.
    intros b ofs.
    do 2 rewrite Maps.PMap.gmap.
    clear Hrestrj Hrestri.
    unfold permMapLt, Mem.perm_order'' in *.
    specialize (Hltj b ofs); specialize (Hlti b ofs).
    unfold getMaxPerm in *; simpl in *.
    rewrite Maps.PMap.gmap in Hlti, Hltj.
    unfold permMapsDisjoint, Maps.PMap.get in *; simpl in *.
    do 2 rewrite Maps.PTree.gmap. unfold Coqlib.option_map.
    specialize (Hdisjoint b ofs).
    assert (Hnone: (Mem.mem_access m).1 ofs Max = None)
      by (unfold isCanonical in Hcan_m; simpl in Hcan_m;
            by apply equal_f with (x:=ofs) in Hcan_m).
    destruct (Maps.PTree.get b (Mem.mem_access m).2) eqn:?; auto.
    rewrite Hnone in Hlti, Hltj;
      destruct (Maps.PTree.get b pi.2)
      as [f1 |] eqn:?;
                destruct (Maps.PTree.get b pj.2) as [f2|] eqn:?;
      repeat match goal with
               | [H: match ?Expr with _ => _ end |- _] => destruct Expr
             end; tauto.
  Qed.
  
  Lemma no_race_wf : forall tid (pf: tid < (num_threads tp)) (Hrace: race_free tp),
                       permMap_wf tp (getThreadPerm tp (Ordinal pf)) tid.
  Proof.
    intros. unfold permMap_wf; auto.
  Defined.

End poolLemmas.

Module Concur.
  Section Concur.
    
    Import ThreadPool.
    Context {cT G : Type} {the_sem : CoreSemantics G cT Mem.mem}.
    
    Notation cT' := (@ctl cT).
    Notation thread_pool := (t cT').
    Notation perm_map := access_map.

    Variable the_ge : G.
    Variable aggelos : nat -> delta_map.
    Variable lp_id : nat.

    Definition containsThread: ThreadPool.t cT' -> nat -> Prop:=
      fun ms tid0 => tid0 < (ThreadPool.num_threads ms).
    
    Record invariant tp :=
      { canonical : forall tid, isCanonical (perm_maps tp tid);
        no_race : race_free tp;
        lock_pool : forall (pf : 0 < num_threads tp), exists c,
                      getThreadC tp (Ordinal pf) = Krun c /\ halted the_sem c
      }.
    
    (* Semantics of the coarse-grained concurrent machine*)
    Definition cont2ord {ms tid0} (cnt: containsThread ms tid0) :=
      Ordinal cnt.

    
    Inductive dry_step {tid0 tp m} (cnt: containsThread tp tid0)
      (Hcompatible: mem_compatible tp m) : thread_pool -> mem  -> Prop :=
    | step_dry :
        forall (tp':thread_pool) c m1 m' (c' : cT),
          let: n := counter tp in
          let: tid := cont2ord cnt in
          forall (Hrestrict_pmap:
               restrPermMap (permMapsInv_lt (perm_comp Hcompatible) tid) = m1)
            (Hinv : invariant tp)
            (Hthread: getThreadC tp tid = Krun c)
            (Hcorestep: corestep the_sem the_ge c m1 c' m')
            (Htp': tp' = @updThread cT' tp tid (Krun c') (getCurPerm m') n),
            dry_step cnt Hcompatible tp' m'.
    
    (*missing lock-ranges*)
    Inductive ext_step {tid0 tp m}
              (cnt0:containsThread tp tid0)(Hcompat:mem_compatible tp m):
      thread_pool -> mem -> Prop :=
    | step_lock :
        forall (tp':thread_pool) m1 c c' m' b ofs
          (cnt_lp: containsThread tp lp_id),
          let: n := counter tp in
          let: tid := cont2ord cnt0 in
          let: lp := cont2ord cnt_lp in
          forall
            (Hinv : invariant tp)
            (Hthread: getThreadC tp tid = Kstop c)
            (Hat_external: at_external the_sem c =
                           Some (LOCK, ef_sig LOCK, Vptr b ofs::nil))
            (Hcompatible: mem_compatible tp m)
            (Hrestrict_pmap: restrPermMap (permMapsInv_lt (perm_comp Hcompatible) lp) = m1)
            (Hload: Mem.load Mint32 m1 b (Int.intval ofs) = Some (Vint Int.one))
            (Hstore: Mem.store Mint32 m1 b (Int.intval ofs) (Vint Int.zero) = Some m')
            (Hat_external: after_external the_sem (Some (Vint Int.zero)) c = Some c')
            (Htp': tp' = updThread tp tid (Kresume c')
                                   (computeMap (getThreadPerm tp tid) (aggelos n)) (n+1)),
            ext_step cnt0 Hcompat tp' m' 
                     
    | step_unlock :
        forall  (tp':thread_pool) m1 c c' m' b ofs
           (cnt_lp: containsThread tp lp_id),
          let: n := counter tp in
          let: tid := cont2ord cnt0 in
          let: lp := cont2ord cnt_lp in
          forall
            (Hinv : invariant tp)
            (Hthread: getThreadC tp tid = Kstop c)
            (Hat_external: at_external the_sem c =
                           Some (UNLOCK, ef_sig UNLOCK, Vptr b ofs::nil))
            (Hrestrict_pmap: restrPermMap (permMapsInv_lt (perm_comp Hcompat) lp) = m1)
            (Hload: Mem.load Mint32 m1 b (Int.intval ofs) = Some (Vint Int.zero))
            (Hstore: Mem.store Mint32 m1 b (Int.intval ofs) (Vint Int.one) = Some m')
            (* what does the return value denote?*)
            (Hat_external: after_external the_sem (Some (Vint Int.zero)) c = Some c')
            (* (Hangel_wf: permMap_wf tp (aggelos n) tid0) *)
            (* (Hangel_canonical: isCanonical (aggelos n)) *)
            (Htp': tp' = updThread tp tid (Kresume c')
                                   (computeMap (getThreadPerm tp tid) (aggelos n)) (n+1)),
            ext_step cnt0 Hcompat tp' m' 
                     
    | step_create :
        forall  (tp_upd tp':thread_pool) c c' c_new vf arg,
          let: n := counter tp in
          let: tid := cont2ord cnt0 in
          forall
            (Hinv : invariant tp)
            (Hthread: getThreadC tp tid = Kstop c)
            (Hat_external: at_external the_sem c =
                           Some (CREATE, ef_sig CREATE, vf::arg::nil))
            (Hinitial: initial_core the_sem the_ge vf (arg::nil) = Some c_new)
            (Hafter_external: after_external the_sem
                                                       (Some (Vint Int.zero)) c = Some c')
            (Htp': tp_upd = updThread tp tid (Kresume c')
                                      (computeMap (getThreadPerm tp tid) (aggelos n)) (n.+2))
            (* (Hangel_wf: permMap_wf tp (aggelos n) tid0) *)
            (* (Hangel_canonical: isCanonical (aggelos n)) *)
            (* (Hangel_wf2: newPermMap_wf tp_upd (aggelos (n.+1))) *)
            (* (Hangel_canonical2: isCanonical (aggelos (n.+1))) *)
            (* NOTE: Something to be done with the new thread!!! *)
            (Htp': tp' = addThread tp_upd (Kresume c_new)
                                   (computeMap empty_map (aggelos n.+1))),
            ext_step cnt0 Hcompat tp' m
                     
    | step_mklock :
        forall  (tp' tp'': thread_pool) m1 c c' m' b ofs pmap_tid' pmap_lp
           (cnt_lp': containsThread tp' lp_id)
           (cnt_lp: containsThread tp lp_id),
          let: n := counter tp in
          let: tid := cont2ord cnt0 in
          let: lp := cont2ord cnt_lp in
          let: lp' := cont2ord cnt_lp' in
          let: pmap_tid := getThreadPerm tp tid in
          forall
            (Hinv : invariant tp)
            (Hthread: getThreadC tp tid = Kstop c)
            (Hat_external: at_external the_sem c =
                           Some (MKLOCK, ef_sig MKLOCK, Vptr b ofs::nil))
            (Hrestrict_pmap: restrPermMap
                               (permMapsInv_lt (perm_comp Hcompat) tid) = m1)
            (Hstore: Mem.store Mint32 m1 b (Int.intval ofs) (Vint Int.zero) = Some m')
            (Hdrop_perm:
               setPerm (Some Nonempty) b (Int.intval ofs) pmap_tid = pmap_tid')
            (Hlp_perm: setPerm (Some Writable)
                               b (Int.intval ofs) (getThreadPerm tp lp) = pmap_lp)
            (Hat_external: after_external
                             the_sem (Some (Vint Int.zero)) c = Some c')
            (Htp': tp' = updThread tp tid (Kresume c') pmap_tid' (n+1))
            (Htp'': tp'' = updThreadP tp' lp' pmap_lp),
            ext_step cnt0 Hcompat tp'' m' 
                     
    | step_freelock :
        forall  (tp' tp'': thread_pool) c c' b ofs pmap_lp'
           (cnt_lp': containsThread tp' lp_id)
           (cnt_lp: containsThread tp lp_id),
          let: n := counter tp in
          let: tid := cont2ord cnt0 in
          let: lp := cont2ord cnt_lp in
          let: lp' := cont2ord cnt_lp' in
          let: pmap_lp := getThreadPerm tp tid in
          forall
            (Hinv : invariant tp)
            (Hthread: getThreadC tp tid = Kstop c)
            (Hat_external: at_external the_sem c =
                           Some (FREE_LOCK, ef_sig FREE_LOCK, Vptr b ofs::nil))
            (Hdrop_perm:
               setPerm None b (Int.intval ofs) pmap_lp = pmap_lp')
            (Hat_external: after_external the_sem (Some (Vint Int.zero)) c = Some c')
            (*the angel must provide the permissions for the thread - freeable or writeable *)
            (* (Hangel_wf: permMap_wf tp (aggelos n) tid0) *)
            (* (Hangel_canonical: isCanonical (aggelos n)) *)
            (Htp': tp' = updThread tp tid (Kresume c')
                                   (computeMap (getThreadPerm tp tid) (aggelos n)) (n+1))       
            (Htp'': tp'' = updThreadP tp' lp' pmap_lp'),
            ext_step cnt0 Hcompat  tp'' m 
                     
    | step_lockfail :
        forall  c b ofs m1
           (cnt_lp: containsThread tp lp_id),
          let: n := counter tp in
          let: tid := cont2ord cnt0 in
          let: lp := cont2ord cnt_lp in
          forall
            (Hinv : invariant tp)
            (Hthread: getThreadC tp tid = Kstop c)
            (Hat_external: at_external the_sem c =
                           Some (LOCK, ef_sig LOCK, Vptr b ofs::nil))
            (Hrestrict_pmap: restrPermMap
                               (permMapsInv_lt (perm_comp Hcompat) lp) = m1)
            (Hload: Mem.load Mint32 m1 b (Int.intval ofs) = Some (Vint Int.zero)),
            ext_step cnt0 Hcompat tp m.
  End Concur.

  Module Type DrySemantics.
    Parameter G: Type.
    Parameter C: Type.
    Definition M: Type:= mem.
    Parameter Sem: CoreSemantics G C M.
  End DrySemantics.
  
  Module DryMachineSig (Sem: DrySemantics) <: ConcurrentMachineSig NatTID.
    (*TID = NAT*)
    Definition tid := nat.                                             
    (*Memories*)
    Definition richMem: Type:= Sem.M.
    Definition dryMem: richMem -> mem:= id.
    
    (*CODE*)
    Definition cT: Type:= Sem.C.
    Definition G: Type:= Sem.G.
    Definition Sem := Sem.Sem.
    Definition cT': Type := @ctl cT.
    
    (*thread pool*)
    Import ThreadPool.  
    Notation thread_pool := (t cT').  
    
    (*MACHINE VARIABLES*)
    Definition machine_state: Type:= thread_pool.
    Definition containsThread: machine_state -> tid -> Prop:=
      fun ms tid0 => tid0 < (num_threads ms).
    Definition lp_id : tid:= 0.
    
    (*INVARIANTS*)
    (*The state respects the memory*)
    Definition mem_compatible: machine_state -> mem -> Prop:=
      @mem_compatible cT'.
    
    (*Steps*)
    Definition cstep (genv:G): forall {tid0 ms m},
                                 containsThread ms tid0 -> mem_compatible ms m ->
                                 machine_state -> mem -> Prop:=
      @dry_step cT G Sem genv.
    
    Inductive resume_thread': forall {tid0} {ms:machine_state},
                                containsThread ms tid0 -> machine_state -> Prop:=
    | ResumeThread: forall tid0 ms ms' c
                      (ctn: containsThread ms tid0)
                      (HC: getThreadC ms (cont2ord ctn) = Kresume c)
                      (Hms': updThreadC ms (cont2ord ctn) (Krun c)  = ms'),
                      resume_thread' ctn ms'.
    Definition resume_thread: forall {tid0 ms},
                                containsThread ms tid0 -> machine_state -> Prop:=
      @resume_thread'.

    Inductive suspend_thread': forall {tid0} {ms:machine_state},
                                 containsThread ms tid0 -> machine_state -> Prop:=
    | SuspendThread: forall tid0 ms ms' c
                       (ctn: containsThread ms tid0)
                       (HC: getThreadC ms (cont2ord ctn) = Krun c)
                       (Hms': updThreadC ms (cont2ord ctn) (Kstop c)  = ms'),
                       suspend_thread' ctn ms'.
    Definition suspend_thread : forall {tid0 ms},
                                  containsThread ms tid0 -> machine_state -> Prop:=
      @suspend_thread'.
    
    Definition conc_call (genv:G):
      forall {tid0 ms m},
        (nat -> delta_map) -> containsThread ms tid0 -> mem_compatible ms m ->
        machine_state -> mem -> Prop:=
      fun tid ms m aggelos => @ext_step cT G Sem genv aggelos lp_id tid ms m.
    
    Inductive threadHalted': forall {tid0 ms},
                               containsThread ms tid0 -> Prop:=
    | thread_halted':
        forall tp c tid0
          (ctn: containsThread tp tid0),
          let: tid := cont2ord ctn in
          forall
            (Hthread: getThreadC tp tid = Krun c)
            (Hcant: halted Sem c),
            threadHalted' ctn. 
    Definition threadHalted: forall {tid0 ms},
                               containsThread ms tid0 -> Prop:= @threadHalted'.

    Parameter init_core : G -> val -> list val -> option machine_state.
  End DryMachineSig.

  (* Here I make the core semantics*)
  Variable example_G: Type.
  Variable example_C: Type.
  Variable example_sem: CoreSemantics example_G example_C mem.
  Module Sem: DrySemantics.
    Definition G:= example_G.
    Definition C:= example_C.
    Definition M:= mem.
    Definition Sem:=example_sem.
  End Sem.
  Module mySchedule := ListScheduler NatTID.
  Module mySem := DryMachineSig Sem.
  Module myCoarseSemantics :=
    CoarseMachine NatTID mySchedule mySem.
  Module myFineSemantics :=
    FineMachine NatTID mySchedule mySem.

  Definition coarse_semantics:=
    myCoarseSemantics.MachineSemantics.
  Definition fine_semantics:=
    myFineSemantics.MachineSemantics.
  
End Concur.



(* After this there needs to be some cleaning. *)










(* Section InitialCore. *)

(*   Context {cT G : Type} {the_sem : CoreSemantics G cT Mem.mem}. *)
(*   Import ThreadPool. *)

  
(*   Notation thread_pool := (t cT). *)
(*   Notation perm_map := access_map. *)
  
(*   Definition at_external (st : (list nat) * thread_pool) *)
(*   : option (external_function * signature * seq val) := None. *)

(*   Definition after_external (ov : option val) (st : list nat * thread_pool) : *)
(*     option (list nat * thread_pool) := None. *)

(*   Definition two_pos : pos := mkPos NPeano.Nat.lt_0_2. *)
  
(*   Definition ord1 := Ordinal (n := two_pos) (m := 1) (leqnn two_pos). *)

(*   (*not clear what the value of halted should be*) *)
(*   Definition halted (st : list nat * thread_pool) : option val := None. *)

(*   Variable compute_init_perm : G -> access_map. *)
(*   Variable lp_code : cT. *)
(*   Variable sched : list nat. *)

(*   Definition initial_core the_ge (f : val) (args : list val) : option (list nat * thread_pool) := *)
(*     match initial_core the_sem the_ge f args with *)
(*       | None => None *)
(*       | Some c => *)
(*         Some (sched, ThreadPool.mk *)
(*                        two_pos *)
(*                        (fun tid => if tid == ord0 then lp_code *)
(*                                 else if tid == ord1 then c *)
(*                                      else c (*bogus value; can't occur*)) *)
(*                        (fun tid => if tid == ord0 then empty_map else *)
(*                                   if tid == ord1 then compute_init_perm the_ge *)
(*                                   else empty_map) *)
(*                        0) *)
(*     end. *)

(*   Variable aggelos : nat -> access_map. *)

(*   Definition cstep (the_ge : G) (st : list nat * thread_pool) m *)
(*              (st' : list nat * thread_pool) m' := *)
(*     @step cT G the_sem the_ge aggelos (@coarse_step cT G the_sem the_ge) *)
(*           (fst st) (snd st) m (fst st') (snd st') m'. *)

(*   Definition fstep (the_ge : G) (st : list nat * thread_pool) m *)
(*              (st' : list nat * thread_pool) m' := *)
(*     @step cT G the_sem the_ge aggelos (@fine_step cT G the_sem the_ge) *)
(*           (fst st) (snd st) m (fst st') (snd st') m'. *)
  
(*   Program Definition coarse_semantics : *)
(*     CoreSemantics G (list nat * thread_pool) mem := *)
(*     Build_CoreSemantics _ _ _ *)
(*                         initial_core *)
(*                         at_external *)
(*                         after_external *)
(*                         halted *)
(*                         cstep *)
(*                         _ _ _. *)

(*   Program Definition fine_semantics : *)
(*     CoreSemantics G (list nat * thread_pool) mem := *)
(*     Build_CoreSemantics _ _ _ *)
(*                         initial_core *)
(*                         at_external *)
(*                         after_external *)
(*                         halted *)
(*                         fstep *)
(*                         _ _ _. *)

(* End InitialCore. *)
(* End Concur. *)