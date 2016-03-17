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

(*From msl get the juice! *)
Require Import rmaps.
Require Import compcert_rmaps.
Require Import juicy_mem.
Require Import juicy_extspec.
Require Import jstep.


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


Module LockPool.
  Definition LockPool:= address -> option rmap.
End LockPool.
Export LockPool.

Module ThreadPool.
  Section ThreadPool.
    
    Variable cT : Type.

    Record t := mk
                  { num_threads : pos
                    ; pool :> 'I_num_threads -> cT
                    ; juice : 'I_num_threads -> rmap;
                    lpool : LockPool
                                                
                  }.
    
  End ThreadPool.
End ThreadPool.

Notation tpool := ThreadPool.t.

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
      joins (juice tp (Ordinal Htid0))
                       (juice tp (Ordinal Htid0')).

  Definition newJuice_wf pmap :=
    forall tid0 (Htid0 : tid0 < num_threads),
      joins ((juice tp) (Ordinal Htid0)) pmap.

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
  
  Definition addThread (c : cT) (pmap : rmap) : thread_pool :=
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
             | Some n' => (juice tp) n'
           end)
        ((lpool tp)).

  Lemma addThread_racefree :
    forall c p (Hwf: newJuice_wf p) (Hrace: race_free tp),
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
      subst. unfold newJuice_wf in Hwf.
      destruct ord0. eapply Hwf; eauto.
    - apply unlift_m_inv in Hget1.
      subst. unfold newJuice_wf in Hwf.
      destruct ord1.
      apply joins_comm. eapply Hwf; eauto.
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
                          if n == tid then c' else tp n) (juice tp)
        (lpool tp).

  Definition updThreadP (tid : 'I_num_threads) (pmap' : rmap) : thread_pool :=
    @mk cT num_threads (pool tp) (fun (n : 'I_num_threads) =>
                                    if n == tid then pmap' else (juice tp) n)
        (lpool tp).

  Definition permMap_wf pmap tid :=
    forall tid0 (Htid0 : tid0 < num_threads) (Hneq: tid <> tid0),
      joins ((juice tp) (Ordinal Htid0)) pmap.
  
  Definition updThread (tid : 'I_num_threads) (c' : cT)
             (pmap : rmap): thread_pool :=
    @mk cT num_threads
        (fun (tid' : 'I_num_threads) =>
           if tid' == tid then c' else tp tid')
        (fun (tid' : 'I_num_threads) =>
           if tid' == tid then pmap else (juice tp) tid') 
         (lpool tp).

  Lemma updThread_wf : forall tid (pf : tid < num_threads) pmap
                         (Hwf: permMap_wf pmap tid)
                         c'
                         (Hrace_free: race_free tp),
                         race_free (updThread (Ordinal pf) c' pmap).
  Proof.
    intros.
    unfold race_free. intros.
    simpl.
    destruct (Ordinal (n:=num_threads) (m:=tid0) Htid0 ==  Ordinal (n:=num_threads) (m:=tid) pf) eqn:Heq0,
                                                                                                     (Ordinal (n:=num_threads) (m:=tid0') Htid0' == Ordinal (n:=num_threads) (m:=tid) pf) eqn:Heq0'.
    - move/eqP:Heq0 => Heq0. subst.
      move/eqP:Heq0' => Heq0'. inversion Heq0'. inversion Heq0; subst. exfalso; auto.
    - move/eqP:Heq0=>Heq0; inversion Heq0; subst. 
      apply joins_comm.
      eapply Hwf. simpl; auto.      
    - move/eqP:Heq0'=>Heq0'. inversion Heq0'. subst.
      eapply Hwf. simpl; auto.
    - simpl in *. eapply Hrace_free; eauto.
  Defined.
  
  Definition getThreadC (tid : 'I_num_threads) : cT := tp tid.
  
  Definition getThreadPerm (tid : 'I_num_threads) : rmap := (juice tp) tid.

  Import Maps.

  Record mem_cohere' m phi :=
    { cont_coh: contents_cohere m phi;
      acc_coh: access_cohere m phi;
      max_coh: max_access_cohere m phi;
      all_coh: alloc_cohere m phi
    }.
  Definition mem_cohere m:=
    forall tid, mem_cohere' m (getThreadPerm tid). 
      
  Record mem_compatible m :=
    { perm_comp: mem_cohere m;
      mem_canonical: isCanonical (getMaxPerm m)
    }.

End poolDefs.

Arguments updThread {_} tp tid c' pmap.
Arguments addThread {_} tp c pmap.

Section poolLemmas.

  Context {cT : Type} (tp : ThreadPool.t cT).

  Import ThreadPool.

  Lemma gssThreadCode (tid : 'I_(num_threads tp)) c' p' : 
    getThreadC (updThread tp tid c' p') tid = c'.
  Proof. by rewrite /getThreadC /updThread /= eq_refl. Defined.

  Lemma gsoThread (tid tid' : 'I_(num_threads tp)) c' p':
    tid' != tid -> getThreadC (updThread tp tid c' p') tid' = getThreadC tp tid'.
  Proof. by rewrite /getThreadC /updThread /=; case Heq: (tid' == tid). Defined.

  Lemma gssThreadPerm (tid : 'I_(num_threads tp)) c' p' : 
    getThreadPerm (updThread tp tid c' p') tid = p'.
  Proof. by rewrite /getThreadC /updThread /= eq_refl. Defined.

  Lemma gsoThreadPerm (tid tid' : 'I_(num_threads tp)) c' p':
    tid' != tid -> getThreadPerm (updThread tp tid c' p') tid' = getThreadPerm tp tid'.
  Proof. by rewrite /getThreadPerm /updThread /=; case Heq: (tid' == tid). Defined.

  Lemma getAddThread c pmap tid :
    tid = ordinal_pos_incr (num_threads tp) ->
    getThreadC (addThread tp c pmap) tid = c.
  Proof. by rewrite /getThreadC /addThread /= => <-; rewrite unlift_none. Qed.
(*
  Lemma permMapsInv_lt : forall m (Hinv: mem_compatible tp m) tid,
                           permMapLt (getThreadPerm tp tid) p.
  Proof.
    intros. 
    unfold permMapLt; auto.
  Qed.*)

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

  (*
  Lemma restrPermMap_disjoint_inv:
    forall (mi mj m : mem) (pi pj : rmap)
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
  Qed.*)
  
  Lemma no_race_wf : forall tid (pf: tid < (num_threads tp)) (Hrace: race_free tp),
                       permMap_wf tp (getThreadPerm tp (Ordinal pf)) tid.
  Proof.
    intros. unfold permMap_wf; auto.
  Defined.

End poolLemmas.

Module JMem.
  
  Definition load (chunk: memory_chunk)(phi: juicy_mem)(b:block)(ofs: Z) : option val:=
    match perm_of_res( (m_phi phi) @(b,ofs) ) with
    | None | Some Nonempty => None
    | _ => Mem.load chunk (m_dry phi) b ofs
    end.
  Definition store' (chunk: memory_chunk)(phi: juicy_mem)(b:block)(ofs: Z)(v:val) : option mem :=
    match perm_of_res( (m_phi phi) @(b,ofs) ) with
    | None | Some Nonempty | Some Readable  => None
    | _ =>  Mem.store chunk (m_dry phi) b ofs v     
    end.
  Definition store  (chunk: memory_chunk)(phi: juicy_mem)(b:block)(ofs: Z)(v:val) : option juicy_mem.
    destruct (store' chunk phi b ofs v) eqn:STR'.
    - pose (phi' := inflate_store m (m_phi phi)).
      apply Some. apply (mkJuicyMem m phi').
      + unfold contents_cohere; intros. admit.
      + admit.
      + admit.
      + admit.
    - exact None.
  Defined.
End JMem.

Module Concur.
  Section Concur.
    
    Import ThreadPool.
    Context {cT G : Type} {the_sem : CoreSemantics G cT mem}{LP:LockPool}.
    
    Notation cT' := (@ctl cT).
    Notation thread_pool := (t cT').
    Notation perm_map := rmap.

    Definition containsThread: ThreadPool.t cT' -> nat -> Prop:=
      fun ms tid0 => tid0 < (ThreadPool.num_threads ms).

    Variable the_ge : G.
    Variable aggelos : nat -> delta_map.
    
    Record invariant tp :=
      { (*canonical : forall tid, isCanonical (juice tp tid);*)
        no_race : race_free tp;
        lock_pool : forall (pf : 0 < num_threads tp), exists c,
                      getThreadC tp (Ordinal pf) = Krun c /\ halted the_sem c
      }.
    
    (* Semantics of the coarse-grained concurrent machine*)
    Definition cont2ord {ms tid0} (cnt: containsThread ms tid0) :=
      Ordinal cnt.

    Definition personal_mem {tid0 tp m} (cnt: containsThread tp tid0)
               (Hcompatible: mem_compatible tp m): juicy_mem.
    pose (tid := cont2ord cnt). 
    destruct Hcompatible as [perm_comp  mem_canon].
    destruct (perm_comp tid).                                                 
    apply (mkJuicyMem m (getThreadPerm tp tid)); auto.
    Defined.

    Definition juicy_sem:= (FSem.F _ _ JuicyFSem.t) _ _ the_sem.
    
    Inductive juicy_step {tid0 tp m} (cnt: containsThread tp tid0)
      (Hcompatible: mem_compatible tp m) : thread_pool -> mem  -> Prop :=
    | step_juicy :
        forall (tp':thread_pool) c jm jm' m' (c' : cT),
          let: lp := lpool tp in
          let: tid := cont2ord cnt in
          forall (Hpersonal_perm:
               personal_mem cnt Hcompatible = jm)
            (Hinv : invariant tp)
            (Hthread: getThreadC tp tid = Krun c)
            (Hcorestep: corestep juicy_sem the_ge c jm c' jm')
            (Htp': tp' = @updThread cT' tp tid (Krun c') (m_phi jm'))
            (Hm': m_dry jm' = m' ),
            juicy_step cnt Hcompatible tp' m'.
    
    (*missing lock-ranges*)
    Parameter get_fun_spec: juicy_mem -> address -> val -> option (pred rmap * pred rmap).
    Parameter get_lock_inv: juicy_mem -> address -> option (pred rmap).
    Parameter freelock: juicy_mem -> address -> option juicy_mem.
    Parameter mklock: juicy_mem -> address -> pred rmap -> option juicy_mem.
    Inductive conc_step {tid0 tp m}
              (cnt0:containsThread tp tid0)(Hcompat:mem_compatible tp m):
      thread_pool -> mem -> Prop :=
    | step_lock :
        forall (tp':thread_pool) jm c c' jm' b ofs d_phi phi',
          let: tid := cont2ord cnt0 in
          forall
            (Hinv : invariant tp)
            (Hthread: getThreadC tp tid = Kstop c)
            (Hat_external: at_external the_sem c =
                           Some (LOCK, ef_sig LOCK, Vptr b ofs::nil))
            (Hcompatible: mem_compatible tp m)
            (Hpersonal_perm: 
               personal_mem cnt0 Hcompatible = jm)
            (Hload: JMem.load Mint32 jm b (Int.intval ofs) = Some (Vint Int.one))
            (Hstore: JMem.store Mint32 jm b (Int.intval ofs) (Vint Int.zero) = Some jm')
            (Hat_external: after_external the_sem (Some (Vint Int.zero)) c = Some c')
            (His_unlocked:lpool tp (b, Int.intval ofs) = Some d_phi )
            (Hadd_lock_res: join (m_phi jm) d_phi  phi')  
            (Htp': tp' = updThread tp tid (Kresume c') phi'),
            conc_step cnt0 Hcompat tp' (m_dry jm')                 
    | step_unlock :
        forall  (tp':thread_pool) jm c c' jm' b ofs (d_phi phi':rmap) (R: pred rmap) ,
          let: tid := cont2ord cnt0 in
          forall
            (Hinv : invariant tp)
            (Hthread: getThreadC tp tid = Kstop c)
            (Hat_external: at_external the_sem c =
                           Some (UNLOCK, ef_sig UNLOCK, Vptr b ofs::nil))
            (Hcompatible: mem_compatible tp m)
            (Hpersonal_perm: 
               personal_mem cnt0 Hcompatible = jm)
            (Hload: JMem.load Mint32 jm b (Int.intval ofs) = Some (Vint Int.zero))
            (Hstore: JMem.store Mint32 jm b (Int.intval ofs) (Vint Int.one) = Some jm')
            (* what does the return value denote?*)
            (Hat_external: after_external the_sem (Some (Vint Int.zero)) c = Some c')
            (Hget_lock_inv: get_lock_inv jm (b, Int.intval ofs) = Some R)
            (Hsat_lock_inv: R d_phi)
            (Hrem_lock_res: join d_phi phi' (m_phi jm))
            (Htp': tp' = updThread tp tid (Kresume c') phi'),
            conc_step cnt0 Hcompat tp' (m_dry jm') 
                     
    | step_create :
        (* HAVE TO REVIEW THIS STEP LOOKING INTO THE ORACULAR SEMANTICS*)
        forall  (tp_upd tp':thread_pool) c c' c_new vf arg jm (d_phi phi': rmap) b ofs P Q,
          let: tid := cont2ord cnt0 in
          forall
            (Hinv : invariant tp)
            (Hthread: getThreadC tp tid = Kstop c)
            (Hat_external: at_external the_sem c =
                           Some (CREATE, ef_sig CREATE, vf::arg::nil))
            (Hinitial: initial_core the_sem the_ge vf (arg::nil) = Some c_new)
            (Hfun_sepc: vf = Vptr b ofs)
            (Hafter_external: after_external the_sem
                                             (Some (Vint Int.zero)) c = Some c')
            (Hcompatible: mem_compatible tp m)
            (Hpersonal_perm: 
               personal_mem cnt0 Hcompatible = jm)
            (Hget_fun_spec: get_fun_spec jm (b, Int.intval ofs) arg = Some (P,Q))
            (Hsat_fun_spec: P d_phi)
            (Hrem_fun_res: join d_phi phi' (m_phi jm))
            (Htp': tp_upd = updThread tp tid (Kresume c') phi')
            (Htp': tp' = addThread tp_upd (Kresume c_new) d_phi),
            conc_step cnt0 Hcompat tp' m
                     
    | step_mklock :
        forall  (tp' tp'': thread_pool) jm jm' jm_locked c c' b ofs R ,
          let: tid := cont2ord cnt0 in
          forall
            (Hinv : invariant tp)
            (Hthread: getThreadC tp tid = Kstop c)
            (Hat_external: at_external the_sem c =
                           Some (MKLOCK, ef_sig MKLOCK, Vptr b ofs::nil))
            (Hcompatible: mem_compatible tp m)
            (Hpersonal_perm: 
               personal_mem cnt0 Hcompatible = jm)
            (Hstore: JMem.store Mint32 jm b (Int.intval ofs) (Vint Int.zero) = Some jm_locked)
            (Hmklock: mklock jm_locked (b, Int.intval ofs) R = Some jm')
            (Hat_external: after_external
                             the_sem (Some (Vint Int.zero)) c = Some c')
            (Htp': tp' = updThread tp tid (Kresume c') (m_phi jm')),
            conc_step cnt0 Hcompat tp'' (m_dry jm') 
                     
    | step_freelock :
        forall  (tp' tp'': thread_pool) c c' b ofs jm jm',
          let: tid := cont2ord cnt0 in
          let: pmap_lp := getThreadPerm tp tid in
          forall
            (Hinv : invariant tp)
            (Hthread: getThreadC tp tid = Kstop c)
            (Hat_external: at_external the_sem c =
                           Some (FREE_LOCK, ef_sig FREE_LOCK, Vptr b ofs::nil))
            (Hcompatible: mem_compatible tp m)
            (Hpersonal_perm: 
               personal_mem cnt0 Hcompatible = jm)
            (Hload: JMem.load Mint32 jm b (Int.intval ofs) = Some (Vint Int.zero)) (*MAYBE IF I HOLD THE LOCK, it doesn't matter?? *)
            (Hfreelock: freelock jm (b, Int.intval ofs) = Some jm') (*SHOULD CHECK I HOLD THE LOCK!!!*)
            (Hat_external: after_external the_sem (Some (Vint Int.zero)) c = Some c')
            (Htp': tp' = updThread tp tid (Kresume c') (m_phi jm')),
            conc_step cnt0 Hcompat  tp'' (m_dry jm')  (* m_dry jm' = m_dry jm = m *)
                     
    | step_lockfail :
        forall  c b ofs jm,
          let: tid := cont2ord cnt0 in
          forall
            (Hinv : invariant tp)
            (Hthread: getThreadC tp tid = Kstop c)
            (Hat_external: at_external the_sem c =
                           Some (LOCK, ef_sig LOCK, Vptr b ofs::nil))
            (Hcompatible: mem_compatible tp m)
            (Hpersonal_perm: 
               personal_mem cnt0 Hcompatible = jm)
            (Hload: JMem.load Mint32 jm b (Int.intval ofs) = Some (Vint Int.zero)),
            conc_step cnt0 Hcompat tp m.
  End Concur.

  Module Type JuicySemantics.
    Parameter G: Type.
    Parameter C: Type.
    Definition M: Type:= mem.
    Parameter Sem: CoreSemantics G C M.
  End JuicySemantics.
  
  Module JuicyMachineSig (Sem: JuicySemantics) <: ConcurrentMachineSig NatTID.
                                                   
    (*TID = NAT*)
    Definition tid := nat.                                             
    (*Memories*)
    Definition richMem: Type:= juicy_mem.
    Definition dryMem: richMem -> mem:= m_dry.
    
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
    Definition lp_id : tid:= 0.                            (* Useless *)
    
    (*INVARIANTS*)
    (*The state respects the memory*)
    Definition mem_compatible: machine_state -> mem -> Prop:=
      @mem_compatible cT'.
    
    (*Steps*)
    Definition cstep (genv:G): forall {tid0 ms m},
                                 containsThread ms tid0 -> mem_compatible ms m ->
                                 machine_state -> mem -> Prop:=
      @juicy_step cT G Sem genv.
    
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
      forall {tid0 ms m}, (nat -> delta_map) -> containsThread ms tid0 -> mem_compatible ms m ->
        machine_state -> mem -> Prop:=
      fun tid ms m aggelos => @conc_step cT G Sem genv tid ms m.
    
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
  End JuicyMachineSig.

  (* Here I make the core semantics*)
  Variable example_G: Type.
  Variable example_C: Type.
  Variable example_sem: CoreSemantics example_G example_C mem.
  Module Sem: JuicySemantics.
    Definition G:= example_G.
    Definition C:= example_C.
    Definition M:= mem.
    Definition Sem:=example_sem.
  End Sem.
  Module mySchedule := ListScheduler NatTID.
  Module mySem := JuicyMachineSig Sem.
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
(*   Notation perm_map := rmap. *)
  
(*   Definition at_external (st : (list nat) * thread_pool) *)
(*   : option (external_function * signature * seq val) := None. *)

(*   Definition after_external (ov : option val) (st : list nat * thread_pool) : *)
(*     option (list nat * thread_pool) := None. *)

(*   Definition two_pos : pos := mkPos NPeano.Nat.lt_0_2. *)
  
(*   Definition ord1 := Ordinal (n := two_pos) (m := 1) (leqnn two_pos). *)

(*   (*not clear what the value of halted should be*) *)
(*   Definition halted (st : list nat * thread_pool) : option val := None. *)

(*   Variable compute_init_perm : G -> rmap. *)
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

(*   Variable aggelos : nat -> rmap. *)

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
