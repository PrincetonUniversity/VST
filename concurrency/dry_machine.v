Require Import compcert.lib.Axioms.

Add LoadPath "../concurrency" as concurrency.

Require Import sepcomp. Import SepComp.
Require Import sepcomp.semantics_lemmas.

Require Import concurrency.pos.
Require Import concurrency.concurrent_machine.
Require Import concurrency.pos.
Require Import Coq.Program.Program.
Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.

(*NOTE: because of redefinition of [val], these imports must appear 
  after Ssreflect eqtype.*)
Require Import compcert.common.AST.     (*for typ*)
Require Import compcert.common.Values. (*for val*)
Require Import compcert.common.Globalenvs. 
Require Import compcert.common.Memory.
Require Import compcert.lib.Integers.
Require Import threads_lemmas.

Require Import Coq.ZArith.ZArith.

Notation EXIT := 
  (EF_external "EXIT" (mksignature (AST.Tint::nil) None)). 

Notation CREATE_SIG :=
  (mksignature (AST.Tint::AST.Tint::nil) (Some AST.Tint) cc_default).
Notation CREATE := (EF_external "CREATE" CREATE_SIG).

Notation READ := 
  (EF_external "READ" (mksignature (AST.Tint::AST.Tint::AST.Tint::nil)
                                   (Some AST.Tint) cc_default)).
Notation WRITE := 
  (EF_external "WRITE" (mksignature (AST.Tint::AST.Tint::AST.Tint::nil)
                                    (Some AST.Tint) cc_default)).

Notation MKLOCK := 
  (EF_external "MKLOCK" (mksignature (AST.Tint::nil)
                                     (Some AST.Tint) cc_default)).
Notation FREE_LOCK := 
  (EF_external "FREE_LOCK" (mksignature (AST.Tint::nil)
                                        (Some AST.Tint) cc_default)).

Notation LOCK_SIG := (mksignature (AST.Tint::nil) (Some AST.Tint) cc_default).
Notation LOCK := (EF_external "LOCK" LOCK_SIG).
Notation UNLOCK_SIG := (mksignature (AST.Tint::nil) (Some AST.Tint) cc_default).
Notation UNLOCK := (EF_external "UNLOCK" UNLOCK_SIG).

Require Import concurrency.permissions.

Module ThreadPool (SEM:Semantics) <: ThreadPoolSig
    with Module TID:= NatTID with Module SEM:=SEM.

  Module TID:=NatTID.
  Module SEM:=SEM.
  Import TID SEM.
  
  Notation code:=C.
  Definition res := access_map.
  Definition LockPool := access_map.
  
  Record t' := mk
                 { num_threads : pos
                   ; pool :> 'I_num_threads -> @ctl code
                   ; perm_maps : 'I_num_threads -> res
                 }.
  
  Definition t := t'.

  Lemma contains0 :
    forall (n : pos), 0 < n.
  Proof.
    intros; destruct n; simpl; by apply/ltP.
  Qed.
  
  Definition lpool (tp : t) :=
    (perm_maps tp) (Ordinal (contains0 (num_threads tp))).

  Definition containsThread (tp : t) (i : NatTID.tid) : Prop:=
    i < num_threads tp.

  Definition getThreadC {i tp} (cnt: containsThread tp i) : ctl :=
    tp (Ordinal cnt).
  
  Definition getThreadR {i tp} (cnt: containsThread tp i) : res :=
    (perm_maps tp) (Ordinal cnt).

  Definition addThread (tp : t) (c : code) (pmap : res) : t :=
    let: new_num_threads := pos_incr (num_threads tp) in
    let: new_tid := ordinal_pos_incr (num_threads tp) in
    mk new_num_threads
        (fun (n : 'I_new_num_threads) => 
           match unlift new_tid n with
           | None => Kresume c (*Could be a new state Kinit?? *)
           | Some n' => tp n'
           end)
        (fun (n : 'I_new_num_threads) => 
           match unlift new_tid n with
           | None => pmap
           | Some n' => (perm_maps tp) n'
           end).
  
  Definition updThreadC {tid tp} (cnt: containsThread tp tid) (c' : ctl) : t :=
    mk (num_threads tp)
       (fun n => if n == (Ordinal cnt) then c' else (pool tp)  n)
       (perm_maps tp).

  Definition updThreadR {tid tp} (cnt: containsThread tp tid)
             (pmap' : res) : t :=
    mk (num_threads tp) (pool tp)
       (fun n =>
          if n == (Ordinal cnt) then pmap' else (perm_maps tp) n).

  Definition updThread {tid tp} (cnt: containsThread tp tid) (c' : ctl)
             (pmap : res) : t :=
    mk (num_threads tp)
       (fun n =>
          if n == (Ordinal cnt) then c' else tp n)
       (fun n =>
          if n == (Ordinal cnt) then pmap else (perm_maps tp) n).

  (*Proof Irrelevance of contains*)
  Lemma cnt_irr: forall t tid
                   (cnt1 cnt2: containsThread t tid),
      cnt1 = cnt2.
  Proof. intros. apply proof_irrelevance. Qed.
  
  (* Update properties*)
  Lemma numUpdateC :
    forall {tid tp} (cnt: containsThread tp tid) c,
      num_threads tp =  num_threads (updThreadC cnt c). 
  Proof.
    intros tid tp cnt c.
    destruct tp; simpl; reflexivity.
  Qed.
  
  Lemma cntUpdateC :
    forall {tid tid0 tp} c
      (cnt: containsThread tp tid),
      containsThread tp tid0 ->
      containsThread (updThreadC cnt c) tid0. 
  Proof.
    intros tid tp.
    unfold containsThread; intros.
    rewrite <- numUpdateC; assumption.
  Qed.
  Lemma cntUpdateC':
    forall {tid tid0 tp} c
      (cnt: containsThread tp tid),
      containsThread (updThreadC cnt c) tid0 ->
      containsThread tp tid0. 
  Proof.
    intros tid tp.
    unfold containsThread; intros.
    rewrite <- numUpdateC in H; assumption.
  Qed.

  Lemma getThreadUpdateC1:
    forall {tid tp} c
      (cnt: containsThread tp tid)
      (cnt': containsThread (updThreadC cnt c) tid),
      getThreadC cnt' = c.
  Proof.
    intros. destruct tp. simpl.
    rewrite (cnt_irr cnt cnt') eq_refl; reflexivity.
  Qed.
  
  Lemma getThreadUpdateC2:
    forall {tid tid0 tp} c
      (cnt1: containsThread tp tid)
      (cnt2: containsThread tp tid0)
      (cnt3: containsThread (updThreadC cnt1 c) tid0),
      tid <> tid0 ->
      getThreadC cnt2 = getThreadC cnt3.
  Proof.
    intros. destruct tp. simpl.
    (*Could use ssreflect better here: *)
    destruct (@eqP _ (Ordinal (n:=num_threads0) (m:=tid1) cnt3) (Ordinal (n:=num_threads0) (m:=tid0) cnt1)).
    inversion e. exfalso; apply H; symmetry; eassumption.
    rewrite (cnt_irr cnt2 cnt3); reflexivity.
  Qed.
        

  (*GetThread Properties*)  
  Lemma gssThreadCode {tid tp} (cnt: containsThread tp tid) c' p'
        (cnt': containsThread (updThread cnt c' p') tid) :
    getThreadC cnt' = c'.
  Proof.
    simpl. rewrite if_true; auto.
    unfold updThread, containsThread in *. simpl in *.
    apply/eqP. apply f_equal.
    apply proof_irr.
  Qed.

  Lemma gssThreadRes {tid tp} (cnt: containsThread tp tid) c' p'
        (cnt': containsThread (updThread cnt c' p') tid) :
    getThreadR cnt' = p'.
  Proof.
    simpl. rewrite if_true; auto.
    unfold updThread, containsThread in *. simpl in *.
    apply/eqP. apply f_equal.
    apply proof_irr.
  Qed.

  Lemma gsoThreadRes {i j tp} (cnti: containsThread tp i)
        (cntj: containsThread tp j) (Hneq: i <> j) c' p'
        (cntj': containsThread (updThread cnti c' p') j) :
    getThreadR cntj' = getThreadR cntj.
  Proof.
    simpl.
    erewrite if_false
      by (apply/eqP; intros Hcontra; inversion Hcontra; by auto).
    unfold updThread in cntj'. unfold containsThread in *. simpl in *.
    unfold getThreadR. do 2 apply f_equal. apply proof_irr.
  Qed.

  Lemma gssThreadCC {tid tp} (cnt: containsThread tp tid) c'
        (cnt': containsThread (updThreadC cnt c') tid) :
    getThreadC cnt' = c'.
  Proof.
    simpl. rewrite if_true; auto.
    unfold updThreadC, containsThread in *. simpl in *.
    apply/eqP. apply f_equal.
    apply proof_irr.
  Qed.

  Lemma gThreadCR {i j tp} (cnti: containsThread tp i)
        (cntj: containsThread tp j) c'
        (cntj': containsThread (updThreadC cnti c') j) :
    getThreadR cntj' = getThreadR cntj.
  Proof.
    simpl.
    unfold getThreadR. 
    unfold updThreadC, containsThread in *. simpl in *.
    do 2 apply f_equal.
    apply proof_irr.
  Qed.
  
End ThreadPool.


Module Concur.
  (* Module Type DrySemantics. *)
  (*   Parameter G: Type. *)
  (*   Parameter C: Type. *)
  (*   Definition M: Type:= mem. *)
  (*   Parameter Sem: CoreSemantics G C M. *)
  (* End DrySemantics. *)

  
  Module mySchedule := ListScheduler NatTID.

  Module DryMachineShell (SEM:Semantics)  <: ConcurrentMachineSig
      with Module ThreadPool.TID:=mySchedule.TID
      with Module ThreadPool.SEM:= SEM.
                                    
    Module ThreadPool := ThreadPool SEM.
    Import ThreadPool.
    Import ThreadPool.SEM.
    Notation tid := NatTID.tid.  

    
    (** Memories*)
    Definition richMem: Type:= M.
    Definition dryMem: richMem -> M:= id.
    Definition diluteMem: M -> M := setMaxPerm.
    
    Notation thread_pool := (ThreadPool.t).
    Notation perm_map := ThreadPool.res.
    
    Definition lp_id := 0.
    
    (** The state respects the memory*)
    Definition mem_compatible tp m : Prop :=
      forall {tid} (cnt: containsThread tp tid),
        permMapLt (getThreadR cnt) (getMaxPerm m).

    (** Per-thread disjointness definition*)
    Definition race_free (tp : thread_pool) :=
      forall i j (cnti : containsThread tp i)
        (cntj : containsThread tp j) (Hneq: i <> j),
        permMapsDisjoint (getThreadR cnti)
                         (getThreadR cntj).

    Record invariant' tp :=
      { no_race : race_free tp;
        lock_pool : forall (cnt : containsThread tp 0), exists c,
              getThreadC cnt = Krun c /\
              halted Sem c
      }.

    Definition invariant := invariant'.
  
    (** Steps*)
    Inductive dry_step genv {tid0 tp m} (cnt: containsThread tp tid0)
              (Hcompatible: mem_compatible tp m) : thread_pool -> mem  -> Prop :=
    | step_dry :
        forall (tp':thread_pool) c m1 m' (c' : code),
        forall (Hrestrict_pmap:
             restrPermMap (Hcompatible tid0 cnt) = m1)
          (Hinv : invariant tp)
          (Hcode: getThreadC cnt = Krun c)
          (Hcorestep: corestep Sem genv c m1 c' m')
          (Htp': tp' = updThread cnt (Krun c') (getCurPerm m')),
          dry_step genv cnt Hcompatible tp' m'.

    (*missing lock-ranges*)
    Inductive ext_step genv {tid0 tp m}
              (cnt0:containsThread tp tid0)(Hcompat:mem_compatible tp m):
      thread_pool -> mem -> Prop :=
    | step_lock :
        forall (tp':thread_pool) m1 c c' m' b ofs virtue
          (cnt_lp: containsThread tp lp_id),
        forall
          (Hinv : invariant tp)
          (Hcode: getThreadC cnt0 = Kstop c)
          (Hat_external: at_external Sem c =
                         Some (LOCK, ef_sig LOCK, Vptr b ofs::nil))
          (Hcompatible: mem_compatible tp m)
          (Hrestrict_pmap:
             restrPermMap (Hcompat lp_id cnt_lp) = m1)
          (Hload: Mem.load Mint32 m1 b (Int.intval ofs) = Some (Vint Int.one))
          (Hstore:
             Mem.store Mint32 m1 b (Int.intval ofs) (Vint Int.zero) = Some m')
          (Hat_external:
             after_external Sem (Some (Vint Int.zero)) c = Some c')
          (Htp': tp' = updThread cnt0 (Kresume c')
                                 (computeMap (getThreadR cnt0) virtue)),
          ext_step genv cnt0 Hcompat tp' m' 
                   
    | step_unlock :
        forall  (tp':thread_pool) m1 c c' m' b ofs virtue
           (cnt_lp: containsThread tp lp_id),
        forall
          (Hinv : invariant tp)
          (Hcode: getThreadC cnt0 = Kstop c)
          (Hat_external: at_external Sem c =
                         Some (UNLOCK, ef_sig UNLOCK, Vptr b ofs::nil))
          (Hrestrict_pmap:
             restrPermMap (Hcompat lp_id cnt_lp) = m1)
          (Hload:
             Mem.load Mint32 m1 b (Int.intval ofs) = Some (Vint Int.zero))
          (Hstore:
             Mem.store Mint32 m1 b (Int.intval ofs) (Vint Int.one) = Some m')
          (* what does the return value denote?*)
          (Hat_external: after_external Sem (Some (Vint Int.zero)) c = Some c')
          (Htp': tp' = updThread cnt0 (Kresume c')
                                 (computeMap (getThreadR cnt0) virtue)),
          ext_step genv cnt0 Hcompat tp' m' 
                   
    | step_create :
        forall  (tp_upd tp':thread_pool) c c' c_new vf arg virtue1 virtue2,
        forall
          (Hinv : invariant tp)
          (Hcode: getThreadC cnt0 = Kstop c)
          (Hat_external: at_external Sem c =
                         Some (CREATE, ef_sig CREATE, vf::arg::nil))
          (Hinitial: initial_core Sem genv vf (arg::nil) = Some c_new)
          (Hafter_external: after_external Sem
                                           (Some (Vint Int.zero)) c = Some c')
          (Htp_upd: tp_upd = updThread cnt0 (Kresume c')
                                       (computeMap (getThreadR cnt0) virtue1))
          (Htp': tp' = addThread tp_upd c_new
                                 (computeMap empty_map virtue2)),
          ext_step genv cnt0 Hcompat tp' m
                   
    | step_mklock :
        forall  (tp' tp'': thread_pool) m1 c c' m' b ofs pmap_tid' pmap_lp
           (cnt_lp': containsThread tp' lp_id)
           (cnt_lp: containsThread tp lp_id),
          let: pmap_tid := getThreadR cnt0 in
          forall
            (Hinv : invariant tp)
            (Hcode: getThreadC cnt0 = Kstop c)
            (Hat_external: at_external Sem c =
                           Some (MKLOCK, ef_sig MKLOCK, Vptr b ofs::nil))
            (Hrestrict_pmap: restrPermMap
                               (Hcompat tid0 cnt0) = m1)
            (Hstore:
               Mem.store Mint32 m1 b (Int.intval ofs) (Vint Int.zero) = Some m')
            (Hdrop_perm:
               setPerm (Some Nonempty) b (Int.intval ofs) pmap_tid = pmap_tid')
            (Hlp_perm: setPerm (Some Writable)
                               b (Int.intval ofs) (getThreadR cnt_lp) = pmap_lp)
            (Hfter_external: after_external
                               Sem (Some (Vint Int.zero)) c = Some c')
            (Htp': tp' = updThread cnt0 (Kresume c') pmap_tid')
            (Htp'': tp'' = updThreadR cnt_lp' pmap_lp),
            ext_step genv cnt0 Hcompat tp'' m' 
                     
    | step_freelock :
        forall  (tp' tp'': thread_pool) c c' b ofs pmap_lp' virtue
           (cnt_lp': containsThread tp' lp_id)
           (cnt_lp: containsThread tp lp_id),
          let: pmap_lp := getThreadR cnt_lp in
          forall
            (Hinv : invariant tp)
            (Hcode: getThreadC cnt0 = Kstop c)
            (Hat_external: at_external Sem c =
                           Some (FREE_LOCK, ef_sig FREE_LOCK, Vptr b ofs::nil))
            (Hdrop_perm:
               setPerm None b (Int.intval ofs) pmap_lp = pmap_lp')
            (Hat_external:
               after_external Sem (Some (Vint Int.zero)) c = Some c')
            (Htp': tp' = updThread cnt0 (Kresume c')
                                   (computeMap (getThreadR cnt0) virtue))
            (Htp'': tp'' = updThreadR cnt_lp' pmap_lp'),
            ext_step genv cnt0 Hcompat  tp'' m 
                     
    | step_lockfail :
        forall  c b ofs m1
           (cnt_lp: containsThread tp lp_id),
        forall
          (Hinv : invariant tp)
          (Hcode: getThreadC cnt0 = Kstop c)
          (Hat_external: at_external Sem c =
                         Some (LOCK, ef_sig LOCK, Vptr b ofs::nil))
          (Hrestrict_pmap: restrPermMap
                             (Hcompat lp_id cnt_lp) = m1)
          (Hload: Mem.load Mint32 m1 b (Int.intval ofs) = Some (Vint Int.zero)),
          ext_step genv cnt0 Hcompat tp m.
    
    Definition cstep (genv : G): forall {tid0 ms m},
        containsThread ms tid0 -> mem_compatible ms m ->
        thread_pool -> mem -> Prop:=
      @dry_step genv.
    
    Definition conc_call (genv :G) :
      forall {tid0 ms m},
        containsThread ms tid0 -> mem_compatible ms m ->
        thread_pool -> mem -> Prop:=
      @ext_step genv.

    Inductive threadHalted': forall {tid0 ms},
                               containsThread ms tid0 -> Prop:=
    | thread_halted':
        forall tp c tid0
          (cnt: containsThread tp tid0)
          (Hinv: invariant tp)
          (Hcode: getThreadC cnt = Krun c)
          (Hcant: halted Sem c),
          threadHalted' cnt.
    
    Definition threadHalted: forall {tid0 ms},
                               containsThread ms tid0 -> Prop:= @threadHalted'.

    Parameter init_core : G -> val -> list val -> option thread_pool.

    Lemma onePos: (0<1)%coq_nat. auto. Qed.
    Definition two_pos : pos := mkPos NPeano.Nat.lt_0_2.

    Definition compute_init_perm : G -> access_map := fun _ => empty_map. (*Needst to be filled*)
    
    Variable lp_code : code. (*Parameter should be a halted, empty state. *)
    Axiom lp_code_halted: ssrbool.isSome (halted Sem lp_code).
    
    Definition initial_machine genv c  :=
      ThreadPool.mk
        two_pos (*Two threads: a lock pool and the initial thread. *)
        (fun tid => if tid == ord0 then (Krun lp_code) else Kresume c)
        (fun tid => if tid == ord0 then empty_map else compute_init_perm genv).
    
    Definition init_mach (genv:G)(v:val)(args:list val):option thread_pool :=
      match initial_core Sem genv v args with
      | Some c => Some (initial_machine genv c)
      | None => None
      end.
    
End DryMachineShell.

  (* Here I make the core semantics*)
  (*Declare Module SEM:Semantics.
  Module DryMachine:= DryMachineShell SEM.
  Module myCoarseSemantics :=
    CoarseMachine mySchedule DryMachine.
  Module myFineSemantics :=
    FineMachine mySchedule  DryMachine.

  Definition coarse_semantics:=
    myCoarseSemantics.MachineSemantics.
  Definition fine_semantics:=
    myFineSemantics.MachineSemantics.*)
  
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