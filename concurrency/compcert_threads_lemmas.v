Require Import compcert.lib.Axioms.

Add LoadPath "../concurrency" as concurrency.

Require Import sepcomp. Import SepComp.
Require Import sepcomp.semantics_lemmas.

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
Require Import compcert.common.Events.
Require Import compcert.lib.Integers.

Require Import Coq.ZArith.ZArith.

Notation EXIT := 
  (EF_external 1%positive (mksignature (AST.Tint::nil) None)). 

Notation CREATE_SIG := (mksignature (AST.Tint::AST.Tint::nil) (Some AST.Tint)).
Notation CREATE := (EF_external 2%positive CREATE_SIG).

Notation READ := 
  (EF_external 3%positive 
  (mksignature (AST.Tint::AST.Tint::AST.Tint::nil) (Some AST.Tint))).
Notation WRITE := 
  (EF_external 4%positive 
  (mksignature (AST.Tint::AST.Tint::AST.Tint::nil) (Some AST.Tint))).

Notation MKLOCK := 
  (EF_external 5%positive (mksignature (AST.Tint::nil) (Some AST.Tint))).
Notation FREE_LOCK := 
  (EF_external 6%positive (mksignature (AST.Tint::nil) (Some AST.Tint))).

Notation LOCK_SIG := (mksignature (AST.Tint::nil) (Some AST.Tint)).
Notation LOCK := (EF_external 7%positive LOCK_SIG).
Notation UNLOCK_SIG := (mksignature (AST.Tint::nil) (Some AST.Tint)).
Notation UNLOCK := (EF_external 8%positive UNLOCK_SIG).

Require Import concurrency.dry_machine.
Require Import concurrency.threads_lemmas.
Require Import concurrency.permissions.
Require Import concurrency.concurrent_machine.

Import Concur.
(** Assuming some threadwise semantics *)
Declare Module SEM:Semantics.
Module DryMachine:= DryMachineShell SEM.
Module myCoarseSemantics :=
  CoarseMachine mySchedule DryMachine.
Module myFineSemantics :=
  FineMachine mySchedule  DryMachine.

Variable initU: mySchedule.schedule.
Definition coarse_semantics:=
  myCoarseSemantics.MachineSemantics initU.

Definition fine_semantics:=
  myFineSemantics.MachineSemantics initU.


(* TODO: - Partial injectiveness (for fresh blocks)

         - Well-defined memories

         - Remove admits.

         - Integrate new changes on threadpool.

         - More comments explaining proofs, especially simulations.

         - More automation (hint databases, type classes for internal
           execution, etc.
         
         - The offset in renamings is annoying, consider if we want to keep it
 *)

Module ThreadPoolWF.
  Import DryMachine ThreadPool.
  
   Lemma unlift_m_inv :
      forall tp tid (Htid : tid < (num_threads tp).+1) ord
        (Hunlift: unlift (ordinal_pos_incr (num_threads tp))
                         (Ordinal (n:=(num_threads tp).+1)
                                  (m:=tid) Htid)=Some ord),
        nat_of_ord ord = tid.
    Proof.
      intros.
      assert (Hcontra: unlift_spec (ordinal_pos_incr (num_threads tp))
                                   (Ordinal (n:=(num_threads tp).+1)
                                            (m:=tid) Htid) (Some ord)).
      rewrite <- Hunlift.
      apply/unliftP.
      inversion Hcontra; subst.
      inversion H0.
      unfold bump.
      assert (pf: ord < (num_threads tp))
        by (by rewrite ltn_ord).
      assert (H: (num_threads tp) <= ord = false).
      rewrite ltnNge in pf.
      rewrite <- Bool.negb_true_iff. auto.
      rewrite H. simpl. rewrite add0n. reflexivity.
    Defined.

    (** Well-formed predicate on new permission map*)
    Definition newPermMap_wf tp pmap :=
      forall i (cnt : containsThread tp i),
        permMapsDisjoint (getThreadR cnt) pmap.

    Definition permMap_wf tp pmap i :=
      forall j (cntj : containsThread tp j) (Hneq: i <> j),
        permMapsDisjoint (getThreadR cntj) pmap.
    
    Opaque pos_incr.
    Lemma addThread_racefree :
      forall tp c p (Hwf: newPermMap_wf tp p) (Hrace: race_free tp),
        race_free (addThread tp c p).
    Proof.
      unfold race_free in *. intros.
      simpl.
      match goal with
      | [ |- context[ match ?Expr with _ => _ end]] =>
        destruct Expr as [ordi|] eqn:Hgeti
      end;
        match goal with
        | [ |- context[ match ?Expr with _ => _ end]] =>
          destruct Expr as [ordj|] eqn:Hgetj
        end.
      unfold containsThread in *; simpl in *.
      - unfold getThreadR in Hrace.
        apply unlift_m_inv in Hgeti.
        apply unlift_m_inv in Hgetj.
        destruct ordi as [i' pfi], ordj as [j' pfj]; subst.
        simpl in *.
        eapply Hrace; eauto.
      - apply unlift_m_inv in Hgeti.
        subst. unfold newPermMap_wf in Hwf.
        destruct ordi. eapply Hwf; eauto.
      - apply unlift_m_inv in Hgetj.
        subst. unfold newPermMap_wf in Hwf.
        destruct ordj. apply permMapsDisjoint_comm. eapply Hwf; eauto.
      - destruct (i == (num_threads tp)) eqn:Heqi.
        + move/eqP:Heqi=>Heqi. subst.
          assert (Hcontra: (ordinal_pos_incr (num_threads tp))
                             != (Ordinal (n:=(num_threads tp).+1) (m:=j) cntj)).
          { apply/eqP. intros Hcontra.
            unfold ordinal_pos_incr in Hcontra.
            inversion Hcontra; auto.
          }
          exfalso. apply unlift_some in Hcontra. rewrite Hgetj in Hcontra.
          destruct Hcontra. discriminate.
        + move/eqP:Heqi=>Heqi.
          assert (
              Hcontra: (ordinal_pos_incr (num_threads tp))
                         !=
                         (Ordinal (n:=(num_threads tp).+1) (m:=i) cnti)).
          { apply/eqP. intros Hcontra.
            unfold ordinal_pos_incr in Hcontra. inversion Hcontra. subst. auto. }
          exfalso. apply unlift_some in Hcontra.
          rewrite Hgeti in Hcontra. destruct Hcontra.
          discriminate.
    Defined.

    Lemma updThread_wf : forall tp tid (pf : containsThread tp tid) pmap
                           (Hwf: permMap_wf tp pmap tid)
                           c'
                           (Hrace_free: race_free tp),
        race_free (updThread pf c' pmap).
    Proof.
      intros.
      unfold race_free. intros.
      simpl.
      destruct (Ordinal (n:=num_threads tp) (m:=i) cnti ==
                Ordinal (n:=num_threads tp) (m:=tid) pf) eqn:Heqi;
        destruct (Ordinal (n:=num_threads tp) (m:=j) cntj ==
                  Ordinal (n:=num_threads tp) (m:=tid) pf) eqn:Heqj.
      - move/eqP:Heqi => Heqi. subst.
        move/eqP:Heqj => Heqj. inversion Heqj. inversion Heqi; subst. exfalso; auto.
      - move/eqP:Heqi=>Heqi. inversion Heqi. subst. 
        apply permMapsDisjoint_comm.
        eapply Hwf. simpl; auto.
      - move/eqP:Heqj=>Heqj. inversion Heqj. subst.
        eapply Hwf. simpl; auto.
      - simpl in *. eapply Hrace_free; eauto.
    Defined.

    Lemma restrPermMap_wf :
      forall tp (m m': mem) tid (cnt: containsThread tp tid)
        (Hcompatible: mem_compatible tp m)
        (Hrestrict: restrPermMap (Hcompatible tid cnt) = m')
        (Hrace : race_free tp),
        permMap_wf tp (getCurPerm m') tid.
    Proof.
      intros. subst.
      unfold restrPermMap, getCurPerm. simpl.
      unfold permMap_wf. intros tid' Htid' Hneq.
      unfold permMapsDisjoint. simpl.
      assert (Hneq' : tid' <> tid) by auto.
      specialize (Hrace tid' tid Htid' cnt Hneq').
      unfold permMapsDisjoint in Hrace.
      assert (Hcanonical:= canonical_lt (Hcompatible tid cnt)).
      assert (Hcan_mem := Max_isCanonical m).
      unfold isCanonical in Hcan_mem.
      unfold getMaxPerm in Hcan_mem. simpl in Hcan_mem.
      intros b ofs. specialize (Hrace b ofs).
      rewrite Maps.PMap.gmap.
      unfold getThreadR in *.
      unfold Maps.PMap.get in *. simpl.
      unfold isCanonical in Hcanonical. rewrite Hcanonical in Hrace.
      rewrite Maps.PTree.gmap. unfold Coqlib.option_map.
      destruct (Maps.PTree.get b (Mem.mem_access m).2) eqn:?;
               destruct (Maps.PTree.get b
                                        (perm_maps tp (Ordinal cnt)).2) eqn:?;
               try rewrite Hcanonical; auto.
      destruct (Maps.PTree.get b
                               (perm_maps tp (Ordinal Htid')).2) eqn:?; auto.
      unfold mem_compatible, permMapLt in Hcompatible.
      unfold Maps.PMap.get in Hcompatible.
      specialize (Hcompatible tid cnt b ofs).
      rewrite Heqo0 in Hcompatible.
      unfold getMaxPerm in Hcompatible. simpl in Hcompatible.
      rewrite Maps.PTree.gmap1 in Hcompatible.
      unfold Coqlib.option_map in Hcompatible.
      rewrite Heqo in Hcompatible.
      apply equal_f with (x := ofs) in Hcan_mem.
      rewrite Hcan_mem in Hcompatible.
      unfold Mem.perm_order'' in Hcompatible. destruct (o ofs); auto.
      exfalso. auto.
      rewrite perm_union_comm. apply not_racy_union. constructor.
    Defined.

    Lemma no_race_wf :
      forall tp tid (pf: containsThread tp tid) (Hrace: race_free tp),
        permMap_wf tp (getThreadR pf) tid.
    Proof.
      intros. unfold race_free, permMap_wf, getThreadR in *; auto.
    Defined.
End ThreadPoolWF.

Global Notation "a # b" := (Maps.PMap.get b a) (at level 1).
(** ** Injections between memories *)
Module MemObsEq.

  Import DryMachine. 
  Import SEM. 

  (* A compcert injection would not work because it allows permissions to go up *)
  (* Moreover, we require that undefined values are matched by the target memory,
     unlike compcert injections *)
  (* Things we may need: the mapped block is valid, the mapping is one-to-one. *)

  
  (** Weak injection between memories *)
  Record weak_mem_obs_eq (f : meminj) (mc mf : M) :=
    {
      domain_invalid: forall b, ~(Mem.valid_block mc b) -> f b = None;
      domain_valid: forall b, Mem.valid_block mc b -> exists b', f b = Some (b',0%Z);
      codomain_valid: forall b1 b2, f b1 = Some (b2,0%Z) -> Mem.valid_block mf b2;
      perm_obs_weak :
        forall b1 b2 ofs (Hrenaming: f b1 = Some (b2,0%Z)),
          Mem.perm_order''
            (permission_at mc b1 ofs Cur)
            (permission_at mf b2 ofs Cur)}.

  (** Strong injections on values *)
  Inductive val_obs (mi : meminj) : val -> val -> Prop :=
    obs_int : forall i : int, val_obs mi (Vint i) (Vint i)
  | obs_long : forall i : int64, val_obs mi (Vlong i) (Vlong i)
  | obs_float : forall f : Floats.float,
      val_obs mi (Vfloat f) (Vfloat f)
  | obs_single : forall f : Floats.float32,
      val_obs mi (Vsingle f) (Vsingle f)
  | obs_ptr : forall (b1 b2 : block) (ofs : int),
      mi b1 = Some (b2,0%Z) ->
      val_obs mi (Vptr b1 ofs) (Vptr b2 ofs)
  | obs_undef : val_obs mi Vundef Vundef.

  Inductive memval_obs_eq (f : meminj) : memval -> memval -> Prop :=
  | memval_obs_byte : forall n : byte,
      memval_obs_eq f (Byte n) (Byte n)
  | memval_obs_frag : forall (v1 v2 : val) (q : quantity) (n : nat)
                        (Hval_obs: val_obs f v1 v2),
      memval_obs_eq f (Fragment v1 q n) (Fragment v2 q n)
  | memval_obs_undef : memval_obs_eq f Undef Undef.
  
  (** Strong injection between memories *)
  Record mem_obs_eq (f : meminj) (mc mf : M) :=
    {
      weak_obs_eq : weak_mem_obs_eq f mc mf;
      perm_obs_strong :
        forall b1 b2 ofs (Hrenaming: f b1 = Some (b2,0%Z)),
          Mem.perm_order''
            (permission_at mf b2 ofs Cur)
            (permission_at mc b1 ofs Cur);
      val_obs_eq :
        forall b1 b2 ofs (Hrenaming: f b1 = Some (b2,0%Z))
          (Hperm: Mem.perm mc b1 ofs Cur Readable),
          memval_obs_eq f (Maps.ZMap.get ofs mc.(Mem.mem_contents)#b1)
                        (Maps.ZMap.get ofs mf.(Mem.mem_contents)#b2)}.
  
End MemObsEq.

Module CoreLanguage.

  Import MemObsEq DryMachine ThreadPool SEM ThreadPoolWF.
  Variable the_ge : SEM.G.
  (** Assumptions on thread's corestep (e.g PPC semantics) *)
    Class corestepSpec :=
      { corestep_det: corestep_fun Sem;
        corestep_unchanged_on:
          forall the_ge c m c' m' b ofs
            (Hstep: corestep Sem the_ge c m c' m')
            (Hstable: ~ Mem.perm m b ofs Cur Writable),
            Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m)) =
            Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m'));
        corestep_obs_eq:
          forall cc cc' mc mf mc' f
            (Hobs_eq: mem_obs_eq f mc mf)
            (Hstep: corestep Sem the_ge cc mc cc' mc'),
          exists mf' f',
            corestep Sem the_ge cc mf cc' mf'
            /\ mem_obs_eq f' mc' mf'
            /\ inject_incr f f'
            /\ inject_separated f f' mc mf
            /\ (forall b1 b1' b2,
                  f b1 = None ->
                  f b1' = None ->
                  f' b1 = Some (b2,0%Z) ->
                  f' b1' = Some (b2,0%Z) ->
                  b1 = b1')
            /\ (exists g, forall b2, Mem.valid_block mf' b2 ->
                          ~ Mem.valid_block mf b2 ->
                          exists b1, g b2 = Some (b1,0%Z)
                                /\ f' b1 = Some (b2,0%Z)
                                /\ f b1 = None);
        corestep_decay:
          forall c c' m m',
            corestep Sem the_ge c m c' m' ->
            decay m m';
        corestep_nextblock:
          forall c m c' m',
            corestep Sem the_ge c m c' m' ->
            forall b, Mem.valid_block m b ->
                 Mem.valid_block m' b
      }.

    Ltac pf_cleanup :=
      repeat match goal with
             | [H1: invariant ?X, H2: invariant ?X |- _] =>
               assert (H1 = H2) by (by eapply proof_irr);
                 subst H2
             | [H1: mem_compatible ?TP ?M, H2: mem_compatible ?TP ?M |- _] =>
               assert (H1 = H2) by (by eapply proof_irr);
                 subst H2
             | [H1: is_true (leq ?X ?Y), H2: is_true (leq ?X ?Y) |- _] =>
               assert (H1 = H2) by (by eapply proof_irr); subst H2
             | [H1: containsThread ?TP ?M, H2: containsThread ?TP ?M |- _] =>
               assert (H1 = H2) by (by eapply proof_irr); subst H2
             | [H1: containsThread ?TP ?M,
                    H2: containsThread (@updThread _ ?TP _ _ _) ?M |- _] =>
               unfold containsThread in H1, H2; unfold updThread in H2;
               simpl in H2;
               assert (H1 = H2) by (by eapply proof_irr); subst H2
             | [H1: containsThread ?TP ?M,
                    H2: containsThread (@updThreadC _ ?TP _ _) ?M |- _] =>
               unfold containsThread in H1, H2; unfold updThreadC in H2;
               simpl in H2;
               assert (H1 = H2) by (by eapply proof_irr); subst H2
             | [H1: containsThread ?TP ?M,
                    H2: containsThread (@updThread _ ?TP _ _ _) ?M |- _] =>
               unfold containsThread in H1, H2; unfold updThread in H2;
               simpl in H2;
               assert (H1 = H2) by (by eapply proof_irr); subst H2
             end.
        
    (** ** Lemmas about coresteps *)

    Context {cspec : corestepSpec}.

    (* TODO: These proofs break the opaquness of the modules, they
    should be redone in an opaque way *)

    (** Lemmas about containsThread and coresteps *)
    Lemma corestep_containsThread:
      forall (tp : thread_pool) c c' m m' p (i j : tid)
        (Hcnti : containsThread tp i)
        (Hcntj: containsThread tp j)
        (Hcorestep: corestep Sem the_ge c m c' m')
        (Hcode: getThreadC Hcnti = Krun c),
        containsThread (updThread Hcnti (Krun c') p) j.
    Proof.
      intros.
        by eapply cntUpdate.
    Qed.

    Lemma corestep_containsThread':
      forall (tp : thread_pool) c c' m m' p (i j : tid)
        (Hcnti : containsThread tp i)
        (Hcntj : containsThread (updThread Hcnti (Krun c') p) j)
        (Hcorestep: corestep Sem the_ge c m c' m')
        (Hcode: getThreadC Hcnti = Krun c),
        containsThread tp j.
    Proof.
      intros.
        by eapply cntUpdate'; eauto.
    Qed.

    (** Lemmas about invariants maintaned by coresteps*)
    
    Lemma corestep_compatible:
      forall (tp : thread_pool) (m m' : mem) (i : nat)
        (pf : containsThread tp i) (c c': code)
        (Hinv: invariant tp)
        (Hcode: getThreadC pf = Krun c)
        (Hcompatible : mem_compatible tp m)
        (Hcorestep: corestep SEM.Sem the_ge c (restrPermMap (Hcompatible i pf)) c' m'),
        mem_compatible (updThread pf (Krun c') (getCurPerm m')) m'.
    Proof.
      intros.
      unfold mem_compatible, updThread, permMapLt. simpl.
      intros tid cnt b ofs. 
      match goal with
      | [ |- context[if ?Expr then _ else _]] =>
        destruct Expr eqn:Htid
      end; [apply getCur_Max|].
      move/eqP:Htid=>Htid.
      assert (Hneq: tid <> i)
        by (unfold containsThread in *; simpl in *;
            intros Hcontra; subst; pf_cleanup; by auto ).
      assert (Hlt := Hcompatible tid cnt b ofs).
      unfold getThreadR in Hlt.
      eapply corestep_decay in Hcorestep.
      apply decay_decay' in Hcorestep.
      destruct (valid_block_dec (restrPermMap (Hcompatible i pf)) b)
        as [Hvalid|Hinvalid].
      - unfold decay' in Hcorestep.
        destruct (Hcorestep b ofs) as [ _ Hdecay].
        destruct (Hdecay Hvalid) as [Hfreed | Heq]; clear Hdecay.
        + destruct Hfreed as [HFree Hdrop].
          assert (Hempty: (perm_maps tp (Ordinal (n:=num_threads tp) (m:=tid) cnt))
                            # b ofs = None).
          { assert (Hp := restrPermMap_Cur (Hcompatible i pf) b ofs).
            unfold permission_at in Hp. rewrite Hp in HFree.
            assert (Hno_race := no_race Hinv).
            unfold race_free in Hno_race.
            specialize (Hno_race _ _ cnt pf Hneq).
            unfold permMapsDisjoint in Hno_race.
            specialize (Hno_race b ofs).
            assert (Hnot_racy : not_racy ((getThreadR cnt) # b ofs)).
            rewrite gsoThreadRes; auto.
            rewrite perm_union_comm in Hno_race.
            eapply no_race_racy with (p1 := (getThreadR pf) # b ofs); eauto.
            rewrite HFree. constructor.
            rewrite gsoThreadRes in Hnot_racy; auto.
            inversion Hnot_racy. unfold getThreadR in *. auto.
          }
          rewrite Hempty.
          destruct ((getMaxPerm m') # b ofs); simpl; auto.
        + rewrite getMaxPerm_correct. unfold permission_at.
          admit. (*need lennart's new lemma *)
      - apply Mem.nextblock_noaccess with (ofs := ofs) (k := Max) in Hinvalid.
        assert (Hp := restrPermMap_Max (Hcompatible i pf) b ofs).
        unfold permission_at in Hp. rewrite Hp in Hinvalid.
        rewrite Hinvalid in Hlt.
        simpl in Hlt.
        destruct ((perm_maps tp (Ordinal (n:=num_threads tp) (m:=tid) cnt)) # b ofs);
          [by exfalso| destruct ((getMaxPerm m') # b ofs); simpl; by auto].
    Qed.

    Lemma corestep_permMap_wf :
      forall (tp : thread_pool) i
        c m c' m'
        (Hlt: forall j (cnt: containsThread tp j),
            permMapLt (getThreadR cnt) (getMaxPerm m))
        (Hperm: permMap_wf tp (getCurPerm m) i)
        (Hcore: corestep Sem the_ge c m c' m'),
        permMap_wf tp (getCurPerm m') i.
    Proof.
      intros.
      unfold permMap_wf in *. intros.
      specialize (Hperm _ cntj Hneq).
      unfold permMapsDisjoint in *. intros b ofs.
      specialize (Hperm b ofs).
      assert (Hdecay := corestep_decay _ _ _ _ Hcore).
      apply decay_decay' in Hdecay.
      unfold decay' in Hdecay.
      destruct (Hdecay b ofs) as [_ Hold].
      clear Hdecay.
      destruct (valid_block_dec m b) as [Hvalid | Hinvalid].
      - destruct (Hold Hvalid) as [Hfree | Heq].
        + destruct Hfree as [_ Hm']. rewrite getCurPerm_correct.
          assert (not_racy (permission_at m' b ofs Cur))
            by (unfold permission_at; rewrite Hm'; constructor).
          rewrite perm_union_comm. by eapply not_racy_union.
        + rewrite getCurPerm_correct. unfold permission_at.
          rewrite <- Heq. rewrite getCurPerm_correct in Hperm.
          unfold permission_at in Hperm. assumption.
      - assert (Hnone: ((getThreadR cntj) # b ofs) = None).
        { apply Mem.nextblock_noaccess with (ofs := ofs) (k := Max) in Hinvalid.
          unfold permMapLt in Hlt.
          specialize (Hlt j cntj b ofs).
          rewrite getMaxPerm_correct in Hlt.
          unfold permission_at in Hlt.
          rewrite Hinvalid in Hlt. simpl in Hlt.
          destruct ((getThreadR cntj) # b ofs); tauto.
        }
        rewrite Hnone. eapply not_racy_union. constructor.
    Qed.

    Lemma corestep_invariant:
      forall (tp : thread_pool) m (i : nat)
        (pf : containsThread tp i) c m1 m1' c'
        (Hinv: invariant tp)
        (Hcompatible: mem_compatible tp m)
        (Hrestrict_pmap :restrPermMap (Hcompatible i pf) = m1)
        (Hcorestep: corestep SEM.Sem the_ge c m1 c' m1')
        (Hcode: getThreadC pf = Krun c),
        invariant (updThread pf (Krun c') (getCurPerm m1')).
    Proof.
      intros.
      destruct Hinv as [Hrace Hlp].
      constructor.
      { unfold race_free in *.
        intros j k.
        destruct (i == j) eqn:Heqj, (i == k) eqn:Heqk; move/eqP:Heqj=>Heqj;
          move/eqP:Heqk=>Heqk; simpl in *; intros cntj cntk Hneq.
        - subst j k; exfalso; auto.
        - subst j.
          erewrite if_true
            by (pf_cleanup; apply eq_refl).
          erewrite if_false by
              (apply/eqP; intro Hcontra'; inversion Hcontra'; auto).
          assert (Hwf := no_race_wf pf Hrace).
          assert (Hwf_m1 : permMap_wf tp (getCurPerm m1) i)
            by (apply restrPermMap_wf in Hrestrict_pmap; auto).
          assert (Hwf': permMap_wf tp (getCurPerm m1') i).
          { eapply @corestep_permMap_wf with (m := m1); eauto.
            unfold mem_compatible in Hcompatible.
            subst m1.
            unfold permMapLt. intros j cnt b ofs.
            rewrite getMaxPerm_correct.
            assert (Hmax := restrPermMap_Max (Hcompatible _ pf) b ofs).
            rewrite Hmax. clear -Hcompatible. specialize (Hcompatible _ cnt).
            specialize (Hcompatible b ofs). assumption.
          }
          unfold permMap_wf in Hwf'.
          specialize (Hwf' _ cntk Hneq).
          apply permMapsDisjoint_comm. assumption.
        - subst k; simpl in *.
          erewrite if_false by
              (apply/eqP; intro Hcontra'; inversion Hcontra'; auto).
          erewrite if_true
            by (pf_cleanup; apply eq_refl).
          assert (Hwf := no_race_wf pf Hrace).
          assert (Hwf_m1 : permMap_wf tp (getCurPerm m1) i)
            by (apply restrPermMap_wf in Hrestrict_pmap; auto).
          assert (Hwf': permMap_wf tp (getCurPerm m1') i).
          { eapply corestep_permMap_wf with (m := m1); eauto.
            subst m1. 
            intros k cnt b ofs.
            rewrite getMaxPerm_correct.
            assert (Hmax := restrPermMap_Max (Hcompatible _ pf) b ofs).
            rewrite Hmax. clear -Hcompatible.
            specialize (Hcompatible _ cnt).
            specialize (Hcompatible b ofs). assumption.
          }
          unfold permMap_wf in Hwf'.
          specialize (Hwf' _ cntj Heqj).
          clear - Hwf'.
          unfold permMapsDisjoint, getThreadR in *. intros b ofs.
          specialize (Hwf' b ofs).
          rewrite getCurPerm_correct. rewrite getCurPerm_correct in Hwf'.
            by assumption.
        -
          do 2 erewrite if_false by
              (apply/eqP; intro Hcontra'; inversion Hcontra'; auto).
          eapply Hrace; eauto.
      }
      { assert (Hcontra: i <> 0).
        { intros Hcontra. subst i.
          simpl in *. 
          destruct (Hlp pf) as [c0' [Hcode' Hhalted]].
          rewrite Hcode in Hcode'; inversion Hcode'; subst c0'.
          apply corestep_not_halted in Hcorestep. 
          rewrite Hcorestep in Hhalted. auto.
        }
        simpl. intros pf0. destruct (Hlp pf0) as [c0 [Hcode0 Hhalted]].
        exists c0. split; auto.
        rewrite if_false; auto.
        apply/eqP. intro Hcontra'. inversion Hcontra'; auto.
      }
    Qed.

    Lemma corestep_disjoint_val:
      forall (tp : thread_pool) (m m' : mem) (i j : tid) (Hneq: i <> j)
        (c c' : code) 
        (pfi : containsThread tp i) (pfj : containsThread tp j)
        (Hcomp : mem_compatible tp m) (b : block) (ofs : Z) 
        (Hreadable: Mem.perm (restrPermMap (Hcomp j pfj)) b ofs Cur Readable)
        (Hcorestep: corestep Sem the_ge c (restrPermMap (Hcomp i pfi)) c' m')
        (Hinv: invariant tp),
        Maps.ZMap.get ofs (Mem.mem_contents m) # b =
        Maps.ZMap.get ofs (Mem.mem_contents m') # b.
    Proof.
      intros.
      assert (Hstable: ~ Mem.perm (restrPermMap (Hcomp _ pfi))
                         b ofs Cur Writable).
      { intros Hcontra.
        assert (Hdisjoint := no_race Hinv pfi pfj Hneq).
        assert (Hpermi := restrPermMap_correct (Hcomp _ pfi) b ofs).
        destruct Hpermi as [_ Hpermi].
        assert (Hpermj := restrPermMap_correct (Hcomp _ pfj) b ofs).
        destruct Hpermj as [_ Hpermj].
        unfold permission_at, Mem.perm in *.
        rewrite Hpermi in Hcontra.
        rewrite Hpermj in Hreadable.
        unfold getThreadR, Mem.perm_order' in *.
        clear - Hcontra Hreadable Hdisjoint.
        specialize (Hdisjoint b ofs). destruct Hdisjoint as [pu Hunion].
        destruct ((perm_maps tp (Ordinal (n:=num_threads tp) (m:=i) pfi)) # b ofs);
          try (exfalso; assumption);
          inversion Hcontra; subst; simpl in Hunion;
          destruct ((perm_maps tp (Ordinal (n:=num_threads tp) (m:=j) pfj)) # b ofs);
          try match goal with
              | [H: Some _ = Some _ |- _] => inversion H; subst
              | [H: match ?Expr with _ => _ end = _ |- _] => destruct Expr
              end; try discriminate; inversion Hreadable.
      }
      apply corestep_unchanged_on with (b := b) (ofs := ofs) in Hcorestep; auto.
    Qed.
    
End CoreLanguage.

Module InternalSteps.
  Import Concur DryMachine DryMachine.ThreadPool SEM.
  Import mySchedule.
  Import CoreLanguage ThreadPoolWF.
  

  Section InternalSteps.   
  
  Notation cstep := (cstep the_ge).
  Notation Sch := schedule.
  Context {cSpec : corestepSpec}. 
    

  (** Internal steps are just thread coresteps or resume steps, they
  mimic fine-grained internal steps *)
  Definition internal_step {tid} {tp} m (cnt: containsThread tp tid)
             (Hcomp: mem_compatible tp m) tp' m' :=
    cstep cnt Hcomp tp' m' \/
    (myCoarseSemantics.resume_thread cnt tp' /\ m = m').

  Inductive internal_execution : Sch -> thread_pool -> mem ->
                                 thread_pool -> mem -> Prop :=
  | refl_exec : forall tp m,
      internal_execution empty tp m tp m
  | step_trans : forall tid U U' tp m tp' m' tp'' m''
                   (cnt: containsThread tp tid)
                   (HschedN: schedPeek U = Some tid)
                   (HschedS: schedSkip U = U')
                   (Hcomp: mem_compatible tp m)
                   (Hstep: internal_step cnt Hcomp tp' m')
                   (Htrans: internal_execution U' tp' m' tp'' m''),
      internal_execution U tp m tp'' m''.

  (** Lemmas about internal steps and internal executions *)
  Lemma internal_execution_trans :
    forall i U tp tp' tp'' m m' m'' (pf': containsThread tp' i)
      (Hcomp: mem_compatible tp' m')
      (Hstep: internal_step pf' Hcomp tp'' m'')
      (Hexec: internal_execution U tp m tp' m'),
      internal_execution (U ++ [:: i]) tp m tp'' m''.
  Proof.
    intros i U. induction U; intros.
    simpl in *.
    inversion Hexec; subst.
    econstructor; simpl; eauto. constructor.
    simpl in HschedN. discriminate.
    inversion Hexec. subst. simpl in *.
    econstructor; simpl; eauto.
  Qed.

  Lemma internal_step_det :
    forall tp tp' tp'' m m' m'' i
      (Hcnt: containsThread tp i)
      (Hcomp: mem_compatible tp m)
      (Hstep: internal_step Hcnt Hcomp tp' m')
      (Hstep': internal_step Hcnt Hcomp tp'' m''),
      tp' = tp'' /\ m' = m''.
  Proof.
    intros. destruct Hstep as [Hcore | [Hresume ?]],
                              Hstep' as [Hcore' | [Hresume' ?]]; subst.
    - inversion Hcore; inversion Hcore'.
      unfold corestep_fun in *.
      subst. pf_cleanup.
      rewrite Hcode in Hcode0. inversion Hcode0. subst c0.
      assert (Heq: c' = c'0 /\ m' = m'').
        by (eapply corestep_det; eauto).
        destruct Heq; subst; auto.
    - inversion Hcore; inversion Hresume'; subst.
      unfold getThreadC in *.
      pf_cleanup.
      rewrite Hcode in Hcode0. discriminate.
    - inversion Hresume; inversion Hcore'; subst;
      pf_cleanup. unfold getThreadC in *; rewrite Hcode in Hcode0.
      discriminate.
    - inversion Hresume; inversion Hresume'; subst.
      pf_cleanup. rewrite Hcode in Hcode0; inversion Hcode0; subst.
      auto.
  Qed.

  Lemma containsThread_internal_step :
      forall tp m tp' m' tid0 tid
        (Hcnt0: containsThread tp tid0)
        (Hcomp: mem_compatible tp m)
        (Hstep: internal_step Hcnt0 Hcomp tp' m') 
        (Hcnt: containsThread tp tid),
        containsThread tp' tid.
    Proof.
      intros. inversion Hstep as [Htstep | [Htstep _]];
        inversion Htstep; subst;
        [ eapply corestep_containsThread; by eauto
        | by eapply cntUpdateC].
    Qed.
    
    Lemma containsThread_internal_execution :
      forall U tp m tp' m' i
        (Hexec: internal_execution U tp m tp' m')
        (Hcnt: containsThread tp i),
        containsThread tp' i.
    Proof.
      intros U. induction U. intros.
      inversion Hexec; subst; simpl in *; auto; try discriminate.
      intros.
      inversion Hexec as [|tid0 U0 U0' ? ? tp0' m0' ? ?];
        subst. eapply containsThread_internal_step in Hstep; eauto.
    Qed.

    Lemma containsThread_internal_step' :
      forall tp m tp' m' i j
        (Hcnt0: containsThread tp j)
        (Hcomp: mem_compatible tp m)
        (Hstep: internal_step Hcnt0 Hcomp tp' m') 
        (Hcnt: containsThread tp' i),
        containsThread tp i.
    Proof.
      intros. inversion Hstep as [Htstep | [Htstep _]];
        inversion Htstep; subst;
        [eapply corestep_containsThread'; eauto |
           by eapply cntUpdateC'; eauto].
    Qed.

    Lemma containsThread_internal_execution' :
      forall U tp m tp' m' i
        (Hexec: internal_execution U tp m tp' m')
        (Hcnt: containsThread tp' i),
        containsThread tp i.
    Proof.
      intros U. induction U. intros.
      inversion Hexec; subst; simpl in *; auto; try discriminate.
      intros.
      inversion Hexec as [|tid0 U0 U0' ? ? tp0' m0' ? ?];
        subst. eapply containsThread_internal_step' in Hstep; eauto.
    Qed.

    Lemma dry_step_compatible :
      forall (tp tp' : thread_pool) m m' (i : nat) (pf : containsThread tp i)
        (Hcompatible: mem_compatible tp m)
        (Hdry: dry_step the_ge pf Hcompatible tp' m'),
        mem_compatible tp' m'.
    Proof.
      intros.
      inversion Hdry; subst; eapply corestep_compatible;
        by eauto.
    Qed.
     
    Lemma resume_step_compatible :
      forall (tp tp' : thread_pool) m (i : nat) (pf : containsThread tp i)
        (Hcompatible: mem_compatible tp m)
        (Hresume: myCoarseSemantics.resume_thread pf tp'),
        mem_compatible tp' m.
    Proof.
      intros.
      inversion Hresume; subst.
      unfold mem_compatible.
      intros j cntj'.
      assert (cntj := cntUpdateC' (Krun c) ctn cntj').
      specialize (Hcompatible _ cntj).
      erewrite @gThreadCR with (cntj := cntj).
        by auto.
    Qed.
    
    Corollary internal_step_compatible :
      forall (tp tp' : thread_pool) m m' (i : nat) (pf : containsThread tp i)
        (Hcompatible: mem_compatible tp m)
        (Hstep: internal_step pf Hcompatible tp' m'),
        mem_compatible tp' m'.
    Proof.
      intros.
      destruct Hstep as [Hdry | [Hresume ?]];
        [eapply dry_step_compatible | subst; eapply resume_step_compatible];
        eauto.
    Qed.
    
    Lemma internal_step_invariant:
      forall (tp tp' : thread_pool) m m' (i : nat) (pf : containsThread tp i)
        (Hcompatible: mem_compatible tp m)
        (Hstep: internal_step pf Hcompatible tp' m'),
        invariant tp'.
    Proof.
      intros.
      destruct Hstep as [Hdry | Hresume].
      - inversion Hdry as [tp'0 c m1 m1' c']. subst m' tp'0 tp'.
        eapply corestep_invariant; eauto.
      - destruct Hresume as [Hresume Heq]; subst.
        inversion Hresume; subst.
        inversion Hinv.
        constructor. simpl. auto.
        unfold race_free. simpl. auto.
        simpl. intros. rewrite if_false.
        specialize (lock_pool0 cnt). auto.
        apply/eqP. intros Hcontra.
        inversion Hcontra. subst.
        destruct (lock_pool0 ctn) as [c0 [Hget' ?]].
        rewrite Hget' in Hcode. discriminate.
    Qed.

 Lemma internal_execution_compatible :
      forall (tp tp' : thread_pool) m m' xs
        (Hcompatible: mem_compatible tp m)
        (Hstep: internal_execution xs tp m tp' m'),
        mem_compatible tp' m'.
    Proof.
      intros. induction Hstep. auto. subst.
      eapply IHHstep; eauto.
      eapply internal_step_compatible; eauto.
    Qed.

    Lemma internal_execution_invariant :
      forall (tp tp' : thread_pool) m m' xs
        (Hcompatible: mem_compatible tp m)
        (Hinv: invariant tp)
        (Hstep: internal_execution xs tp m tp' m'),
        invariant tp'.
    Proof.
      intros. induction Hstep. auto. subst.
      eapply IHHstep; eauto.
      eapply internal_step_compatible; eauto.
      eapply internal_step_invariant; eauto.
    Qed.
    
    Lemma gsoThreadC_step:
      forall tp tp' m m' i j (pfi: containsThread tp i)
        (pfj: containsThread tp j)
        (pfj': containsThread tp' j)
        (Hcomp: mem_compatible tp m)
        (Hstep: internal_step pfi Hcomp tp' m')
        (Hneq: i <> j),
        getThreadC pfj = getThreadC pfj'.
    Proof.
      intros. destruct Hstep as [Hstep | [Hstep Heq]];
        inversion Hstep; subst;
        simpl; erewrite if_false
          by (apply/eqP; intros Hcontra; inversion Hcontra; auto);
        pf_cleanup; reflexivity.
    Qed.

    Lemma gsoThreadC_exec:
      forall tp m tp' m' i j xs
        (pfj: containsThread tp j)
        (pfj': containsThread tp' j)
        (Hstep: internal_execution [seq x <- xs | x == i] tp m tp' m')
        (Hneq: i <> j),
        getThreadC pfj = getThreadC pfj'.
    Proof.
      intros. generalize dependent tp. generalize dependent m.
      induction xs; intros.
      - simpl in Hstep. inversion Hstep; subst. by pf_cleanup.
        simpl in HschedN. by discriminate.
      - simpl in Hstep.
        destruct (a == i) eqn:Heq; move/eqP:Heq=>Heq.
        + subst a. inversion Hstep; subst.
          simpl in Htrans.
          assert (pfj'0: containsThread tp'0 j)
            by (eapply containsThread_internal_step; eauto).
          specialize (IHxs _ _  pfj'0 Htrans).
          rewrite <- IHxs.
          erewrite gsoThreadC_step; eauto.
          simpl in HschedN. inversion HschedN; subst.
          assumption.
        + eauto.
    Qed.

    Lemma gsoThreadR_step:
      forall tp tp' m m' i j (pfi: containsThread tp i)
        (pfj: containsThread tp j)
        (pfj': containsThread tp' j)
        (Hcomp: mem_compatible tp m)
        (Hstep: internal_step pfi Hcomp tp' m')
        (Hneq: i <> j),
        getThreadR pfj = getThreadR pfj'.
    Proof.
      intros. destruct Hstep as [Hstep | [Hstep Heq]];
        inversion Hstep; subst;
        [erewrite <- @gsoThreadRes with (cntj' := pfj') |
         erewrite <- @gThreadCR with (cntj' := pfj')];
          by eauto.
    Qed.
    
    Corollary permission_at_step:
      forall tp tp' m m' i j
        (Hneq: i <> j)
        (pfi: containsThread tp i)
        (pfj: containsThread tp j)
        (pfj': containsThread tp' j)
        (Hcomp: mem_compatible tp m)
        (Hcomp': mem_compatible tp' m')
        (Hstep: internal_step pfi Hcomp tp' m') b ofs,
        permission_at (restrPermMap (Hcomp _ pfj)) b ofs Cur =
        permission_at (restrPermMap (Hcomp' _ pfj')) b ofs Cur.
    Proof.
      intros.
      do 2 rewrite restrPermMap_Cur.
      erewrite @gsoThreadR_step;
        by eauto.
    Qed.

    Lemma gsoThreadR_execution:
      forall tp m tp' m' i j xs
        (pfj: containsThread tp j)
        (pfj': containsThread tp' j)
        (Hneq: i <> j)
        (Hstep: internal_execution [seq x <- xs | x == i] tp m tp' m'),
        getThreadR pfj = getThreadR pfj'.
    Proof.
      intros. generalize dependent tp. generalize dependent m.
      induction xs; intros.
      - simpl in Hstep. inversion Hstep; subst. by pf_cleanup.
        simpl in HschedN. by discriminate.
      - simpl in Hstep.
        destruct (a == i) eqn:Heq; move/eqP:Heq=>Heq.
        + subst a. inversion Hstep; subst.
          simpl in Htrans.
          simpl in HschedN; inversion HschedN; subst tid.
          pf_cleanup.
          assert (pfj'0: containsThread tp'0 j)
            by (eapply containsThread_internal_step; eauto).
          specialize (IHxs _ _  pfj'0 Htrans).
          rewrite <- IHxs.
          erewrite gsoThreadR_step; eauto.
        + eauto.
    Qed.
          
    Lemma permission_at_execution:
      forall tp m tp' m' i j xs
        (pfi: containsThread tp i)
        (pfj: containsThread tp j)
        (pfj': containsThread tp' j)
        (Hneq: i <> j)
        (Hcomp: mem_compatible tp m)
        (Hcomp': mem_compatible tp' m')
        (Hstep: internal_execution [seq x <- xs | x == i] tp m tp' m'),
      forall b ofs,
        permission_at (restrPermMap (Hcomp _ pfj)) b ofs Cur =
        permission_at (restrPermMap (Hcomp' _ pfj')) b ofs Cur.
    Proof.
      intros.
      do 2 rewrite restrPermMap_Cur.
      erewrite gsoThreadR_execution; eauto.
    Qed.
  
    Lemma internal_step_disjoint_val :
      forall tp tp' m m' i j
        (Hneq: i <> j)
        (pfi: containsThread tp i)
        (pfj: containsThread tp j)
        (Hcomp: mem_compatible tp m)
        (Hcomp': mem_compatible tp' m')
        (Hstep: internal_step pfi Hcomp tp' m') b ofs
        (Hreadable: 
           Mem.perm (restrPermMap (Hcomp _ pfj)) b ofs Cur Readable),
        Maps.ZMap.get ofs (Mem.mem_contents m) # b =
        Maps.ZMap.get ofs (Mem.mem_contents m') # b.
    Proof.
      intros.
      inversion Hstep as [Hcstep | [Hrstep Heq]]; subst; auto.
      inversion Hcstep; subst; eapply corestep_disjoint_val;
        by eauto.
    Qed.
     
    Lemma internal_exec_disjoint_val :
      forall tp tp' m m' i j xs
        (Hneq: i <> j)
        (pfi: containsThread tp i)
        (pfj: containsThread tp j)
        (Hcomp: mem_compatible tp m)
        (Hstep: internal_execution [seq x <- xs | x == i] tp m tp' m') b ofs
        (Hreadable: 
           Mem.perm (restrPermMap (Hcomp _ pfj)) b ofs Cur Readable),
        Maps.ZMap.get ofs (Mem.mem_contents m) # b =
        Maps.ZMap.get ofs (Mem.mem_contents m') # b.
    Proof.
      intros.
      generalize dependent tp.  generalize dependent m.
      induction xs as [|x xs]; intros.
      - simpl in Hstep; inversion Hstep; subst.
        reflexivity.
        simpl in HschedN. by discriminate.
      - simpl in Hstep.
        destruct (x == i) eqn:Heq; move/eqP:Heq=>Heq.
        + subst x.
          inversion Hstep; subst.
          simpl in Htrans.
          simpl in HschedN.
          inversion HschedN; subst tid.
          pf_cleanup.
          assert (pfj0': containsThread tp'0 j) by
              (eapply containsThread_internal_step; eauto).
          assert (pfi0': containsThread tp'0 i) by
              (eapply containsThread_internal_step; eauto).
          assert(Hcomp0': mem_compatible tp'0 m'0) by
              (eapply internal_step_compatible; eauto).
          assert (Hreadable0':
                    Mem.perm (restrPermMap (Hcomp0' j pfj0')) b ofs Cur Readable).
          { clear IHxs Htrans HschedN Hstep.
            assert (Hperm_eq :=
                      permission_at_step Hneq  pfj pfj0' Hcomp0' Hstep0 b ofs).
            do 2 rewrite restrPermMap_Cur in Hperm_eq.
            unfold Mem.perm in *.
            assert (H1:= restrPermMap_Cur (Hcomp0' j pfj0') b ofs).
            unfold permission_at in H1.
            rewrite H1. rewrite <- Hperm_eq.
            assert (H2:= restrPermMap_Cur (Hcomp j pfj) b ofs).
            unfold permission_at in H2.
            rewrite H2 in Hreadable. assumption.
          }
          specialize (IHxs _ _  pfi0' pfj0' Hcomp0' Htrans Hreadable0').
          rewrite <- IHxs.
          eapply internal_step_disjoint_val; eauto.
        + by eauto.
    Qed.

    Lemma internal_step_decay:
      forall tp m tp' m' i (cnt: containsThread tp i)
        (cnt': containsThread tp' i)
        (Hcomp: mem_compatible tp m)
        (Hcomp': mem_compatible tp' m')
        (Hstep: internal_step cnt Hcomp tp' m'),
        decay (restrPermMap (Hcomp _ cnt))
              (restrPermMap (Hcomp' _ cnt')).
    Proof.
      intros. unfold decay. intros b ofs.
      assert (Hperm: permission_at
                       (restrPermMap (Hcomp' _ cnt')) b ofs Cur =
                     (getThreadR cnt') # b ofs)
        by (eapply restrPermMap_Cur; eauto).
      unfold permission_at in Hperm.
      destruct Hstep as [Hcstep | [Hresume ?]]; subst.
      - inversion Hcstep. subst.
        apply corestep_decay in Hcorestep.
        unfold decay in *. intros.
        specialize (Hcorestep b ofs).
        assert (Hpmap: getThreadR cnt' = getCurPerm m')
          by (by rewrite gssThreadRes).
        unfold Mem.perm in *. 
        repeat rewrite Hperm.
        repeat rewrite Hpmap.
        rewrite getCurPerm_correct.
        unfold permission_at.
          by assumption.
      - inversion Hresume; subst.
        assert (Hpmap: getThreadR cnt' = getThreadR cnt)
          by (apply gThreadCR).
        assert (Hperm0: permission_at
                          (restrPermMap (Hcomp _ cnt)) b ofs Cur =
                        (getThreadR cnt) # b ofs)
          by (eapply restrPermMap_Cur; eauto).
        unfold Mem.perm, permission_at in *.
        rewrite Hperm Hperm0. rewrite Hpmap. auto.
        split; auto.
        intros Hinvalid p Hlt.
        apply Mem.nextblock_noaccess with (ofs := ofs)
                                            (k := Cur) in Hinvalid.
        rewrite Hinvalid in Hperm0. rewrite <- Hperm0 in Hlt.
        simpl in Hlt. by exfalso.
    Qed.

    Lemma decay_trans :
      forall m m' m'',
        decay m m' ->
        decay m' m'' ->
        decay m m''.
    Admitted.

    (* This lemma is probably not useful anymore...*)
    Lemma internal_execution_decay:
      forall tp m tp' m' xs i (cnt: containsThread tp i)
        (cnt': containsThread tp' i)
        (Hcomp: mem_compatible tp m)
        (Hcomp': mem_compatible tp' m')
        (Hexec: internal_execution [seq x <- xs | x == i] tp m tp' m'),
        decay (restrPermMap (Hcomp _ cnt))
              (restrPermMap (Hcomp' _ cnt')).
    Proof.
      intros tp m tp' m' xs.
      generalize dependent tp. generalize dependent m.
      induction xs.
      - intros. simpl in Hexec. inversion Hexec; subst.
        pf_cleanup. admit. (*decay is refl *)
        simpl in HschedN. discriminate.
      - intros.
        destruct (a == i) eqn:Heq; move/eqP:Heq=>Heq; subst.
        + simpl in Hexec.
          erewrite if_true in Hexec by (apply eq_refl).
          inversion Hexec; subst; simpl in *.
          inversion HschedN; subst tid.
          assert (Hcomp'0: mem_compatible tp'0 m'0)
            by (eapply internal_step_compatible; eauto).
          assert (cnt0': containsThread tp'0 i)
            by (eapply containsThread_internal_step; eauto).
          pf_cleanup.
          eapply IHxs with
          (Hcomp := Hcomp'0) (Hcomp' := Hcomp')
                             (cnt := cnt0') (cnt' := cnt') in Htrans.
          assert (Hdecay:
                    decay (restrPermMap (Hcomp _ cnt))
                          (restrPermMap (Hcomp'0 _ cnt0')))
            by (eapply internal_step_decay; eauto).
          eapply decay_trans; eauto.
        + simpl in Hexec.
          erewrite if_false in Hexec
            by (apply/eqP; assumption).
          auto.
    Qed.

    Lemma internal_step_valid:
      forall tp m tp' m' i (cnt: containsThread tp i)
        (Hcomp: mem_compatible tp m)
        (Hstep: internal_step cnt Hcomp tp' m') b
        (Hvalid: Mem.valid_block m b),
        Mem.valid_block m' b.
    Proof.
      intros.
      destruct Hstep as [Htstep | [_ ?]];
        [inversion Htstep; subst;
         eapply corestep_nextblock;
         by eauto | by subst].
    Qed.

    Lemma internal_execution_valid :
      forall tp m tp' m' xs
        (Hexec: internal_execution xs tp m tp' m') b
        (Hvalid: Mem.valid_block m b),
        Mem.valid_block m' b.
    Proof.
      intros.
      generalize dependent tp. generalize dependent m.
      induction xs as [|x xs]; intros.
      inversion Hexec; subst; first by assumption.
      simpl in HschedN;
        by discriminate.
      inversion Hexec; subst.
      simpl in HschedN. inversion HschedN; subst.
      simpl in Htrans.
      assert (Hvalid0: Mem.valid_block m'0 b)
        by (eapply internal_step_valid; eauto).
        by eauto.
    Qed.
     
    
  End InternalSteps.
End InternalSteps.

Module SimDefs.

  Import Concur DryMachine MemObsEq.
  Import DryMachine.ThreadPool SEM.
  Import mySchedule CoreLanguage InternalSteps.
  Require Import sepcomp.closed_safety.
  
  Notation cstep := (cstep the_ge).
  Notation Sch := schedule.
  Notation cmachine_step := ((corestep coarse_semantics) the_ge).
  Notation fmachine_step := ((corestep fine_semantics) the_ge).
  Notation CoarseSem := coarse_semantics.
  Hint Unfold myCoarseSemantics.MachStep myFineSemantics.MachStep.
  
  (** Simulations between individual threads. *)
  
  (* Consider hiding thread_pool completely *)
  Definition weak_tsim {tpc tpf : thread_pool} (mc mf : Mem.mem)
             {i} (f: meminj) (pfc : containsThread tpc i)
             (pff : containsThread tpf i) (compc: mem_compatible tpc mc)
             (compf: mem_compatible tpf mf) : Prop :=
    weak_mem_obs_eq f (restrPermMap  (compc i pfc))
                    (restrPermMap (compf i pff)).
  
  Record strong_tsim {tpc tpf : thread_pool} (mc mf : Mem.mem) {i}
         (f: meminj) (pfc : containsThread tpc i)
         (pff : containsThread tpf i) (compc: mem_compatible tpc mc)
         (compf: mem_compatible tpf mf) : Prop :=
    { code_eq: getThreadC pfc = getThreadC pff;
      strong_obs: mem_obs_eq f (restrPermMap (compc i pfc))
                             (restrPermMap (compf i pff))
    }.

  
  (** Simulation relation between a "coarse-grain" 
     state and a "fine-grain" state *)
  
  Definition max_inv mf := forall b ofs, Mem.valid_block mf b ->
                                    permission_at mf b ofs Max = Some Freeable.

  (* simStrong now maintains the extra invariant that any new blocks
      from the internal execution are owned by thread tid. This is
     needed for the suspend_sim proof. Note that it's not possible
     to prove it just by the fact that only thread tid executes because
     1. some location may be allocated and then freed in this multistep
      execution and 2. our relation only strongly relates the final state
      of the execution not in-between states. *)
  
  Record sim tpc mc tpf mf (xs : Sch) (f : meminj) : Prop :=
    { numThreads : forall i, containsThread tpc i <-> containsThread tpf i;
      mem_compc: mem_compatible tpc mc;
      mem_compf: mem_compatible tpf mf;
      safeCoarse: forall sched n, safeN coarse_semantics the_ge n (sched, tpc) mc;
      simWeak:
        forall tid
          (pfc: containsThread tpc tid)
          (pff: containsThread tpf tid),
          weak_tsim f pfc pff mem_compc mem_compf;
      simStrong:
        forall tid (pfc: containsThread tpc tid) (pff: containsThread tpf tid),
        exists f' tpc' mc', inject_incr f f' /\
                       ([seq x <- xs | x == tid] = nil -> f = f') /\
                       internal_execution ([seq x <- xs | x == tid])
                                          tpc mc tpc' mc' /\
                       (forall (pfc': containsThread tpc' tid)
                         (mem_compc': mem_compatible tpc' mc'),
                           strong_tsim f' pfc' pff mem_compc' mem_compf) /\
                       (forall tid2 (pff2: containsThread tpf tid2)
                          (Hneq: tid <> tid2) b1 b2 ofs,
                           f' b1 = Some (b2,0%Z) ->
                           f b1 = None ->
                           (getThreadR pff2) # b2 ofs = None);
                           
      invF: invariant tpf;
      maxF: max_inv mf
    }.

  (** Distinguishing the various step types of the concurrent machine *)

  Inductive StepType : Type :=
    Internal | Concurrent | Halted | Suspend.

  Definition ctlType (code : ctl) : StepType :=
    match code with
    | Krun c =>
      match at_external Sem c with
      | None => 
        match halted Sem c with
        | Some _ => Halted
        | None => Internal
        end
      | Some _ => Suspend
      end
    | Kstop c => Concurrent
    | Kresume c => Internal
    end.
  
  Definition getStepType {i tp} (cnt : containsThread tp i) : StepType :=
    ctlType (getThreadC cnt).

  Lemma internal_step_type :
    forall i tp tp' m m' (cnt : containsThread tp i)
      (Hcomp: mem_compatible tp m)
      (Hstep_internal: internal_step cnt Hcomp tp' m'),
      getStepType cnt = Internal.
  Proof.
    intros.
    unfold getStepType, ctlType.
    destruct Hstep_internal as [Hcstep | [Hresume Heq]].
    inversion Hcstep. subst. rewrite Hcode.
    assert (H1:= corestep_not_at_external Sem _ _ _ _ _ Hcorestep).
    rewrite H1.
    assert (H2:= corestep_not_halted Sem _ _ _ _ _ Hcorestep).
      by rewrite H2.
      inversion Hresume; subst.
      pf_cleanup. by rewrite Hcode.
  Qed.

  Notation "cnt '@'  'I'" := (getStepType cnt = Internal) (at level 80).
  Notation "cnt '@'  'E'" := (getStepType cnt = Concurrent) (at level 80).
  Notation "cnt '@'  'S'" := (getStepType cnt = Suspend) (at level 80).
  Notation "cnt '@'  'H'" := (getStepType cnt = Halted) (at level 80).

  (** Simulations Diagrams *)
  Definition sim_internal_def :=
    forall (tpc tpf : thread_pool) (mc mf : Mem.mem)
      (xs : Sch) (f : meminj) (i : NatTID.tid)
      (pff: containsThread tpf i)
      (Hinternal: pff @ I)
      (Hsim: sim tpc mc tpf mf xs f),
    exists tpf' mf',
      (forall U, fmachine_step (i :: U, tpf) mf (U, tpf') mf') /\
      sim tpc mc tpf' mf' (i :: xs) f.

  Definition sim_external_def :=
    forall (tpc tpf : thread_pool) (mc mf : Mem.mem)
      (xs : Sch) (f : meminj) (i : NatTID.tid)
      (pff: containsThread tpf i)
      (Hexternal: pff @ E)
      (Hsynced: ~ List.In i xs)
      (Hsim: sim tpc mc tpf mf xs f),
    exists tpc' mc' tpf' mf' f',
      (forall U, fmachine_step (i :: U, tpf) mf (U, tpf') mf') /\
      sim tpc' mc' tpf' mf' xs f'.

  (** When we reach a suspend step, we can ``synchronize'' the two
  machines by executing on the coarse machine the internal steps of
  the thread that reached the suspend step. The injection of this
  thread will now serve as the new injection. *)

  Definition sim_suspend_def :=
    forall (tpc tpf : thread_pool) (mc mf : Mem.mem)
      (xs : Sch) (f : meminj) (i : NatTID.tid)
      (pff: containsThread tpf i)
      (Hexternal: pff @ S)
      (Hsim: sim tpc mc tpf mf xs f),
    exists tpc' mc' tpf' mf' f',
      (forall U, fmachine_step (i :: U, tpf) mf (U, tpf') mf') /\
      sim tpc' mc' tpf' mf' [seq x <- xs | x != i] f'.

End SimDefs.

(** ** Proofs *)
Module SimProofs.

  Import Concur DryMachine MemObsEq.
  Import DryMachine.ThreadPool SEM.
  Import mySchedule CoreLanguage InternalSteps.
  Require Import sepcomp.closed_safety.
  Import ThreadPoolWF SimDefs.
  
  (** Solves absurd cases from fine-grained internal steps *)
    Ltac absurd_internal Hstep :=
      inversion Hstep; try inversion Htstep; subst; simpl in *;
      try match goal with
          | [H: value _ = Some _ |- _] => inversion H; subst
          end; pf_cleanup;
      repeat match goal with
             | [H: getThreadC ?Pf = _, Hint: ?Pf @ I |- _] =>
               unfold getStepType in Hint;
                 rewrite H in Hint; simpl in Hint
             | [H1: match ?Expr with _ => _ end = _,
                    H2: ?Expr = _ |- _] => rewrite H2 in H1
             | [H: threadHalted _ |- _] =>
               inversion H; clear H; subst; pf_cleanup
             | [H1: is_true (isSome (halted ?Sem ?C)),
                    H2: match at_external _ _ with _ => _ end = _ |- _] =>
               destruct (at_external_halted_excl Sem C) as [Hext | Hcontra];
                 [rewrite Hext in H2;
                   destruct (halted Sem C); discriminate |
                  rewrite Hcontra in H1; exfalso; by auto]
             end; try discriminate; try (exfalso; by auto).

    Context {cSpec : corestepSpec}.

    (** Proofs about [internal_execution] and [internal_step] *)
      
    Lemma internal_step_cmachine_step :
      forall (i : NatTID.tid) (tp tp' : thread_pool) (m m' : mem)
        (U : list NatTID.tid)
        (Hcnt: containsThread tp i)
        (Hcomp: mem_compatible tp m) 
        (Hstep_internal: internal_step Hcnt Hcomp tp' m'),
        cmachine_step ((buildSched (i :: U)), tp) m
                     ((buildSched (i :: U)), tp') m' /\
        (forall tp'' m'' U',
            cmachine_step ((buildSched (i :: U)), tp) m
                         ((buildSched U'), tp'') m'' ->
            tp' = tp'' /\ m' = m'' /\ i :: U = U').
    Proof.
      intros. split.
      destruct Hstep_internal as [Hcore | [Hresume Hmem]]; subst;
      autounfold;
      econstructor(simpl; eauto).
      intros tp'' m'' U' Hstep.
      assert (Hstep_internal': internal_step Hcnt Hcomp tp'' m'' /\ i :: U = U').
      { inversion Hstep; subst; clear Hstep;
        simpl in *; inversion HschedN; subst; pf_cleanup;
        unfold internal_step; try (by auto);
        apply internal_step_type in Hstep_internal; exfalso;
        unfold getStepType, ctlType in Hstep_internal;
        try inversion Htstep; 
        try (inversion Hhalted); subst;
        unfold getThreadC in *; pf_cleanup;
        repeat match goal with
               | [H1: context[match ?Expr with | _ => _ end],
                      H2: ?Expr = _ |- _] =>
                 rewrite H2 in H1
               end; try discriminate.
        destruct (at_external_halted_excl Sem c) as [Hnot_ext | Hcontra].
        rewrite Hnot_ext in Hstep_internal.
        destruct (halted Sem c); discriminate.
        rewrite Hcontra in Hcant. auto.
      }
      destruct Hstep_internal' as [Hstep_internal' Heq]; subst.
      destruct (internal_step_det Hstep_internal Hstep_internal'); subst.
      auto.
    Qed.

    Lemma safeN_corestepN_internal:
      forall xs i U tpc mc tpc' mc' n
        (Hsafe : safeN coarse_semantics the_ge
                       ((size [seq x <- xs | x == i]) + n)
                       (buildSched (i :: U), tpc) mc)
        (Hexec : internal_execution [seq x <- xs | x == i] tpc mc tpc' mc'),
        corestepN CoarseSem the_ge (size [seq x <- xs | x == i])
                  (buildSched (i :: U), tpc) mc (buildSched (i :: U), tpc') mc'
        /\ safeN coarse_semantics the_ge n (buildSched (i :: U), tpc') mc'.
    Proof.
      intros xs. induction xs as [ | x xs]; intros.
      { simpl in *. inversion Hexec; subst.
        auto.
        simpl in HschedN. discriminate.
      }
      { simpl in *.
        destruct (x == i) eqn:Hx; move/eqP:Hx=>Hx; subst.
        - simpl in Hsafe.
          destruct Hsafe as [[st' [m' Hmach_step]] Hsafe].
          destruct st' as [stU' tp'].
          specialize (Hsafe _ _ Hmach_step).
          inversion Hexec; subst; simpl in *; clear Hexec;
          inversion HschedN; subst i.
          assert (Hmach_step_det :=
                    internal_step_cmachine_step U Hstep).
          destruct Hmach_step_det as [Hmach_step' Hmach_det].
          specialize (Hmach_det _ _ _ Hmach_step).
          destruct Hmach_det as [? [? ?]]; subst.
          destruct (IHxs _ _ _ _ _ _ _ Hsafe Htrans) as [HcorestepN Hsafe'].
          eauto.
        - eapply IHxs; eauto.
      }
    Qed.

    Lemma at_internal_cmachine_step :
      forall i U U' tp tp' m m' (cnt: containsThread tp i)
        (isInternal: cnt @ I)
        (Hstep: cmachine_step (buildSched (i :: U), tp) m (U', tp') m'),
      exists (Hcomp : mem_compatible tp m),
        internal_step cnt Hcomp tp' m' /\ U' = buildSched (i :: U).
    Proof.
      intros.
      unfold getStepType in isInternal.
      inversion Hstep; subst; try inversion Htstep; subst; simpl in *;
      try match goal with
          | [H: value _ = Some _ |- _] => inversion H; subst
          end; pf_cleanup;
      repeat match goal with
             | [H: getThreadC _ = _ |- _] =>
               rewrite H in isInternal; simpl in isInternal
             | [H1: match ?Expr with _ => _ end = _,
                    H2: ?Expr = _ |- _] => rewrite H2 in H1
             | [H: threadHalted _ |- _] =>
               inversion H; clear H; subst; pf_cleanup
             end; try discriminate; try (exfalso; by auto).
      exists Hcmpt. split; auto.
      right; auto.
      exists Hcmpt. split; auto.
      left; auto.
      destruct (at_external_halted_excl Sem c) as [Hext | Hcontra];
      [rewrite Hext in isInternal;
      destruct (halted Sem c); discriminate |
       rewrite Hcontra in Hcant; exfalso; by auto].
    Qed.

    (** Proofs about [fmachine_step]*)
    Lemma fstep_containsThread :
      forall tp tp' m m' i j
        (cntj: containsThread tp j)
        (Hstep: forall U, fmachine_step (i :: U, tp) m (U, tp') m'),
        containsThread tp' j.
    Proof.
      intros. specialize (Hstep empty).
      inversion Hstep; subst; try inversion Htstep;
      simpl in *; try inversion HschedN;
      subst; auto;
      (* the tactic below seems highly redundant but maybe it won't be
         if we make the modules opaque *)
      repeat match goal with
             | [ |- containsThread (updThreadC _ _) _] =>
               apply cntUpdateC; auto
             | [ |- containsThread (updThread _ _ _) _] =>
               apply cntUpdate; auto
             | [ |- containsThread (updThreadR _ _) _] =>
               apply cntUpdateR; auto
             | [ |- containsThread (addThread _ _ _) _] =>
               apply cntAdd; auto
             end.
    Qed.

    Lemma fstep_containsThread' :
      forall tp tp' m m' i j
        (cnti: containsThread tp i)
        (cntj: containsThread tp' j)
        (Hinternal: cnti @ I)
        (Hstep: forall U, fmachine_step (i :: U, tp) m (U, tp') m'),
        containsThread tp j.
    Proof.
      intros.
      specialize (Hstep empty).
      absurd_internal Hstep;
        by eauto.
    Qed.
    
    Lemma fmachine_step_invariant:
      forall (tp tp' : thread_pool) m m' (i : nat) (pf : containsThread tp i) U
        (Hcompatible: mem_compatible tp m)
        (Hinternal: pf @ I)
        (Hstep: fmachine_step (i :: U, tp) m (U, tp') m'),
        invariant tp'.
    Proof.
      intros.
      absurd_internal Hstep.
      inversion Hinv.
      constructor.
      intros i j cnti' cntj' Hneq.
      assert (cnti := @cntUpdateC' tid i tp (Krun c) Htid cnti').
      assert (cntj := @cntUpdateC' tid j tp (Krun c) Htid cntj').
      erewrite @gThreadCR with (cntj := cntj).
      erewrite @gThreadCR with (cntj := cnti);
        by auto.
      intros cnt0'.
      assert (cnt0 := @cntUpdateC' tid 0 tp (Krun c) Htid cnt0').
      assert (tid <> 0).
      { destruct (lock_pool0 cnt0) as [? [Hcontra _]].
        intros H. subst tid. pf_cleanup. by congruence.
      }
      erewrite <- @gsoThreadCC with (cntj := cnt0);
        by eauto.
        by eapply corestep_invariant; eauto.
    Qed.

    (* TODO: This is misplaced or maybe not*)
    Lemma permMap_wf_setMax:
      forall (tp : thread_pool) i m
        (Hwf: permMap_wf tp (getCurPerm m) i),
        permMap_wf tp (getCurPerm (setMaxPerm m)) i.
    Proof.
      intros. unfold permMap_wf in *.
      intros.
      specialize (Hwf j cntj Hneq).
      unfold permMapsDisjoint in *.
      intros. specialize (Hwf b ofs).
      rewrite getCurPerm_correct.
      rewrite getCurPerm_correct in Hwf.
      assert (H := setMaxPerm_Cur m b ofs). unfold permission_at in *.
      rewrite H;
        by auto.
    Qed.
    
    Lemma mem_compatible_setMaxPerm :
      forall tp m
        (Hcomp: mem_compatible tp m),
        mem_compatible tp (setMaxPerm m).
    Proof.
      intros tp m Hcomp i cnt b ofs.
      rewrite getMaxPerm_correct.
      destruct (valid_block_dec m b) as [Hvalid | Hinvalid].
      erewrite setMaxPerm_MaxV by assumption. simpl.
      match goal with
      | [ |- match ?Expr with _ => _ end] =>
        destruct Expr
      end; constructor.
      erewrite setMaxPerm_MaxI by assumption.
      apply Mem.nextblock_noaccess with (ofs := ofs) (k := Max) in Hinvalid.
      specialize (Hcomp _ cnt b ofs). rewrite getMaxPerm_correct in Hcomp.
      unfold permission_at in Hcomp.
      rewrite Hinvalid in Hcomp. simpl in Hcomp.
      destruct ((getThreadR cnt) # b ofs); simpl; tauto.
    Qed.
    
    Lemma fmachine_step_compatible:
      forall (tp tp' : thread_pool) m m' (i : nat) (pf : containsThread tp i) U
        (Hcompatible: mem_compatible tp m)
        (Hinternal: pf @ I)
        (Hstep: fmachine_step (i :: U, tp) m (U, tp') m'),
        mem_compatible tp' m'.
    Proof.
      intros.
      absurd_internal Hstep.
      unfold mem_compatible.
      intros i cnti'.
      assert (cnti := cntUpdateC' _ Htid cnti').
      erewrite @gThreadCR with (cntj:= cnti);
        by eauto.
      simpl.
      eapply mem_compatible_setMaxPerm. 
      eapply corestep_compatible; eauto.
      (* this holds trivially, we don't need to use corestep_compatible*)
    Qed.

    Lemma gsoThreadR_fstep:
      forall tp tp' m m' i j U
        (Hneq: i <> j)
        (pfi: containsThread tp i)
        (pfj: containsThread tp j)
        (pfj': containsThread tp' j)
        (Hinternal: pfi @ I)
        (Hstep: fmachine_step (i :: U, tp) m (U, tp') m'),
        getThreadR pfj = getThreadR pfj'.
    Proof.
      intros.
      absurd_internal Hstep;
        [reflexivity |
         erewrite <- @gsoThreadRes with (cntj' := pfj);
           by eauto].
    Qed.

    Lemma permission_at_fstep:
      forall tp tp' m m' i j U
        (Hneq: i <> j)
        (pfi: containsThread tp i)
        (pfj: containsThread tp j)
        (pfj': containsThread tp' j)
        (Hcomp: mem_compatible tp m)
        (Hcomp': mem_compatible tp' m')
        (Hinv: pfi @ I)
        (Hstep: fmachine_step (i :: U, tp) m (U,tp') m') b ofs,
        permission_at (restrPermMap (Hcomp _ pfj)) b ofs Cur =
        permission_at (restrPermMap (Hcomp' _ pfj')) b ofs Cur.
    Proof.
      intros.
      do 2 rewrite restrPermMap_Cur;
      erewrite gsoThreadR_fstep;
        by eauto.
    Qed.

    Lemma gsoThreadC_fstepI:
      forall tp tp' m m' i j U
        (pfj: containsThread tp j)
        (pfj': containsThread tp' j)
        (pfi: containsThread tp i)
        (Hinternal: pfi @ I)
        (Hstep: fmachine_step (i :: U, tp) m (U, tp') m')
        (Hneq: i <> j),
        getThreadC pfj = getThreadC pfj'.
    Proof.
      intros.
      absurd_internal Hstep.
      erewrite gsoThreadCC with (cntj' := pfj); eauto.
      erewrite gsoThreadCode with (cntj' := pfj); eauto.
    Qed.
    
    Hint Resolve fmachine_step_compatible fmachine_step_invariant
         fstep_containsThread fstep_containsThread' : fstep.

    Hint Rewrite gsoThreadR_fstep permission_at_fstep : fstep.
    
    Lemma fmachine_step_disjoint_val :
      forall tp tp' m m' i j U
        (Hneq: i <> j)
        (pfi: containsThread tp i)
        (pfj: containsThread tp j)
        (pfj': containsThread tp' j)
        (Hcomp: mem_compatible tp m)
        (Hcomp': mem_compatible tp' m')
        (Hinv: pfi @ I)
        (Hstep: fmachine_step (i :: U, tp) m (U,tp') m') b ofs
        (Hreadable: 
           Mem.perm (restrPermMap (Hcomp _ pfj)) b ofs Cur Readable),
        Maps.ZMap.get ofs (Mem.mem_contents m) # b =
        Maps.ZMap.get ofs (Mem.mem_contents m') # b.
    Proof.
      intros.
      absurd_internal Hstep;
        [reflexivity | eapply corestep_disjoint_val; by eauto].
    Qed.

    Lemma fmachine_decay :
      forall tp m tp' m' i (cnt: containsThread tp i)
        (Hinternal: cnt @ I)
        (Hcomp: mem_compatible tp m)
        (Hstep : forall U,
            fmachine_step (i :: U, tp) m (U, tp') m'),
        decay (restrPermMap (Hcomp _ cnt)) m'.
    Admitted.
    
    (** Profs about [mem_obs_eq] and [weak_mem_obs_eq] *)
    
    Lemma weak_obs_eq_restr :
      forall (m m' : Mem.mem) (f : meminj)
        (weakObsEq: weak_mem_obs_eq f m m')
        (pf: permMapLt (getCurPerm m) (getMaxPerm m))
        (pf': permMapLt (getCurPerm m') (getMaxPerm (setMaxPerm m'))),
        weak_mem_obs_eq f (restrPermMap pf) (restrPermMap pf').
    Proof.
      intros. inversion weakObsEq.
      constructor; auto.
      intros.
      assert (Hrestr := restrPermMap_correct pf b1 ofs).
      destruct Hrestr as [_ Hcur].
      assert (Hrestr' :=
                restrPermMap_correct pf' b2 ofs).
      destruct Hrestr' as [_ Hcur'].
      rewrite Hcur; rewrite Hcur';
      do 2 rewrite getCurPerm_correct; eauto.
    Qed.

    Lemma mem_obs_eq_restr :
      forall (m m' : Mem.mem) (f : meminj)
        (memObsEq: mem_obs_eq f m m')
        (pf: permMapLt (getCurPerm m) (getMaxPerm m))
        (pf': permMapLt (getCurPerm m') (getMaxPerm (setMaxPerm m'))),
        mem_obs_eq f (restrPermMap pf) (restrPermMap pf').
    Proof.
      intros.
      inversion memObsEq.
      assert (Hrestr := restrPermMap_correct pf).
      assert (Hrestr' :=
                restrPermMap_correct pf').
      constructor.
      - eapply weak_obs_eq_restr; eauto.
      - intros;
        destruct (Hrestr b1 ofs) as [_ Hcur];
        destruct (Hrestr' b2 ofs) as [_ Hcur'];
        rewrite Hcur Hcur';
        do 2 rewrite getCurPerm_correct; auto.
      - intros. unfold restrPermMap; simpl.
        eapply val_obs_eq0; eauto.
        unfold Mem.perm in *.
        destruct (Hrestr b1 ofs) as [_ Hcur].
        unfold permission_at in *.
        rewrite Hcur in Hperm.
        rewrite getCurPerm_correct in Hperm. assumption.
    Qed.

    Lemma weak_obs_eq_setMax:
      forall (f : meminj) (m m' : mem)
        (Hweak_obs: weak_mem_obs_eq f m m'),
        weak_mem_obs_eq f m (setMaxPerm m').
    Proof.
      intros. inversion Hweak_obs.
      constructor; auto.
      intros. rewrite setMaxPerm_Cur.
      auto.
    Qed.
    
    Lemma mem_obs_eq_setMax :
      forall f m m'
        (Hobs_eq: mem_obs_eq f m m'),
        mem_obs_eq f m (setMaxPerm m').
    Proof.
      intros. inversion Hobs_eq.
      constructor. apply weak_obs_eq_setMax; auto.
      intros. rewrite setMaxPerm_Cur. auto.
      intros. unfold Mem.perm in *.
      eapply val_obs_eq0; auto.
    Qed.
    
    (** ** Proofs of internal step safety and simulation*)

    Lemma tsim_fstep_safe:
      forall tpc tpc' tpf mc mc' mf i fi
        (pfc: containsThread tpc i) (pff: containsThread tpf i)
        (Hcompc: mem_compatible tpc mc)
        (Hcompf: mem_compatible tpf mf)
        (HmaxF: max_inv mf)
        (HinvF: invariant tpf)
        (Hstrong_sim: strong_tsim fi pfc pff Hcompc Hcompf)
        (Hstep_internal: internal_step pfc Hcompc tpc' mc'),
      exists tpf' mf' fi',
        (forall U, fmachine_step (i :: U, tpf) mf (U, tpf') mf') /\
        max_inv mf' /\
        inject_incr fi fi' /\
        (forall (pfc': containsThread tpc' i) (pff': containsThread tpf' i)
          (Hcompc': mem_compatible tpc' mc') (Hcompf': mem_compatible tpf' mf'),
            strong_tsim fi' pfc' pff' Hcompc' Hcompf') /\
        (forall j
           (pffj : containsThread tpf j),
            i <> j ->
            forall (b1 b2 : block),
              fi' b1 = Some (b2, 0%Z) ->
              fi b1 = None ->
              forall ofs, (getThreadR pffj) # b2 ofs = None).
    Proof.
      intros.
      assert (HinvC': invariant tpc')
        by (eapply internal_step_invariant; eauto).
      destruct Hstep_internal as [Hcstep | Hresume].
      { inversion Hcstep; subst; clear Hcstep.
        destruct Hstrong_sim as [Hcode_eq memObsEq].
        rewrite Hcode in Hcode_eq.
        assert (H' := Hcorestep).
        eapply corestep_obs_eq in Hcorestep; eauto.
        destruct Hcorestep
          as [mf' [fi' [HcorestepF [Hobs_eq' [Hincr [Hseparated Hinverse]]]]]].
        remember (restrPermMap (Hcompf _ pff)) as mf1 eqn:Hrestrict.
        symmetry in Hrestrict.
        remember (updThread pff (Krun c') (getCurPerm mf'))
          as tpf' eqn:Hupd.
        exists tpf' (setMaxPerm mf') fi'.
        split.
        { (* fine machine steps *)
          intros U. eapply myFineSemantics.core_step; simpl; eauto.
          econstructor; eauto.
        }
        {
          split.
          unfold max_inv.
          intros b ofs Hvalid.
          rewrite setMaxPerm_MaxV;
            by auto.
          split; first by assumption.
          split.
          intros. econstructor;
            first by (subst tpf'; by do 2 erewrite gssThreadCode).
          assert (Hlt_mc' : permMapLt (getCurPerm mc')
                                      (getMaxPerm mc'))
            by (unfold permMapLt; intros;
                rewrite getCurPerm_correct; rewrite getMaxPerm_correct;
                apply Mem.access_max).
          erewrite restrPermMap_irr with (Hlt' := Hlt_mc')
            by (by rewrite gssThreadRes).
          assert (Hlt_mf': permMapLt (getCurPerm mf')
                                     (getMaxPerm (setMaxPerm mf'))).
         { unfold permMapLt. intros.
           rewrite getCurPerm_correct. rewrite getMaxPerm_correct.
           destruct (valid_block_dec mf' b) as [Hvalid | Hinvalid].
           erewrite setMaxPerm_MaxV by assumption. simpl.
           destruct (permission_at mf' b ofs Cur); constructor.
           erewrite setMaxPerm_MaxI by assumption. simpl.
           apply Mem.nextblock_noaccess with (ofs := ofs) (k := Cur) in Hinvalid.
           unfold permission_at. rewrite Hinvalid. constructor.
         }
         erewrite restrPermMap_irr with (Hlt' := Hlt_mf')
            by (subst tpf'; rewrite gssThreadRes; eauto);
           by eapply mem_obs_eq_restr.
         (* block ownership*)
         (*sketch: the invariant is maintanted by coresteps hence it
           will hold for tpf'. Moreover we know that the new blocks in
           mc'|i will be mapped to new blocks in mf' by inject separated,
           where the permissions are empty for other threads. *)
         intros j pffj Hij b1 b2 Hfi' Hfi ofs.
         specialize (Hseparated _ _ _ Hfi Hfi').
         destruct Hseparated as [Hinvalidmc1 Hinvalidmf1].
         apply Mem.nextblock_noaccess with (k := Max) (ofs := ofs) in Hinvalidmf1.
         assert (Hlt := Hcompf _ pffj b2 ofs).
         rewrite getMaxPerm_correct in Hlt.
         assert (Hperm_b2: permission_at mf b2 ofs Max = None).
         { subst mf1.
           assert (H:= restrPermMap_Max (Hcompf i pff) b2 ofs).
           unfold permission_at in H. rewrite Hinvalidmf1 in H.
           rewrite getMaxPerm_correct in H. by auto.
         }
         rewrite Hperm_b2 in Hlt.
         simpl in Hlt. destruct ((getThreadR pffj) # b2 ofs); by tauto.
        }
      }
      { destruct Hresume as [Hresume Heq]; subst.
        inversion Hresume; subst; clear Hresume; pf_cleanup.
        destruct Hstrong_sim as [Hcode_eq memObsEq].
        rewrite Hcode in Hcode_eq.
        remember (updThreadC pff (Krun c)) as tpf' eqn:Hupd.
        exists tpf' mf fi.
        split.
        { (* The fine-grained machine steps *)
          intros. eapply myFineSemantics.resume_step; simpl; eauto.
          econstructor; eauto.
        }
        { split; first by auto.
          split; first by auto.
          split.
          - intros.
            constructor;
              first by (subst tpf';
                          by do 2 rewrite gssThreadCC).
            erewrite restrPermMap_irr with
            (Hlt' := Hcompf _ pff) by (subst; pf_cleanup; reflexivity).
            erewrite restrPermMap_irr; eauto.
              by rewrite gThreadCR.
          - intros j pffj Hij b1 b2 Hfi Hfi'.
            by congruence.
        }
      }
    Qed.
    
    Lemma weak_tsim_fstep:
      forall tpc tpf tpf' mc mf mf' i j f U
        (pffi: containsThread tpf i)
        (pfcj: containsThread tpc j) (pffj: containsThread tpf j)
        (pffj': containsThread tpf' j)
        (Hcompc: mem_compatible tpc mc)
        (Hcompf: mem_compatible tpf mf)
        (Hcompf': mem_compatible tpf' mf')
        (HinvF: invariant tpf)
        (Hinternal: pffi @ I)
        (Hstep: fmachine_step (i :: U, tpf) mf (U, tpf') mf')
        (HweakSim: weak_tsim f pfcj pffj Hcompc Hcompf),
        weak_tsim f pfcj pffj' Hcompc Hcompf'.
    Proof.
    Admitted.

    Lemma cmachine_step_invariant:
      forall tpc mc tpc' mc' tpc'' mc'' U U' U'' n
        (HstepN: corestepN CoarseSem the_ge n
                           (U, tpc) mc (U', tpc') mc')
        (Hstep: cmachine_step (U', tpc') mc' (U'', tpc'') mc''),
        invariant tpc.
    Proof.
      intros. destruct n; simpl in HstepN. inversion HstepN; subst.
      inversion Hstep; subst; try inversion Htstep; auto.
      inversion Hhalted; simpl in *; subst; auto.
      simpl in *; subst; auto.
      destruct HstepN as [tpc''' [mc''' [Hstep0 _]]].
      clear Hstep.
      inversion Hstep0; subst; try inversion Htstep; auto.
      inversion Hhalted; simpl in *; subst; auto.
      simpl in *; subst; auto.
    Qed.
          
    Lemma sim_internal : sim_internal_def.
    Proof.
      unfold sim_internal_def.
      intros.
      inversion Hsim as
          [HnumThreads HmemCompC HmemCompF HsafeC HsimWeak HsimStrong HinvF HmaxF].
      assert (pfc: containsThread tpc i)
        by (eapply HnumThreads; eauto).
      destruct (HsimStrong i pfc pff)
        as [fi [tpc' [mc' [Hincr [Hsynced [Hexec [Htsim Hownedi]]]]]]];
        clear HsimStrong.
      assert (pfc': containsThread tpc' i)
        by (eapply containsThread_internal_execution in pfc; eauto).
      specialize (Htsim pfc').
      specialize (HsafeC (mySchedule.buildSched (i :: nil))
                         ((size ([seq x <- xs | x == i])).+1)).
      rewrite <- addn1 in HsafeC.
      assert (HcoreN := safeN_corestepN_internal xs _ _ 1 HsafeC Hexec).
      destruct HcoreN as [HcorestepN HsafeN].
      unfold safeN in HsafeN; simpl in *.
      destruct HsafeN as [[[U tpc''] [mc'' Hstep']] _].
      assert (HinvC: invariant tpc)
        by (eapply cmachine_step_invariant; eauto).
      assert (memCompC' := internal_execution_compatible HmemCompC Hexec).
      specialize (Htsim memCompC').
      assert (Hinternal_pfc': pfc' @ I)
        by (assert (Hcodes := code_eq Htsim);
             unfold getStepType; by rewrite Hcodes).
      apply at_internal_cmachine_step with (cnt := pfc') in Hstep'; eauto.
      destruct Hstep' as [Hcomp [Hstep' Heq]]. subst U; pf_cleanup.
      destruct (tsim_fstep_safe HmaxF HinvF Htsim Hstep')
        as [tpf' [mf' [fi' [HstepF [HmaxF' [Hincr' [Htsim' Howned']]]]]]].
      assert (pfc'': containsThread tpc'' i)
        by (eapply containsThread_internal_step; eauto).
      assert (pff': containsThread tpf' i)
        by (eapply (fstep_containsThread pff); eauto).
      assert (memCompC'': mem_compatible tpc'' mc'').
      eapply internal_step_compatible with (Hcompatible := memCompC'); eauto.
      assert (memCompF': mem_compatible tpf' mf')
        by (eapply fmachine_step_compatible with (pf := pff); eauto).
      exists tpf' mf'.
      split.
      (** Proof that the fine-grained execution steps *)
      assumption.
      (** Proof that the simulation is preserved*)
      clear HsafeC HcorestepN.
      eapply Build_sim with (mem_compc := HmemCompC) (mem_compf := memCompF').
      - intros k;
        split;
        intro pfk;
        [apply HnumThreads in pfk | apply HnumThreads];
          by eauto with fstep.
      - apply (safeCoarse Hsim).
      - (** Proof of weak simulation between threads *)
        intros j pfcj pffj'.
        assert (pffj: containsThread tpf j)
          by (eauto with fstep).
        eapply weak_tsim_fstep with (pffi := pff); eauto.
      - (** Proof of strong simulation between threads*)
        intros j pfcj pffj'.
        destruct (i == j) eqn:Heq; move/eqP:Heq=>Heq.
        { subst j. exists fi' tpc'' mc''.
          split;
            first by (eapply inject_incr_trans; eauto).
          split.
          - intros Hnostep.
            simpl in Hnostep. rewrite if_true in Hnostep.
            discriminate. apply eq_refl.
          - split.
            simpl. rewrite if_true.
            assert (Heq: i :: [seq x <- xs | x == i] =
                         [seq x <- xs | x == i] ++ [:: i]).
            { clear. induction xs. reflexivity.
              simpl. destruct (a==i) eqn:Heq; move/eqP:Heq=>Heq.
              subst. simpl. rewrite IHxs. reflexivity.
              auto.
            }
            rewrite Heq.
            eapply internal_execution_trans; by eauto.
              by apply eq_refl.
          - split; first by (intros; eapply Htsim').
            intros k pffk' Hik b1 b2 ofs Hfi' Hf.
            assert (pffk: containsThread tpf k)
              by (eauto with fstep).
            erewrite <- gsoThreadR_fstep with (pfj := pffk); eauto.
            destruct (valid_block_dec mc' b1) as [Hvalidmc'b1 | Hinvalidmc'b1].
            - assert (Hfb1 := (domain_valid (weak_obs_eq (strong_obs Htsim))) b1).
              erewrite restrPermMap_valid in Hfb1.
              destruct (Hfb1 Hvalidmc'b1) as [b2' Hfi].
              assert (b2' = b2)
                by (apply Hincr' in Hfi; rewrite Hfi in Hfi';
                    inversion Hfi'; by subst); subst.
                by eauto.
            - assert (Hfb1 := (domain_invalid
                                 (weak_obs_eq (strong_obs Htsim))) b1).
              erewrite restrPermMap_valid in Hfb1.
              specialize (Hfb1 Hinvalidmc'b1).
              by eauto.
        }
        { simpl. erewrite if_false by (apply/eqP; intros Hcontra; auto).
          clear HsimWeak Htsim Hincr Hincr'.
          assert (HsimStrong := simStrong Hsim).
          assert (pffj: containsThread tpf j)
            by eauto with fstep.
          destruct (HsimStrong j pfcj pffj)
            as [fj [tpcj' [mcj' [Hincrj [Hsyncedj [Hexecj [Htsimj Hownedj]]]]]]].
          exists fj tpcj' mcj'. split; auto. split; [ by auto | split; auto].
          split.
          (* difficult part: simulation between tpf' and tpcj' *)
          intros pfcj' memCompCj'.
          specialize (Htsimj pfcj' memCompCj').
          inversion Htsimj as [code_eqjj memObsEqj].
          constructor;
            first by
              (rewrite code_eqjj;
                 by (eapply gsoThreadC_fstepI; eauto)).
          constructor. (*mem_obs_eq proof*)
          { constructor.
            - apply (domain_invalid (weak_obs_eq memObsEqj)).
            - apply (domain_valid (weak_obs_eq memObsEqj)).
            - assert (Hcodomain := (codomain_valid (weak_obs_eq memObsEqj))).
              intros b1 b2 Hfj.
              specialize (Hcodomain b1 b2 Hfj).
              admit. (*lift valid block for fmachine_step*)
            - intros b1 b2 ofs.
              rewrite <- permission_at_fstep with
              (Hcomp := (mem_compf Hsim)) (U := empty) (i := i) (pfi := pff)
                                          (pfj := pffj)
                                          (Hcomp' := memCompF'); auto.
                by apply (perm_obs_weak (weak_obs_eq memObsEqj)).
          }
          { intros b1 b2 ofs.
            rewrite <- permission_at_fstep with
            (Hcomp := (mem_compf Hsim)) (i := i) (U := empty) (pfi := pff)
                                        (pfj := pffj) (Hcomp' := memCompF'); auto.
              by apply (perm_obs_strong memObsEqj).
          }
          { intros b1 b2 ofs Hfj Hperm. unfold restrPermMap. simpl.
            assert (Hval := val_obs_eq memObsEqj).
            specialize (Hval b1 b2 ofs Hfj Hperm).
            unfold restrPermMap in Hval. simpl in Hval.
            assert (Hpermf: Mem.perm (restrPermMap (HmemCompF _ pffj))
                                     b2 ofs Cur Readable).
            { specialize (HstepF empty).
              assert (Hperm_eqf :=
                        permission_at_fstep Heq pff pffj pffj' HmemCompF memCompF'
                                           Hinternal HstepF b2 ofs).
              unfold permission_at in Hperm_eqf.
              assert (Hperm_weak := (perm_obs_weak (weak_obs_eq memObsEqj) b1
                                                   ofs Hfj)).
              assert (Hperm_strong := (perm_obs_strong memObsEqj) b1 b2 ofs Hfj).
              clear - Hperm Hperm_eqf Hperm_strong Hperm_weak.
              destruct Hsim; simpl in Hperm_strong, Hperm_weak; pf_cleanup.
              unfold permission_at in *.
              rewrite Hperm_eqf in Hperm_strong Hperm_weak.
              unfold Mem.perm_order'' in Hperm_strong, Hperm_weak.
              unfold Mem.perm, Mem.perm_order' in *. 
              destruct ((Mem.mem_access
                           (restrPermMap (memCompF' _ pffj'))) # b2 ofs
                                                                       Cur) eqn:?.
              - rewrite Hperm_eqf.
                destruct ((Mem.mem_access
                             (restrPermMap (memCompCj' _ pfcj')))
                            # b1 ofs Cur) eqn:?.
                eapply perm_order_trans; eauto.
                tauto.
              - rewrite Hperm_eqf.
                destruct ((Mem.mem_access (restrPermMap
                                             (memCompCj' _ pfcj')))
                            # b1 ofs Cur); auto.
            }
            specialize (HstepF empty).
            erewrite <- fmachine_step_disjoint_val with (tp := tpf)
            (i := i) (j := j) (m' := mf') (m := mf) (tp' := tpf') (U := empty);
              by eauto. 
          }
          (* block ownership *)
          intros k pffk' Hjk b1 b2 ofs Hfj Hf.
          assert (pffk: containsThread tpf k)
            by (eapply fstep_containsThread'; eauto).
            specialize (Hownedj _ pffk Hjk b1 b2 ofs Hfj Hf).
            destruct (i == k) eqn:Hik; move/eqP:Hik=>Hik.
            - subst k.
              assert (pfcj': containsThread tpcj' j)
                by (eapply containsThread_internal_execution; eauto).
              assert (Hcompcj': mem_compatible tpcj' mcj')
                by (eapply internal_execution_compatible with (tp := tpc) (m := mc);
                     eauto).
              specialize (Htsimj pfcj' Hcompcj').
              assert (Hcodomain := (codomain_valid (weak_obs_eq
                                                      (strong_obs Htsimj)))).
              specialize (Hcodomain _ _ Hfj).
              erewrite restrPermMap_valid in Hcodomain.
              assert (Hdecay := fmachine_decay pff Hinternal HmemCompF HstepF).
              apply decay_decay' in Hdecay.
              destruct (Hdecay b2 ofs) as [_ Hdecay_valid].
              destruct (Hdecay_valid Hcodomain) as [[Hcontra _]| Hstable].
              assert (Hp := restrPermMap_Cur (HmemCompF i pff) b2 ofs).
              unfold permission_at in Hp.
              rewrite Hp in Hcontra.
              pf_cleanup. by congruence.

              Lemma gssThreadR_fstep:
                forall tp tp' m m' i
                  (pfi: containsThread tp i)
                  (pfi': containsThread tp' i)
                  (Hinternal: pfi @ I)
                  (Hstep: forall U, fmachine_step (i :: U, tp) m (U, tp') m'),
                  getThreadR pfi = getThreadR pfi'.
              Proof. Admitted.
              
              pf_cleanup.
              erewrite <- gssThreadR_fstep with (pfi := pff); eauto.
            - erewrite <- gsoThreadR_fstep with (pfi := pff) (pfj := pffk); eauto.
        }
        { (*invariant tpf' *)
          eapply fmachine_step_invariant with (tp := tpf); eauto.
        }
        { assumption.  }
        Grab Existential Variables. assumption. assumption. assumption.
        auto. auto. auto. auto. (*TODO: find out where these existentials come from*)
    Qed.

    (** ** Proof of simulation for stop steps *)

    Lemma suspend_step_inverse:
      forall i U U' tpc tpc' mc mc'
        (cnt: containsThread tpc i)
        (Hsuspend: cnt @ S)
        (Hstep: cmachine_step (i :: U, tpc) mc (U', tpc') mc'),
        U = U' /\ mc = mc' /\ mem_compatible tpc mc /\
        myCoarseSemantics.suspend_thread cnt tpc'.
    Proof.
      intros.
      inversion Hstep; simpl in *; subst; inversion HschedN; subst;
      try (inversion Htstep || inversion Hhalted); subst; pf_cleanup;
      unfold getStepType in Hsuspend;
      try rewrite Hcode in Hsuspend; simpl in Hsuspend;
      try match goal with
          | [H: match ?Expr with _ => _ end = _, H2: ?Expr = _ |- _] =>
            rewrite H2 in H
          end; try discriminate;
      try match goal with
          | [H: ~ containsThread _ _, H2: containsThread _ _ |- _] =>
            exfalso; by auto
          | [H: is_true (isSome (@halted _ _ _ _ _))  |- _] => 
            destruct (at_external_halted_excl Sem c) as [Hnot_ext | Hcontra];
              [rewrite Hnot_ext in Hsuspend;
                destruct (halted Sem c); discriminate |
               rewrite Hcontra in Hcant; by auto]
          end.
      destruct (at_external Sem c) eqn:Hat_external.
      apply corestep_not_at_external in Hcorestep.
        by congruence.
        destruct (halted Sem c); by discriminate.
        split; by auto.
    Qed.

    Lemma suspendC_step_det:
      forall tp tp' tp'' i (cnt: containsThread tp i)
        (Hstep: myCoarseSemantics.suspend_thread cnt tp')
        (Hstep': myCoarseSemantics.suspend_thread cnt tp''),
        tp' = tp''.
    Proof.
      intros.
      inversion Hstep; inversion Hstep'; subst.
      pf_cleanup. rewrite Hcode in Hcode0.
      inversion Hcode0; by subst.
    Qed.

    Lemma suspendF_containsThread:
      forall tp tp' i j (cnti: containsThread tp i)
        (Hsuspend: myFineSemantics.suspend_thread cnti tp'),
        containsThread tp j <-> containsThread tp' j.
    Proof.
      intros; inversion Hsuspend; subst.
      split;
        [eapply cntUpdateC | eapply cntUpdateC'].
    Qed.

    Lemma suspendC_containsThread:
      forall tp tp' i j (cnti: containsThread tp i)
        (Hsuspend: myCoarseSemantics.suspend_thread cnti tp'),
        containsThread tp j <-> containsThread tp' j.
    Proof.
      intros; inversion Hsuspend; subst.
      split;
        [eapply cntUpdateC | eapply cntUpdateC'].
    Qed.
          
    Lemma updThreadC_compatible:
      forall (tp : thread_pool) m (i : tid) (c : ctl)
        (ctn : containsThread tp i)
        (Hcomp: mem_compatible tp m),
        mem_compatible (updThreadC ctn c) m.
    Proof.
      intros.
      intros j pfj.
        by apply Hcomp.
    Qed.
        
    Corollary suspendC_compatible:
      forall tp tp' m i (cnt: containsThread tp i)
      (Hcomp: mem_compatible tp m)
      (Hsuspend: myCoarseSemantics.suspend_thread cnt tp'),
        mem_compatible tp' m.
    Proof.
      intros. inversion Hsuspend; subst.
        by eapply updThreadC_compatible.
    Qed.

    Corollary suspendF_compatible:
      forall tp tp' m i (cnt: containsThread tp i)
        (Hcomp: mem_compatible tp m)
        (Hsuspend: myFineSemantics.suspend_thread cnt tp'),
        mem_compatible tp' m.
    Proof.
      intros. inversion Hsuspend; subst.
        by apply updThreadC_compatible.
    Qed.

    Lemma gsoThreadC_suspend:
      forall (tp : thread_pool) (i j : tid) (cntj : containsThread tp j)
        (c : code) (Hneq: i <> j) (cnti : containsThread tp i)
        (cntj' : containsThread (updThreadC cnti (Kstop c)) j),
        getThreadC cntj = getThreadC cntj'.
    Proof.
      intros; erewrite gsoThreadCC; eauto.
    Qed.
    
    Corollary gsoThreadC_suspendC:
      forall tp tp' i j (cnt: containsThread tp i) (cntj: containsThread tp j)
        (cntj': containsThread tp' j) (Hneq: i <> j)
        (Hsuspend: myCoarseSemantics.suspend_thread cnt tp'),
        getThreadC cntj = getThreadC cntj'.
    Proof.
      intros; inversion Hsuspend; subst;
        by apply gsoThreadC_suspend.
    Qed.

    Corollary gsoThreadC_suspendF:
      forall tp tp' i j (cnt: containsThread tp i) (cntj: containsThread tp j)
        (cntj': containsThread tp' j) (Hneq: i <> j)
        (Hsuspend: myFineSemantics.suspend_thread cnt tp'),
        getThreadC cntj = getThreadC cntj'.
    Proof.
      intros; inversion Hsuspend; subst;
        by apply gsoThreadC_suspend.
    Qed.

    Lemma gsoThreadR_suspendC:
      forall tp tp' i j (cnt: containsThread tp i) (cntj: containsThread tp j)
        (cntj': containsThread tp' j)
        (Hsuspend: myCoarseSemantics.suspend_thread cnt tp'),
        getThreadR cntj = getThreadR cntj'.
    Proof.
      intros. inversion Hsuspend. subst.
      by erewrite @gThreadCR with (cntj := cntj).
    Qed.

    Lemma gsoThreadR_suspendF:
      forall tp tp' i j (cnt: containsThread tp i) (cntj: containsThread tp j)
        (cntj': containsThread tp' j)
        (Hsuspend: myFineSemantics.suspend_thread cnt tp'),
        getThreadR cntj = getThreadR cntj'.
    Proof.
      intros. inversion Hsuspend. subst.
        by erewrite @gThreadCR with (cntj := cntj).
    Qed.
     
    Lemma filter_neq_eq :
      forall {A :eqType} (xs : seq A) i j (Hneq: i <> j),
        [seq x <- [seq x <- xs | x != i] | x == j] = [seq x <- xs | x == j].
    Proof.
      intros. induction xs.
      - reflexivity.
      - simpl. destruct (a != i) eqn:Hai; move/eqP:Hai=>Hai.
        simpl.
        destruct (a ==j) eqn:Haj; move/eqP:Haj=>Haj;
          [by apply f_equal | assumption].
        subst. erewrite if_false by (apply/eqP; auto).
        assumption.
    Qed.

    Lemma suspendC_invariant:
      forall tp tp' i
        (pff: containsThread tp i)
        (Hinv: invariant tp)
        (Hsuspend: myCoarseSemantics.suspend_thread pff tp'),
        invariant tp'.
    Proof.
      Admitted.
    
    Lemma suspendF_invariant:
      forall tp tp' i
        (pff: containsThread tp i)
        (Hinv: invariant tp)
        (Hsuspend: myFineSemantics.suspend_thread pff tp'),
        invariant tp'.
    Proof.
      intros. inversion Hsuspend; subst.
      inversion Hinv.
      constructor. unfold race_free in *.
      simpl. auto.
      simpl. intros. erewrite if_false.
      eauto.
      apply/eqP. intros Hcontra. inversion Hcontra.
      subst. pf_cleanup.
      specialize (lock_pool0 pff).
      destruct lock_pool0 as [c' [Hget' Hhalted]].
      rewrite Hget' in HC. inversion HC; subst.
      destruct (at_external_halted_excl SEM.Sem c)
        as [?|Hnothalted];
        try congruence.
      rewrite Hnothalted in Hhalted; eauto.
    Qed.

    Lemma strong_tsim_step:
      forall tp1 tp2 tp1' m1 m2 m1' j f
        (pf1j: containsThread tp1 j)
        (pf1j': containsThread tp1' j)
        (Hcomp1: mem_compatible tp1 m1)
        (Hcomp1': mem_compatible tp1' m1')
        (Hinv: invariant tp1')
        (Hsim: strong_tsim f pf1j pf1j' Hcomp1 Hcomp1')
        (Hstep: internal_step pf1j Hcomp1 tp2 m2),
      exists tp2' m2' f',
        internal_step pf1j' Hcomp1' tp2' m2' /\
        inject_incr f f' /\
        inject_separated f f' m1 m1' /\
        (forall b1 b1' b2,
            f b1 = None ->
            f b1' = None ->
            f' b1 = Some (b2,0%Z) ->
            f' b1' = Some (b2,0%Z) ->
            b1 = b1') /\
        (exists g, forall b2, Mem.valid_block m2' b2 ->
                    ~ Mem.valid_block m1' b2 ->
                    exists b1, g b2 = Some (b1, 0%Z) /\
                          f' b1 = Some (b2, 0%Z)
                          /\ f b1 = None) /\
        (exists (pf2j: containsThread tp2 j)
           (pf2j': containsThread tp2' j)
           (Hcomp2: mem_compatible tp2 m2)
           (Hcomp2': mem_compatible tp2' m2'),
            strong_tsim f' pf2j pf2j' Hcomp2 Hcomp2').
    Proof.
      intros.
      inversion Hstep as [Hcstep | [Hresume ?]].
      - inversion Hcstep; subst.
        inversion Hsim as [Hcode_eq Hmem_obs_eq].
        remember (getThreadC pf1j') as c1' eqn:Hcode'.
        subst c1'.
        rewrite Hcode in Hcode_eq.
        assert (H := corestep_obs_eq c c' m2 Hmem_obs_eq Hcorestep).
        destruct H
          as [m2' [f' [Hcorestep' [Hobs_eq [Hincr [Hseparated [Hinjective Hinverse]]]]]]].
        exists (updThread pf1j' (Krun c') (getCurPerm m2')) m2' f'.
        assert (Hinternal':
                  internal_step pf1j' Hcomp1'
                                (updThread pf1j' (Krun c') (getCurPerm m2')) m2')
          by (left; econstructor; eauto).
        split; first by assumption.
        split; first by assumption.
        split; first by assumption.
        split; first by assumption.
        destruct Hinverse as [g Hg].
        split; first by (exists g; eauto).
        assert (pf2j := containsThread_internal_step Hstep pf1j).
        assert (pf2j' := containsThread_internal_step Hinternal' pf1j').
        assert (Hcomp2 := internal_step_compatible Hstep).
        assert (Hcomp2' := internal_step_compatible Hinternal').
        exists pf2j pf2j' Hcomp2 Hcomp2'.
        constructor; first by do 2 rewrite gssThreadCode.
        destruct Hobs_eq as [[Hinvalid' Hvalid' Hweak_perm] Hstrong_perm Hval].
        constructor.
        + (*weak_mem_obs_eq proof*)
          constructor.
          * intros b Hinvalid;
            erewrite restrPermMap_valid in Hinvalid;
              by eauto. 
          * intros b Hvalid;
            erewrite restrPermMap_valid in Hvalid;
              by eauto.
          * eauto.
          * eauto. 
          * intros b1 b2 ofs Hf';
            do 2 rewrite restrPermMap_Cur;
            do 2 rewrite gssThreadRes;
            do 2 rewrite getCurPerm_correct;
              by eauto.
        + (* strong_perm proof *)
          intros b1 b2 ofs Hf'.
          do 2 rewrite restrPermMap_Cur;
            do 2 rewrite gssThreadRes;
            do 2 rewrite getCurPerm_correct;
              by eauto.
        + (* val proof *)
          intros b1 b2 ofs Hf' Hreadable.
          simpl.
          eapply Hval; eauto.
          unfold Mem.perm in *.
          assert (H:= restrPermMap_Cur (Hcomp2 j pf2j) b1 ofs).
          unfold permission_at in H.
          rewrite H in Hreadable.
          rewrite gssThreadRes in Hreadable;
            rewrite getCurPerm_correct in Hreadable.
            by assumption.
      - (* Case internal step is a resume step*)
        subst m2.
        inversion Hsim as [Hcode_eq Hmem_obs_eq].
        inversion Hresume; subst.
        pf_cleanup. rewrite Hcode_eq in Hcode.
        exists (updThreadC pf1j' (Krun c)) m1' f.
        assert (Hinternal':
                  internal_step pf1j' Hcomp1' (updThreadC pf1j' (Krun c)) m1')
          by (right; split; econstructor; eauto).
        split;
          first by assumption.
        split; first by auto.
        split; first by congruence.
        split; first by congruence.
        split; first by
            (exists (fun b : block => Some (b, 0%Z)); intros; by exfalso).
        assert (pf2j := containsThread_internal_step Hstep pf1j).
        assert (pf2j' := containsThread_internal_step Hinternal' pf1j').
        assert (Hcomp2 := internal_step_compatible Hstep).
        assert (Hcomp2' := internal_step_compatible Hinternal').
        exists pf2j pf2j' Hcomp2 Hcomp2'.
        constructor; first by do 2 rewrite gssThreadCC.
        destruct Hmem_obs_eq
          as [[Hinvalid' Hvalid' Hcodomain Hweak_perm] Hstrong_perm Hval].
        constructor.
        + (*weak_mem_obs_eq proof*)
          constructor.
          * intros b Hinvalid;
            erewrite restrPermMap_valid in Hinvalid;
              by eauto. 
          * intros b Hvalid;
            erewrite restrPermMap_valid in Hvalid;
              by eauto.
          * by eauto.
          * intros b1 b2 ofs Hf'. 
            do 2 rewrite restrPermMap_Cur;
              do 2 rewrite gThreadCR.
            specialize (Hweak_perm _ _ ofs Hf').
            do 2 rewrite restrPermMap_Cur in Hweak_perm.
              by assumption.
        + (* strong_perm proof *)
          intros b1 b2 ofs Hf'.
          do 2 rewrite restrPermMap_Cur;
            do 2 rewrite gThreadCR;
            specialize (Hstrong_perm _ _ ofs Hf');
            do 2 rewrite restrPermMap_Cur in Hstrong_perm;
              by assumption.
        + (* val proof *)
          intros b1 b2 ofs Hf' Hreadable.
          simpl.
          eapply Hval; eauto.
          unfold Mem.perm in *.
          assert (H2:= restrPermMap_Cur (Hcomp2 j pf2j) b1 ofs).
          assert (H1:= restrPermMap_Cur (Hcomp1 j pf1j) b1 ofs).
          unfold permission_at in *.
          rewrite H2 in Hreadable.
          rewrite H1.
            by rewrite gThreadCR in Hreadable.
    Qed.

    Lemma strong_tsim_execution:
      forall tp1 tp2 tp1' m1 m2 m1' j xs f
        (pf1j: containsThread tp1 j)
        (pf1j': containsThread tp1' j)
        (Hcomp1: mem_compatible tp1 m1)
        (Hcomp1': mem_compatible tp1' m1')
        (Hinv: invariant tp1')
        (Hsim: strong_tsim f pf1j pf1j' Hcomp1 Hcomp1')
        (Hexec: internal_execution [seq x <- xs | x == j] tp1 m1 tp2 m2),
      exists tp2' m2' f',
        internal_execution [seq x <- xs | x == j] tp1' m1' tp2' m2' /\
        inject_incr f f' /\
        inject_separated f f' m1 m1' /\
        (forall b1 b1' b2,
            f b1 = None ->
            f b1' = None ->
            f' b1 = Some (b2,0%Z) ->
            f' b1' = Some (b2,0%Z) ->
            b1 = b1') /\
        (exists g, forall b2, Mem.valid_block m2' b2 ->
                    ~ Mem.valid_block m1' b2 ->
                    exists b1, g b2 = Some (b1, 0%Z) /\
                          f' b1 = Some (b2, 0%Z)
                          /\ f b1 = None) /\
        (exists (pf2j: containsThread tp2 j)
           (pf2j': containsThread tp2' j)
           (Hcomp2: mem_compatible tp2 m2)
           (Hcomp2': mem_compatible tp2' m2'),
            strong_tsim f' pf2j pf2j' Hcomp2 Hcomp2').
    Proof.
     intros.
      generalize dependent tp1.
      generalize dependent m1.
      generalize dependent f.
      generalize dependent tp1'. generalize dependent m1'.
      induction xs as [|x xs]; simpl; intros.
      - inversion Hexec; subst.
        exists tp1' m1' f.
        split; first by constructor.
        split; first by auto.
        split; first by congruence.
        split; first by congruence.
        split. exists (fun b : block => Some (b,0%Z)). intros. by exfalso.
        do 4 eexists; eauto.
        simpl in HschedN; inversion HschedN.
      - destruct (x == j) eqn:Hxj; move/eqP:Hxj=>Hxj.
        + subst x. inversion Hexec as [|tid U U' tp1a m1a tp0 m0].
          subst U U' tp1a m1a tp'' m''.
          simpl in Htrans. simpl in HschedN;
            inversion HschedN; subst tid; clear HschedN Hexec.
          pf_cleanup.
          assert (Htsim := strong_tsim_step Hinv Hsim Hstep).
          destruct Htsim as
              [tp0' [m0' [f0 [Hstep0' [Hincr0' [Hsep0' [Hinjective0' [Hinverse0' Htsim0']]]]]]]].
          destruct Htsim0' as [pfj' [pfj0' [Hcomp' [Hcomp0' Htsim0]]]].
          pf_cleanup.
          assert (Hinv0': invariant tp0') by admit.
          destruct (IHxs _ _ _ _ Hinv0' _ _ _ _ _ Htsim0 Htrans)
            as [tp2' [m2' [f2' [Hexec2 [Hincr2 [Hsep2 [Hinjective2 [Hinverse2 Hsim2]]]]]]]].
          exists tp2' m2' f2'.
          destruct Hsim2 as [pf2j [pf2j' [Hcomp2 [Hcomp2' Htsim2]]]].
          split; first by (econstructor; simpl; eauto).
          split; first by (eapply inject_incr_trans; eauto).
          split.
          { (*injection separated *)
            intros b1 b2 delta Hf Hf2'.
            unfold inject_separated in *.
            destruct (valid_block_dec m0 b1) as [Hvalidm0 | Hinvalidm0].
            * apply (domain_valid (weak_obs_eq (strong_obs Htsim0))) in Hvalidm0.
              destruct Hvalidm0 as [? Hf0].
              assert (b2 = x).
              {  assert (Hf2'' : f2' b1 = Some (x,0%Z))
                by (eapply Hincr2; eauto).
                 rewrite Hf2' in Hf2''. inversion Hf2''; by subst. }
              subst x.
              eapply Hsep0';
                by eauto.
            * apply (domain_invalid (weak_obs_eq (strong_obs Htsim0))) in Hinvalidm0.
              destruct (Hsep2 _ _ _ Hinvalidm0 Hf2') as [Hinvalid Hinvalidm0'].
              split;
                intros Hcontra;
                eapply internal_step_valid in Hcontra; eauto.
          }
          split.
          { (* injectivity for new blocks *)
            intros b1 b1' b2 Hf Hf' Hf2 Hf2'.
            destruct (valid_block_dec m0 b1) as [Hvalidm0 | Hinvalidm0];
              destruct (valid_block_dec m0 b1') as [Hvalidm0' | Hinvalidm0'].
            - apply (domain_valid (weak_obs_eq (strong_obs Htsim0))) in Hvalidm0.
              destruct Hvalidm0 as [b2' Hf0].
              apply (domain_valid (weak_obs_eq (strong_obs Htsim0))) in Hvalidm0'.
              destruct Hvalidm0' as [b2'' Hf0'].
              assert (Heq: b2 = b2' /\ b2' = b2'').
              { apply Hincr2 in Hf0'.
                apply Hincr2 in Hf0. rewrite Hf0 in Hf2.
                rewrite Hf0' in Hf2'. inversion Hf2; inversion Hf2'; by subst. }
              destruct Heq; subst b2' b2''.
              eapply Hinjective0'; eauto.
            - (* Proof: b1 is valid in m0. By codomain_valid b2 must
                 be valid in m0'. b1' is invalid in m0 and valid in
                 m2.  by seperation any block that it maps is invalid
                 in m0' and valid only in m2'.  Hence we derive a
                 contradiction on Mem.valid_block m2' b2 *)
              
              apply (domain_valid (weak_obs_eq (strong_obs Htsim0))) in Hvalidm0.
              destruct Hvalidm0 as [b2' Hf0].
              apply (domain_invalid (weak_obs_eq (strong_obs Htsim0))) in Hinvalidm0'.
              unfold inject_separated in Hsep2.
              specialize (Hsep2 _ _ _ Hinvalidm0' Hf2').
              destruct Hsep2 as [? Hinvalidb2].
              assert (b2 = b2')
                by (eapply Hincr2 in Hf0; rewrite Hf0 in Hf2; inversion Hf2; by subst);
                subst b2'.
              apply (codomain_valid (weak_obs_eq (strong_obs Htsim0))) in Hf0.
              erewrite restrPermMap_valid in Hf0.
                by exfalso.
            - (* Proof: same as above with the roles of b1 and b1' exchanged *)
              
              apply (domain_valid (weak_obs_eq (strong_obs Htsim0))) in Hvalidm0'.
              destruct Hvalidm0' as [b2' Hf0].
              apply (domain_invalid (weak_obs_eq (strong_obs Htsim0))) in Hinvalidm0.
              unfold inject_separated in Hsep2.
              specialize (Hsep2 _ _ _ Hinvalidm0 Hf2).
              destruct Hsep2 as [? Hinvalidb2].
              assert (b2 = b2')
                by (eapply Hincr2 in Hf0; rewrite Hf0 in Hf2'; inversion Hf2'; by subst);
                subst b2'.
              apply (codomain_valid (weak_obs_eq (strong_obs Htsim0))) in Hf0.
              erewrite restrPermMap_valid in Hf0.
                by exfalso.
            - (* Proof: both b1 and b1' are not valid in m0, hence they are only
                  valid in m2, for which we have injectivity by induction hypothesis *)
              apply (domain_invalid (weak_obs_eq (strong_obs Htsim0))) in Hinvalidm0.
              apply (domain_invalid (weak_obs_eq (strong_obs Htsim0))) in Hinvalidm0'.
                by eauto.
          } split.
          { (*inverse, TODO: sketch proof *)
            destruct Hinverse2 as [g2 Hg2spec].
            destruct Hinverse0' as [g0 Hg0spec].
            exists (fun b => match valid_block_dec m0' b with
                     | in_left => g0 b
                     | in_right => g2 b
                     end).
            intros b2 Hvalidm2' Hinvalidm1'.
            destruct (valid_block_dec m0' b2) as [Hvalidm0' | Hinvalidm0'].
            - destruct (Hg0spec _ Hvalidm0' Hinvalidm1') as [b1 [Hg0 [Hf0 Hf]]].
              apply Hincr2 in Hf0.
              exists b1;
                by eauto.
            - destruct (Hg2spec _ Hvalidm2' Hinvalidm0') as [b1 [Hg [Hf2' Hf0]]].
              assert (f b1 = None)
                by (destruct (f b1) as [[? ?]|]eqn:Hf; auto;
                    apply Hincr0' in Hf; by congruence).
              eexists; eauto.
          }
          by eauto.
      - by eauto.
    Qed.
            
    Lemma strong_tsim_stop:
      forall tpc tpc' tpf mc mc' mf i fi
        (pfc: containsThread tpc i) (pff: containsThread tpf i)
        (Hcompc: mem_compatible tpc mc) (Hcompf: mem_compatible tpf mf)
        (HinvF: invariant tpf)
        (Hstrong_sim: strong_tsim fi pfc pff Hcompc Hcompf)
        (Hstep: cmachine_step (buildSched [:: i], tpc) mc (empty, tpc') mc')
        (Hsuspend: pfc @ S),
      exists tpf',
        myFineSemantics.suspend_thread pff tpf' /\
        forall (Hcompc': mem_compatible tpc' mc') (Hcompf' : mem_compatible tpf' mf)
          (pfc': containsThread tpc' i) (pff': containsThread tpf' i),
          strong_tsim fi pfc' pff' Hcompc' Hcompf'.
    Proof.
      intros.
      inversion Hstep; simpl in *; subst; inversion HschedN; subst;
      try (inversion Htstep || inversion Hhalted); subst; pf_cleanup;
      unfold getStepType in Hsuspend;
      try rewrite Hcode in Hsuspend; simpl in Hsuspend;
      try match goal with
          | [H: match ?Expr with _ => _ end = _, H2: ?Expr = _ |- _] =>
            rewrite H2 in H
          end; try discriminate;
      try match goal with
          | [H: ~ containsThread _ _, H2: containsThread _ _ |- _] =>
            exfalso; by auto
          | [H: is_true (isSome (@halted _ _ _ _ _))  |- _] => 
            destruct (at_external_halted_excl Sem c) as [Hnot_ext | Hcontra];
              [rewrite Hnot_ext in Hsuspend;
                destruct (halted Sem c); discriminate |
               rewrite Hcontra in Hcant; by auto]
          end.
      destruct Hstrong_sim as [Hcode_eq memObsEq].
      rewrite Hcode in Hcode_eq.
      exists (updThreadC pff (Kstop c)).
      split.
      econstructor; eauto.
      intros. pf_cleanup.
      constructor;
        first by do 2 rewrite gssThreadCC.
      erewrite restrPermMap_irr with (Hlt := Hcompc' tid Htid) (Hlt' := Hcmpt tid Htid)
        by reflexivity.
      erewrite restrPermMap_irr with (Hlt := Hcompf' tid pff) (Hlt' := Hcompf tid pff)
        by reflexivity.
      assumption.
    Qed.

    (** Strong simulation with the id injection*)
    Lemma strong_tsim_id :
      forall tp tp' tp'' m m' i j xs
        (Hij: i <> j)
        (pfj: containsThread tp j)
        (pfj': containsThread tp' j)
        (pfj'': containsThread tp'' j)
        (pfi': containsThread tp' i)
        (Hcomp: mem_compatible tp m)
        (Hcomp'': mem_compatible tp'' m')
        (Hsuspend: myCoarseSemantics.suspend_thread pfi' tp'')
        (Hexec: internal_execution [seq x <- xs | x == i] tp m tp' m'),
        strong_tsim (fun b => if valid_block_dec m b then Some (b,0%Z) else None)
                    pfj pfj'' Hcomp Hcomp''.
    Proof.
      constructor.
      - (* codes are equal*)
        assert (Hcode := gsoThreadC_suspendC pfj' pfj'' Hij Hsuspend).
        rewrite <- Hcode.
          by erewrite gsoThreadC_exec with (pfj' := pfj'); eauto.
      - (* mem_obs_eq *)
        constructor.
        + (*weak_mem_obs_eq*)
          constructor.
          * (*invalid domain of fid*)
            intros b Hinvalid.
            destruct (valid_block_dec m b) as [Hcontra | ?];
              [unfold Mem.valid_block in *;
                rewrite restrPermMap_nextblock in Hinvalid;
                  by exfalso | by reflexivity].
          * (*valid domain of fid*)
            intros b Hvalid.
              by destruct (valid_block_dec m b);
              [exists b; by reflexivity | unfold Mem.valid_block in *;
                   rewrite restrPermMap_nextblock in Hvalid; by exfalso].
          * (*codomain of fid *)
            intros b1 b2 Hfid.
            destruct (valid_block_dec m b1); simpl in Hfid;
            try discriminate.
            inversion Hfid; subst.
            erewrite restrPermMap_valid.
            eapply internal_execution_valid; by eauto.
          * (* Permissions of memc are higher than memc''*)
            intros b1 b2 ofs Hfid.
            destruct (valid_block_dec m b1); simpl in Hfid;
            try discriminate.
            inversion Hfid; subst.
            do 2 rewrite restrPermMap_Cur.
            erewrite <- gsoThreadR_suspendC with
            (cntj' := pfj'') (cntj := pfj') by eauto.
            erewrite <- gsoThreadR_execution with (pfj' := pfj')
                                                   (pfj := pfj); eauto.
            destruct ((getThreadR pfj) # b2 ofs); simpl;
              by constructor.
        + (* Permissions of memc'' are higher than mc*)
          intros b1 b2 ofs Hfid.
          destruct (valid_block_dec m b1); simpl in Hfid;
          try discriminate.
          inversion Hfid; subst.
          do 2 rewrite restrPermMap_Cur.
          erewrite <- gsoThreadR_suspendC with
          (cntj' := pfj'') (cntj := pfj') by eauto.
          erewrite <- gsoThreadR_execution with (pfj' := pfj')
                                                 (pfj := pfj); eauto.
          destruct ((getThreadR pfj) # b2 ofs); simpl;
            by constructor.
        + (* j-Values of mc and mc'' are equal up to injection*)
          intros b1 b2 ofs Hfid Hreadable.
          destruct (valid_block_dec m b1); simpl in Hfid;
          try discriminate.
          inversion Hfid; subst.
          simpl.
          erewrite <- internal_exec_disjoint_val
          with (tp := tp) (xs := xs) (tp' := tp') (m' := m'); eauto.
          destruct (Maps.ZMap.get ofs (Mem.mem_contents m) # b2);
            constructor.
          destruct v0; try constructor.
          admit. (* need the mem_wd invariant to show this*)
            by eapply containsThread_internal_execution'; eauto.
    Qed.
    
    Lemma sim_suspend : sim_suspend_def.
    Proof.
      unfold sim_suspend_def.
      intros.
      inversion Hsim as
          [HnumThreads HmemCompC HmemCompF HsafeC HsimWeak HsimStrong HinvF HmaxF].
      assert (pfc: containsThread tpc i)
        by (eapply HnumThreads; eauto).
      destruct (HsimStrong i pfc pff)
        as [fi [tpc' [mc' [Hincr [Hsynced [Hexec [Htsim Hownedi]]]]]]];
        clear HsimStrong.
      assert (pfc': containsThread tpc' i)
        by (eapply containsThread_internal_execution in pfc; eauto).
      specialize (Htsim pfc').
      specialize (HsafeC (mySchedule.buildSched (i ::  nil))
                         ((size ([seq x <- xs | x == i])).+1)).
      rewrite <- addn1 in HsafeC.
      assert (HcoreN := safeN_corestepN_internal xs _ nil 1 HsafeC Hexec).
      destruct HcoreN as [HcorestepN HsafeN].
      unfold safeN in HsafeN; simpl in *.
      destruct HsafeN as [[[U tpc''] [mc'' Hstep']] _].
      assert (HinvC: invariant tpc)
        by (eapply cmachine_step_invariant; eauto).
      assert (memCompC' := internal_execution_compatible HmemCompC Hexec).
      specialize (Htsim memCompC').
      assert (Hstop_pfc': pfc' @ S)
        by (assert (Hcodes := code_eq Htsim);
             unfold getStepType; by rewrite Hcodes).
      (* A suspend step pops the schedule and does not touch the memory *)
      assert (Heq : empty = U /\ mc' = mc'' /\ mem_compatible tpc' mc' /\
                    myCoarseSemantics.suspend_thread pfc' tpc'')
        by (eapply suspend_step_inverse; eauto).
      destruct Heq as [? [? [Hcomp' HsuspendC]]]; subst mc' U.
      assert (memCompC'': mem_compatible tpc'' mc'')
        by (eapply suspendC_compatible; eauto).
      assert (HstepF := strong_tsim_stop HinvF Htsim Hstep' Hstop_pfc').
      destruct HstepF as [tpf' [HstepF Htsim']].
      assert (memCompF': mem_compatible tpf' mf)
        by (eapply suspendF_compatible; eauto).
      exists tpc'' mc'' tpf' mf.
      (* since thread i commits, the new global renaming will be fi *)
      exists fi.
      split.
      { (* the fine-grained machine takes a suspend step *)
        intros U; eapply myFineSemantics.suspend_step; simpl; eauto.
      }
      { (* The simulation between tpc'' and tpf' is retained. *)
        eapply Build_sim with (mem_compc := memCompC'') (mem_compf := memCompF').
        { (* number of threads *)
          admit.
        }
        { (* safety of coarse state *)
          intros U n.
          assert (Hsafe_tpc := safeCoarse Hsim).
          specialize (Hsafe_tpc (buildSched (i :: U))
                                (size [seq x <- xs | x == i] + (1 + n))).
          assert (HcoreN := safeN_corestepN_internal xs _ U _ Hsafe_tpc Hexec).
          destruct HcoreN as [HcorestepN_tpc HsafeN_tpc'].
          simpl in HsafeN_tpc'.
          destruct HsafeN_tpc' as [[[U' tpc''0] [mc''0 Hstep'0]] Hsafe].

          destruct (suspend_step_inverse pfc' Hstop_pfc' Hstep'0)
            as [? [? [_ Hsuspend]]]; subst U' mc''0.
          assert (tpc''0 = tpc'')
            by (eapply suspendC_step_det; eauto);
            subst tpc''0.
            by eauto.
        }
        { (* Proof of weak simulation between the threadpools and memories *)
          clear HsafeC. pf_cleanup.
          intros j pfcj'' pffj'.
          constructor.
          { (* Outside the domain of fi *)
            apply (domain_invalid (weak_obs_eq (strong_obs Htsim))).
          }
          { (* Inside the domain of fi *)
            apply (domain_valid (weak_obs_eq (strong_obs Htsim))).
          }
          { (* Valid codomain*)
            apply (codomain_valid (weak_obs_eq (strong_obs Htsim))).
          }
          { (* Permissions of the coarse-state are higher than the fine-state *)
            (* Proof idea: for thread i, we have a strong simulation
            on internal steps and then a suspend step so it should be
            straightforward. For thread j: For blocks before
            (nextblock mc) from weak-sim and for blocks after
            (nextblock mc) this should be freeable on i and thus empty
            on j. Correction: This doesn't hold, because the new
            blocks may have been freed by some internal step. Hence we
            need some other way to capture that they belong to thread
            i and the other threads should have empty permission (a
            new invariant). In fact, this invariant should talk about
            the permissions at the fine-grained level as we no longer
            can use the non-interference invariant because the
            permissions of thread i are not necessary freeable.

            Deprecated and wrong: Morever, we have a strong simulation
            on thread i and a non-interference invariant, hence we can
            infer that the new locations will have empty permission on
            the fine-grained machine.  *)
            intros b1 b2 ofs Hfi.
            (* The permissions will be same as before taking the suspend step*)
            assert (pffj: containsThread tpf j) by admit.
            assert (Hperm_eqF: permission_at (restrPermMap (memCompF' _ pffj'))
                                             b2 ofs Cur =
                               permission_at (restrPermMap (HmemCompF _ pffj))
                                             b2 ofs Cur)
              by (do 2 rewrite restrPermMap_Cur;
                   erewrite <- gsoThreadR_suspendF with (cntj := pffj); eauto).
            rewrite Hperm_eqF.

            (* Likewise for the coarse-grained machine*)
            assert (pfcj': containsThread tpc' j)
              by (eapply suspendC_containsThread; eauto).
            assert (Hperm_eqC: permission_at (restrPermMap (memCompC'' _ pfcj''))
                                             b1 ofs Cur =
                               permission_at (restrPermMap (memCompC' _ pfcj'))
                                             b1 ofs Cur)
              by (do 2 rewrite restrPermMap_Cur;
                   erewrite <- gsoThreadR_suspendC with (cntj := pfcj'); eauto).
            rewrite Hperm_eqC.
            clear Hperm_eqF Hperm_eqC HcorestepN HstepF Hstep'.
            destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
            { (* Case j = i *)
              subst.
              clear - Htsim Hfi.
              destruct Htsim as [_ Hstrong]; destruct Hstrong as [Hweak _ _];
              destruct Hweak as [_ _ _ Hperm_weak].
              specialize (Hperm_weak b1 b2 ofs Hfi).
                by pf_cleanup.
            }
            { (* Case j <> i *)
              assert (pfcj: containsThread tpc j)
                by (eapply containsThread_internal_execution'; eauto).
              specialize (HsimWeak _ pfcj pffj). 
              inversion HsimWeak as [Hinvdomain Hdomain Hcodomain Hobs_weak].
              destruct (valid_block_dec mc b1) as [Hvalid_mc | Hinvalid_mc].
              - (* b1 is a block that's valid in mc, i.e. not allocated by i *)
                assert (Hvalid: Mem.valid_block (restrPermMap (HmemCompC _ pfcj)) b1)
                  by (unfold Mem.valid_block in *;
                        by rewrite restrPermMap_nextblock).
                apply Hdomain in Hvalid.
                destruct Hvalid as [b2' Hf].
                assert (b2 = b2')
                  by (apply Hincr in Hf; rewrite Hf in Hfi;
                      inversion Hfi; by subst); subst b2'.
                erewrite <- permission_at_execution with (xs := xs) (tp := tpc);
                  eauto.
              - (* b1 is a block that's not valid in mc, i.e. allocated by i *)
                (* NOTE: here is the place where we use the invariant
                about blocks owned by i. The proof became much smaller
                (but the burden was moved elsewhere)*)
                apply Hinvdomain in Hinvalid_mc.
                specialize (Hownedi j pffj Hij _ _ ofs Hfi Hinvalid_mc).
                do 2 rewrite restrPermMap_Cur. rewrite Hownedi.
                destruct ((getThreadR pfcj') # b1 ofs); simpl;
                  by auto.
            }
          }
        }
        { (* Proof of strong simulation *)
          (* If thread i = thread j then it's straightforward. 
           * If thread i <> thread j then we need to shuffle things.
           * In particular we know that for some memory mcj s.t mc -->j mcj
           * we have a strong simulation with mf and we want to establish it for
           * mcj' s.t. mc -->i mci --> mcj'. 
           * Take as fj' = | b < nb mc => id | nb mc =< b < nb mci => fi 
           *               | nb mci =< b < nb mcj' => fj (g b)) where g is the inverse of
           * the f that storngly injects mcj to mcj'.
           * Note that: mc strongly injects in mci|j with id, hence mcj strongly injects
              into mcj' with an extension of the id injection (fij). *)

          intros j pfcj'' pffj'.
          case (i == j) eqn:Hij; move/eqP:Hij=>Hij.
          { subst j. exists fi tpc'' mc''.
            split; auto. split; auto. split; auto.
            assert (Hempty: [seq x <- [seq x <- xs | x != i] | x == i] = nil).
            { clear. induction xs as [|x xs]; first by reflexivity.
              simpl; destruct (x == i) eqn:Heq;
              simpl; first by assumption.
              erewrite if_false
                by (apply/eqP; intro Hcontra; subst;
                      by move/eqP:Heq=>Heq).
                by assumption.
            }
            rewrite Hempty. by constructor.
            split; first by auto.
              by congruence.
          }
          { (*case j <> i *)
            assert (pfci'': containsThread tpc'' i)
              by (eapply suspendC_containsThread with (cnti := pfc'); eauto).
            assert (pffi': containsThread tpf' i)
              by (eapply suspendF_containsThread with (cnti := pff); eauto).
            specialize (Htsim' memCompC'' memCompF' pfci'' pffi').
            assert (pfc'j: containsThread tpc' j)
              by (eapply suspendC_containsThread with (cnti := pfc'); eauto).
            assert (pfcj: containsThread tpc j)
              by (eapply containsThread_internal_execution'; eauto).
            
            (* The original <tpc, mc> strongly injects into <tpc'',mc''> where
               <tpc, mc> -->i <tpc', mc'> -->iS <tpc'',mc'>  with the id map*)
            assert (Hsim_c_ci: strong_tsim (fun b => if valid_block_dec mc b then
                                                    Some (b,0%Z) else None)
                                           pfcj pfcj'' HmemCompC memCompC'')
              by (eapply strong_tsim_id with (pfi' := pfc'); eauto).
            
            assert (pffj: containsThread tpf j)
              by (eapply suspendF_containsThread; eauto).
            assert (Htsimj := (simStrong Hsim) j pfcj pffj).
            (* executing the internal steps for thread j gives us a strong 
             * simulation between the coarse and fine-grained states. *)
            destruct Htsimj as
                [fj [tpcj [mcj [Hincrj [Hsyncedj [Hexecj [Htsimj Hownedj]]]]]]].
            (* by the strong simulation on mc and mc'' (via id) we can
              obtain a strong simulation between mcj and mcj', where
              mcj' mc -->i --> mci -->j mcj' *)
            assert (Hinv'': invariant tpc'')
              by (eapply suspendC_invariant with (tp := tpc');
                   [eapply internal_execution_invariant with (tp := tpc); eauto | eauto]).
            assert (Hsimjj':= strong_tsim_execution xs Hinv'' Hsim_c_ci Hexecj).
            destruct Hsimjj'
              as [tpcj' [mcj' [fij [Hexecij [Hincr' [Hsep
                                                       [Hinjective [Hinverse Hsimjj']]]]]]]].
            destruct Hsimjj' as [pfcjj [pfij [Hcompjj [Hcompij Hsimij]]]].
            pf_cleanup.
            destruct Hinverse as [g Hinverse].
            (* notice that mcj and mcj' will be equal up to nextblock mc
             * (mcj injects to mcj' with id up to nextblock mc). Hence
             * for blocks smaller than nb mc we follow the fj injection to mf
             * for blocks between nb mc and nb mc'' we follow the fi injection
             * and for blocks after that we follow the fj one after taking
             * the inverse. (TODO: point to a diagram) *)
            
            remember (fun b1 => match valid_block_dec mc b1 with
                             | in_left => fj b1
                             | in_right =>
                               match valid_block_dec mc'' b1 with
                               | in_left => fi b1
                               | in_right =>
                                 match valid_block_dec mcj' b1 with
                                 | in_left =>
                                   match (g b1) with
                                   | Some (b2, _) =>
                                     fj b2
                                   | None =>
                                     None (*absurd case*)
                                   end
                                 | in_right => None
                                 end
                               end
                             end) as f' eqn:Hf'.
            specialize (Htsimj pfcjj Hcompjj).
            specialize (HsimWeak _ pfc pff).
            exists f' tpcj' mcj'.
            split.
            { (* fi is included in f' *)
              intros b1 b2 delta Hfi.
              subst f'.
              destruct (valid_block_dec mc b1) as [Hvalidmc | Hinvalidmc].
              - assert (Hf_val := (domain_valid HsimWeak) b1).
                specialize (Hf_val
                              ((proj2 (restrPermMap_valid
                                         (HmemCompC i pfc) b1)) Hvalidmc)).
                destruct Hf_val as [b2' Hf_val].
                assert (Hfj := (domain_valid (weak_obs_eq (strong_obs Htsimj)))).
                assert (Hvalidmcj: Mem.valid_block
                                     (restrPermMap (Hcompjj j pfcjj)) b1).
                { rewrite restrPermMap_valid.
                  eapply internal_execution_valid; eauto.
                }
                destruct (Hfj _ Hvalidmcj) as [b2'' Hfj''].
                assert (Heq: b2 = b2' /\ delta = 0%Z)
                  by (apply Hincr in Hf_val;
                       rewrite Hf_val in Hfi; inversion Hfi; by subst);
                  destruct Heq;
                  subst b2' delta.
                apply Hincrj in Hf_val. rewrite Hf_val in Hfj''.
                inversion Hfj''; subst b2''. assumption.
              - destruct (valid_block_dec mc'' b1) as [Hvalidmc'' | Hinvalidmc''];
                first by assumption.
                destruct (valid_block_dec mcj' b1) as [Hvalidmcj' | Hinvalidmcj'];
                  assert (Hcontra := domain_invalid (weak_obs_eq (strong_obs Htsim')));
                  assert (Hinvalid: ~ Mem.valid_block
                                      (restrPermMap (memCompC'' i pfci'')) b1)
                    by (intros Hcontra2;
                          by apply restrPermMap_valid in Hcontra2);
                  specialize (Hcontra _ Hinvalid);
                    by congruence.
            } split.
            { (* synced *)
              intros Hsynced'.
              assert (Hlst :[seq x <- [seq x <- xs | x != i] | x == j] =
                            [seq x <- xs | x == j]) by (by eapply filter_neq_eq).
              rewrite Hlst in Hsynced'.
              rewrite Hsynced' in Hexecij.
              inversion Hexecij; subst;
              [|simpl in HschedN; inversion HschedN; subst; discriminate].
              rewrite Hsynced' in Hexecj.
              specialize (Hsyncedj Hsynced'). subst fj.
              extensionality b.
              destruct (valid_block_dec mc b) as [Hvalidmc | Hinvalidmc].
              - assert (Hfb := (domain_valid HsimWeak) b Hvalidmc).
                destruct Hfb as [b' Hfb].
                rewrite Hfb. by apply Hincr in Hfb.
              - destruct (valid_block_dec mcj' b) as [Hvalidmcj' | Hinvalidmcj'];
                first by reflexivity.
                assert (Hinvdomain := domain_invalid (weak_obs_eq (strong_obs Htsim))).
                assert (Hinvalidmcji': ~ Mem.valid_block (restrPermMap (memCompC' i pfc')) b)
                  by (intros Hcontra; by apply restrPermMap_valid in Hcontra).
                  by eauto.
            } split.
            { (* tpc'' can step in a fine grained way for thread j *)
                by rewrite filter_neq_eq.
            } split.
            { (*strong simulation between mcj' and mf' *)
              intros pfcj' Hcompcj'. pf_cleanup.
              constructor.
              - assert (Hctlij := code_eq Hsimij).
                assert (Hctljj := code_eq Htsimj).
                subst.
                rewrite Hctlij in Hctljj.
                erewrite <- gsoThreadC_suspendF with (cntj := pffj) (cntj' := pffj');
                  by eauto.
              - (*mem_obs_eq between thread-j on mij=mcj' and on mff'*)

                (* Before going into the actual proof, some assertions about
                   how the permissions in the various proofs relate.
                   Again we should point at a figure somewhere. *)

                (* For a block that's valid in mc, j-permissions of mcj'
                         and mcj are equal *)
                assert (HpermC_mc_block: forall b1 ofs,
                           Mem.valid_block mc b1 ->
                           permission_at (restrPermMap (Hcompij j pfij))
                                         b1 ofs Cur =
                           permission_at (restrPermMap (Hcompjj j pfcjj))
                                         b1 ofs Cur).
                { intros b1 ofs Hvalidmc.
                  unfold inject_incr in Hincr'.
                  specialize (Hincr' b1 b1 0%Z).
                  destruct (valid_block_dec mc b1); try by exfalso.
                  simpl in Hincr'.
                  specialize (Hincr' (Logic.eq_refl _)).
                  assert (HpermC_lt :=
                            (perm_obs_weak (weak_obs_eq (strong_obs Hsimij)))
                              b1 b1 ofs Hincr').
                  assert (HpermC_gt :=
                            (perm_obs_strong (strong_obs Hsimij))
                              b1 b1 ofs Hincr').
                  eapply perm_order_antisym; eauto.
                }
                (* j-permissions of mcj are higher than mf*)
                assert (HpermF_mcj :=
                          perm_obs_weak (weak_obs_eq (strong_obs Htsimj))).

                (* also j-permissions of mcj are lower than mf*)
                assert (Hpermmcj_F := perm_obs_strong (strong_obs Htsimj)).
                
                (* The permission of j at an i-block in mci is
                   empty. We can deduce that by the fact that mc steps
                   to mc'' with i-steps hence the permissions of
                   thread-j will remain empty and then mc'' steps to
                   mcj' and the permissions will remain empty by
                   decay*)
                assert (Hpermj_mc'':
                          forall b1 ofs,
                            ~ Mem.valid_block mc b1 ->
                            Mem.valid_block mc'' b1 ->
                            permission_at (restrPermMap (memCompC'' _ pfcj''))
                                          b1 ofs Cur = None).
                { intros b1 ofs Hinvalidmc Hvalidmc''.
                  (* Proof that the permission at b1 in mc|j is empty *)
                  assert (Hinitp:
                            permission_at (restrPermMap (HmemCompC _ pfcj)) b1 ofs Cur = None).
                  { apply Mem.nextblock_noaccess with (k := Max) (ofs := ofs) in Hinvalidmc.
                    assert (Hlt := HmemCompC _ pfcj b1 ofs).
                    rewrite getMaxPerm_correct in Hlt.
                    unfold permission_at in Hlt. rewrite Hinvalidmc in Hlt.
                    simpl in Hlt.
                    rewrite restrPermMap_Cur.
                    destruct ((getThreadR pfcj) # b1 ofs); by tauto.
                  }
                  (* Proof that internal execution on thread i
                  preserves these empty permissions*)
                  assert (pfcj': containsThread tpc' j)
                    by (eapply containsThread_internal_execution; eauto).
                  assert (Hp': permission_at (restrPermMap (memCompC' _ pfcj'))
                                             b1 ofs Cur = None).
                  { rewrite restrPermMap_Cur.
                    erewrite <- gsoThreadR_execution with (pfj := pfcj); eauto.
                    rewrite restrPermMap_Cur in Hinitp. by assumption.
                  }
                  rewrite restrPermMap_Cur.
                  erewrite <- gsoThreadR_suspendC with (cntj:= pfcj'); eauto.
                  rewrite restrPermMap_Cur in Hp'.
                    by assumption.
                }

                (* The permission of j at an i-block in mcij/mcj' is empty*)
                assert (Hpermj_mcj': forall b1 ofs,
                           ~ Mem.valid_block mc b1 ->
                           Mem.valid_block mc'' b1 ->
                           permission_at
                             (restrPermMap (Hcompij j pfij)) b1 ofs Cur = None).
                { (* Proof: By the fact that this block is allocated
                           by i, we know that the permission of thread
                           j on memory mc'' will be empty. Moreover by
                           the decay predicate, mcj' will have the
                           same permission as mc'' on this block
                           (since valid blocks cannot increase their
                           permissions) *)
                  intros b1 ofs Hinvalidmc Hvalidmc''.
                  specialize (Hpermj_mc'' b1 ofs Hinvalidmc Hvalidmc'').
                  unfold permission_at in Hpermj_mc''.
                  erewrite restrPermMap_Cur.
                  assert (Hdecay := internal_execution_decay).
                  specialize (Hdecay _ _ _ _ _ _ pfcj'' pfij memCompC'' Hcompij Hexecij).
                  unfold decay in Hdecay.
                  apply decay_decay' in Hdecay.
                  specialize (Hdecay b1 ofs).
                  destruct Hdecay as [_ Hold].
                  erewrite restrPermMap_valid in Hold.
                  specialize (Hold Hvalidmc'').
                  destruct Hold as [[Hcontra _] | Heq]; first by congruence.
                  rewrite Hpermj_mc'' in Heq.
                  assert (Hperm_at := restrPermMap_Cur (Hcompij j pfij) b1 ofs).
                  unfold permission_at in Hperm_at. by rewrite Hperm_at in Heq.
                }

                (* The permission of j at an i-block in mf is empty *)
                assert (Hpermj_eqF: forall b1 b2 ofs,
                           ~ Mem.valid_block mc b1 ->
                           Mem.valid_block mc'' b1 ->
                           fi b1 = Some (b2, 0%Z) ->
                           permission_at (restrPermMap (memCompF' j pffj'))
                                         b2 ofs Cur = None).
                { (* Proof is straightforward by the blocks owned by i invariant*)
                  intros b1 b2 ofs Hinvalidmc Hvalidmc'' Hfi.
                  rewrite restrPermMap_Cur.
                  erewrite <- gsoThreadR_suspendF with (cntj := pffj) by eauto.
                  assert (Hf := (domain_invalid HsimWeak)).
                  specialize (Hf b1).
                  erewrite restrPermMap_valid in Hf. 
                  eapply Hownedi; by eauto.
                }
                
                (* The j-permission of a j-block at mcj is equal to the 
                   permission at mcj'*)
                assert (Hpermmcj_mcj': forall b1' b1 ofs,
                           fij b1' = Some (b1, 0%Z) ->
                           permission_at (restrPermMap (Hcompjj j pfcjj))
                                         b1' ofs Cur =
                           permission_at (restrPermMap (Hcompij j pfij))
                                         b1 ofs Cur).
                { intros b1' b1 ofs Hfij. 
                  assert (Hperm_lt :=
                            (perm_obs_weak (weak_obs_eq (strong_obs Hsimij)))
                              b1' b1 ofs Hfij).
                  assert (Hperm_gt :=
                            (perm_obs_strong ((strong_obs Hsimij)))
                              b1' b1 ofs Hfij).
                  eapply perm_order_antisym; eauto.
                }
                subst f'.
                constructor.
                { (* weak obs eq *)
                  constructor.
                  - (*invalid domain of f' *)
                    intros b Hinvalid.
                    assert (Hinvalidmc'': ~ Mem.valid_block mc'' b)
                      by (intros Hcontra;
                           eapply internal_execution_valid with (m' := mcj')
                            in Hcontra;
                           eauto).
                    assert (Hinvalidmc: ~ Mem.valid_block mc b)
                      by (intros Hcontra;
                           eapply internal_execution_valid with (m' := mc'')
                            in Hcontra;
                           eauto).
                    repeat match goal with
                           | [|- context[match ?Expr with _ => _ end ]] =>
                             destruct Expr; first by exfalso
                           end.
                    reflexivity.
                  - (*valid domain of f'*)
                    intros b1 Hvalid.
                    erewrite restrPermMap_valid in Hvalid.
                    destruct (valid_block_dec mc b1) as [Hvalidmc | Hinvalidmc].
                    + assert (Hf := (domain_valid HsimWeak) b1).
                      erewrite restrPermMap_valid in Hf.
                      destruct (Hf Hvalidmc) as [b2 Hf_val].
                      apply Hincrj in Hf_val.
                      eexists; eassumption.
                    + destruct (valid_block_dec mc'' b1)
                        as [Hvalidmc'' | Hinvalidmc''].
                      * assert (Hfi := (domain_valid
                                          (weak_obs_eq (strong_obs Htsim'))) b1).
                        erewrite restrPermMap_valid in Hfi.
                        eauto.
                      * destruct (valid_block_dec mcj' b1); try (by exfalso).
                        specialize (Hinverse b1 Hvalid Hinvalidmc'').
                        destruct Hinverse as [b2 [Hg [Hfij _]]].
                        assert (Hdomainij :=
                                  domain_invalid (weak_obs_eq (strong_obs Hsimij))).
                        specialize (Hdomainij b2).
                        erewrite restrPermMap_valid in Hdomainij.
                        destruct (valid_block_dec mcj b2)
                          as [Hvalidmcj | Hinvalidmcj].
                        assert (Hfj := (domain_valid
                                          (weak_obs_eq (strong_obs Htsimj))) b2).
                        erewrite restrPermMap_valid in Hfj.
                        destruct (Hfj Hvalidmcj) as [b2' Hfj'].
                        exists b2'.
                          by rewrite Hg.
                          exfalso.
                          specialize (Hdomainij Hinvalidmcj).
                            by congruence.
                  - (* valid codomain of f'*)
                    intros b1 b2 Hf'.
                    assert (Hfj_codomain := codomain_valid (weak_obs_eq (strong_obs Htsimj))).
                    assert (Hfi_codomain := codomain_valid (weak_obs_eq (strong_obs Htsim))).
                    erewrite restrPermMap_valid in *.
                    repeat match goal with
                           | [H: context[match valid_block_dec ?M ?B with
                                         | _ => _ end] |- _] =>
                             destruct (valid_block_dec M B)
                           end; try discriminate.
                    specialize (Hfj_codomain b1 b2);
                      erewrite restrPermMap_valid in *.
                    eauto.
                    specialize (Hfi_codomain b1 b2);
                      erewrite restrPermMap_valid in *.
                    eauto.
                    specialize (Hinverse _ v n0).
                    destruct Hinverse as [? [Hg [Hfij ?]]].
                    rewrite Hg in Hf'.
                    specialize (Hfj_codomain _ _ Hf').
                    erewrite restrPermMap_valid in *.
                      by eauto.
                  - (* permissions of mcj' are higher than mf *)
                    intros b1 b2 ofs Hf'.
                    destruct (valid_block_dec mc b1) as [Hvalidmc | Hinvalidmc].
                    { (*case it's a block that's valid in mc*)
                      specialize (HpermC_mc_block b1 ofs Hvalidmc).
                      specialize (HpermF_mcj b1 b2 ofs Hf').
                      rewrite <- HpermC_mc_block in HpermF_mcj.
                      do 2 erewrite restrPermMap_Cur in *.
                      erewrite <- gsoThreadR_suspendF
                      with (cntj := pffj) (cntj' := pffj'); eauto.
                    }
                    { (*case it's a block that's invalid in mc*)
                      destruct (valid_block_dec mc'' b1)
                        as [Hvalidmc'' | Hinvalidmc''].
                      (*case it's a block that's valid in mc'' (an i-block)*)
                      specialize (Hpermj_eqF _ _ ofs Hinvalidmc Hvalidmc'' Hf').
                      rewrite Hpermj_eqF.
                      specialize (Hpermj_mcj' b1 ofs Hinvalidmc Hvalidmc'').
                      rewrite Hpermj_mcj'.
                      simpl; by constructor.
                      (*case it's a block that's invalid in mc'' *)
                      destruct (valid_block_dec mcj')
                        as [Hvalidmcj' | Hinvalidmcj']; try discriminate.
                      specialize (Hinverse b1 Hvalidmcj' Hinvalidmc'').
                      destruct Hinverse as [b1' [Hg [Hfij Hfid]]].
                      rewrite Hg in Hf'.
                      specialize (HpermF_mcj b1' b2 ofs Hf').
                      specialize (Hpermmcj_F b1' b2 ofs Hf').
                      replace (permission_at (restrPermMap
                                                (memCompF' j pffj')) b2 ofs Cur)
                      with ((getThreadR pffj') # b2 ofs)
                        by (rewrite restrPermMap_Cur; reflexivity).
                      erewrite <- gsoThreadR_suspendF
                      with (cntj := pffj) (cntj' := pffj'); eauto.
                      replace ((getThreadR pffj) # b2 ofs)
                      with
                      (permission_at (restrPermMap
                                        (mem_compf Hsim pffj)) b2 ofs Cur)
                        by (rewrite restrPermMap_Cur; reflexivity).
                      specialize (Hpermmcj_mcj' _ _ ofs Hfij).
                      rewrite <- Hpermmcj_mcj'.
                        by assumption.
                    }
                }
                { (* strong_perm_obs *)
                  intros b1 b2 ofs Hf'.
                  (* the permissions of mf' and mf are the same,
                     suspend step does not touch the memory*)
                  rewrite restrPermMap_Cur.
                    erewrite <- gsoThreadR_suspendF
                  with (cntj := pffj) (cntj' := pffj'); eauto.
                  rewrite <- restrPermMap_Cur with (Hlt := mem_compf Hsim pffj).
                  destruct (valid_block_dec mc b1) as [Hvalidmc | Hinvalidmc].
                  - (* b is a valid block in mc*)
                    specialize (HpermC_mc_block _ ofs Hvalidmc).
                    specialize (Hpermmcj_F _ _ ofs Hf').
                    rewrite <- HpermC_mc_block in Hpermmcj_F.
                      by assumption.
                  - destruct (valid_block_dec mc'' b1)
                      as [Hvalidmc'' | Hinvalidmc''].
                    + (* b1 is an i-block (allocated by thread i) *)
                      specialize (Hpermj_mcj' _ ofs Hinvalidmc Hvalidmc'').
                      rewrite Hpermj_mcj'.
                      match goal with
                      | [|- Mem.perm_order'' ?Expr _] =>
                        destruct Expr
                      end; simpl; auto.
                    + destruct (valid_block_dec mcj' b1) as [Hvalidmcj'|?];
                      try discriminate.
                      specialize (Hinverse b1 Hvalidmcj' Hinvalidmc'').
                      destruct Hinverse as [b1' [Hg [Hfij _]]].
                      rewrite Hg in Hf'.
                      specialize (Hpermmcj_mcj' _ _ ofs Hfij).
                      rewrite <- Hpermmcj_mcj'.
                        by eauto.
                }
                { (* val_obs_eq *)
                  intros b1 b2 ofs Hf' Hreadable.
                  simpl.
                  assert (Hvalmcj_mcj' := val_obs_eq (strong_obs Hsimij));
                    simpl in Hvalmcj_mcj'.
                  assert (Hvalmcj_mf := (val_obs_eq (strong_obs Htsimj)));
                    simpl in Hvalmcj_mf. 
                  destruct (valid_block_dec mc b1) as [Hvalidmc | Hinvalidmc]
                                                        eqn:Hvalidmcdec.
                  - (* Value of a block that is valid in mc *)
                    (* Idea: this block is mapped between mcj and mcj' by id
                       and from mcj to mf by fj. Hence we can reuse fj *)
                    assert (Hincr'_b1 := Hincr' b1 b1 0%Z).
                    rewrite Hvalidmcdec in Hincr'_b1. simpl in Hincr'_b1.
                    specialize (Hincr'_b1 (Logic.eq_refl _)).
                    assert (Hvalmcj_mcj'_b1 := Hvalmcj_mcj' _ _ ofs Hincr'_b1).
                    assert (Hvalmcj_mf_b1 := Hvalmcj_mf _ _ ofs Hf').
                    unfold Mem.perm in Hreadable, Hvalmcj_mcj'_b1, Hvalmcj_mf_b1.
                    assert (Hreadable' := Hpermmcj_mcj' _ _ ofs Hincr'_b1).
                    unfold permission_at in Hreadable'.
                    rewrite <- Hreadable' in Hreadable.
                    specialize (Hvalmcj_mf_b1 Hreadable).
                    specialize (Hvalmcj_mcj'_b1 Hreadable).
                    inversion Hvalmcj_mcj'_b1 as
                        [n Hn_mcj Hn_mcj' | vj vj' q1 n Hval_obsjj' Hvj Hvj'| Hundef_mcj Hmv_mcj'].
                    + rewrite <- Hn_mcj in Hvalmcj_mf_b1.
                      inversion Hvalmcj_mf_b1 as [n0 Heq Hn_mf| |];
                        first by constructor.
                    + (* Fragments case *)
                      rewrite <- Hvj in Hvalmcj_mf_b1.
                      inversion Hvalmcj_mf_b1 as [| vj0 vf q n0 Hval_obsjf Hvj0 Hvf |];
                        subst vj0 q1 n0.
                      constructor.
                      inversion Hval_obsjj' as [| | | | bpj1 bpj'2 ofsp Hfijp|]; subst;
                      inversion Hval_obsjf as [| | | | bpj0 bpf2 ofspf Hf'p|];
                      try subst bpj0; subst; try by constructor.
                      clear Hval_obsjf Hval_obsjj' Hvf Hvj.
                      constructor.
                      destruct (valid_block_dec mc bpj1) as [Hvalidmcbpj1 | Hinvalidmcbpj1]
                                                              eqn:Hdecbpj1.
                      { assert (Hincr'_bpj1 := Hincr' bpj1 bpj1 0%Z).
                        rewrite Hdecbpj1 in Hincr'_bpj1. simpl in Hincr'_bpj1.
                        specialize (Hincr'_bpj1 (Logic.eq_refl _)).
                        rewrite Hincr'_bpj1 in Hfijp; inversion Hfijp; subst bpj'2.
                        clear Hfijp.
                        rewrite Hdecbpj1. by assumption.
                      }
                      { (* here it is usefulto have inject seperation for fij*)
                        unfold inject_separated in Hsep.
                        specialize (Hsep bpj1 bpj'2 0%Z).
                        rewrite Hdecbpj1 in Hsep.
                        simpl in Hsep. specialize (Hsep (Logic.eq_refl _) Hfijp).
                        destruct Hsep as [_ Hinvalidmc''bpj'2].
                        assert (Hinvalidbmcpj'2: ~ Mem.valid_block mc bpj'2).
                        { intros Hcontra.
                          eapply internal_execution_valid with
                          (b := bpj'2) (m' := mc'') in Hcontra;
                            by eauto.
                        }
                        destruct (valid_block_dec mc bpj'2) as
                            [Hvalidmcbpj'2 | Hinvalidmcbpj'2];
                          first (by exfalso; auto).
                        destruct (valid_block_dec mc'' bpj'2) as [? | _];
                          first by (exfalso; auto).
                        destruct (valid_block_dec mcj' bpj'2) as [Hvalidmcj'bpj'2 | Hcontra].
                        specialize (Hinverse _ Hvalidmcj'bpj'2 Hinvalidmc''bpj'2).
                        destruct Hinverse as [b0 [Hg [Hfij0 Hfid0]]].
                        rewrite Hg.
                        clear HpermC_mc_block HpermF_mcj Hpermmcj_F Hpermj_mc'' Hreadable'
                              Hreadable   Hpermmcj_mcj'   Hpermj_eqF    Hvj'.
                        (* NOTE: i need injectivity for the newly
                           (Separated) blocks. So fij bpj1 =  fij b0
                           imply b0 = bpj1. This is possible *)
                        clear Hdecbpj1.
                        apply (domain_invalid (weak_obs_eq (strong_obs Hsim_c_ci)))
                          in Hinvalidmcbpj1.
                        specialize (Hinjective _ _ _ Hfid0 Hinvalidmcbpj1 Hfij0 Hfijp).
                        subst b0. by assumption.
                        apply (codomain_valid (weak_obs_eq (strong_obs Hsimij))) in Hfijp.
                        erewrite restrPermMap_valid in Hfijp. by exfalso.
                      }
                      rewrite <- Hundef_mcj in Hvalmcj_mf_b1.
                      inversion Hvalmcj_mf_b1.
                        by constructor.
                  - (* Notice that this case is exactly the same as
                       above.  What changes is in which memory region
                       the pointer is in, but the proof about the
                       pointer itself is the same.  TODO: can we merge
                       the two cases? I think no, but need to check
                       again *)

                    destruct (valid_block_dec mc'' b1) as [Hvalidmc'' | Hinvalidmc''].
                    specialize (Hpermj_mcj' _ ofs Hinvalidmc Hvalidmc'').
                    unfold Mem.perm in Hreadable.
                    unfold permission_at in Hpermj_mcj'.
                    rewrite Hpermj_mcj' in Hreadable.
                    simpl in Hreadable;
                      by exfalso.
                    destruct (valid_block_dec mcj' b1) as [Hvalidmcj' | ?];
                      try discriminate.
                    destruct (Hinverse _ Hvalidmcj' Hinvalidmc'') as [b0 [Hg [Hfij _]]].
                    rewrite Hg in Hf'.
                    assert (Hpermeq := Hpermmcj_mcj' _ _ ofs Hfij).
                    assert (Hreadable': Mem.perm (restrPermMap (Hcompjj j pfcjj))
                                                 b0 ofs Cur Readable)
                      by (unfold Mem.perm in *; unfold permission_at in Hpermeq;
                            by rewrite Hpermeq).
                    specialize (Hvalmcj_mcj' _ _ ofs Hfij Hreadable').
                    specialize (Hvalmcj_mf _ _ ofs Hf' Hreadable').
                    clear Hreadable Hreadable' Hpermeq Hpermmcj_mcj' Hpermj_eqF Hpermj_mcj'
                          Hpermj_mc'' Hpermmcj_F HpermF_mcj HpermC_mc_block.
                    inversion Hvalmcj_mcj' as
                        [n Hn_mcj Hn_mcj' | vj vj' q1 n Hval_obsjj' Hvj Hvj'| Hundef_mcj Hmv_mcj'].
                    + rewrite <- Hn_mcj in Hvalmcj_mf.
                      inversion Hvalmcj_mf as [n0 Heq Hn_mf| |];
                        first by constructor.
                    + (* Fragments case *)
                      rewrite <- Hvj in Hvalmcj_mf.
                      inversion Hvalmcj_mf as [| vj0 vf q n0 Hval_obsjf Hvj0 Hvf |];
                        subst vj0 q1 n0.
                      constructor.
                      inversion Hval_obsjj' as [| | | | bpj1 bpj'2 ofsp Hfijp|]; subst;
                      inversion Hval_obsjf as [| | | | bpj0 bpf2 ofspf Hf'p|];
                      try subst bpj0; subst; try by constructor.
                      clear Hval_obsjf Hval_obsjj' Hvf Hvj.
                      constructor.
                      destruct (valid_block_dec mc bpj1) as [Hvalidmcbpj1 | Hinvalidmcbpj1]
                                                              eqn:Hdecbpj1.
                      { assert (Hincr'_bpj1 := Hincr' bpj1 bpj1 0%Z).
                        rewrite Hdecbpj1 in Hincr'_bpj1. simpl in Hincr'_bpj1.
                        specialize (Hincr'_bpj1 (Logic.eq_refl _)).
                        rewrite Hincr'_bpj1 in Hfijp; inversion Hfijp; subst bpj'2.
                        clear Hfijp.
                        rewrite Hdecbpj1. by assumption.
                      }
                      { (* here it is usefulto have inject seperation for fij*)
                        unfold inject_separated in Hsep.
                        specialize (Hsep bpj1 bpj'2 0%Z).
                        rewrite Hdecbpj1 in Hsep.
                        simpl in Hsep. specialize (Hsep (Logic.eq_refl _) Hfijp).
                        destruct Hsep as [_ Hinvalidmc''bpj'2].
                        assert (Hinvalidbmcpj'2: ~ Mem.valid_block mc bpj'2).
                        { intros Hcontra.
                          eapply internal_execution_valid with
                          (b := bpj'2) (m' := mc'') in Hcontra;
                            by eauto.
                        }
                        destruct (valid_block_dec mc bpj'2) as
                            [Hvalidmcbpj'2 | Hinvalidmcbpj'2];
                          first (by exfalso; auto).
                        destruct (valid_block_dec mc'' bpj'2) as [? | _];
                          first by (exfalso; auto).
                        destruct (valid_block_dec mcj' bpj'2) as [Hvalidmcj'bpj'2 | Hcontra].
                        specialize (Hinverse _ Hvalidmcj'bpj'2 Hinvalidmc''bpj'2).
                        destruct Hinverse as [b0' [Hg' [Hfij0' Hfid0']]].
                        rewrite Hg'.
                        (* NOTE: i need injectivity for the newly
                           (Separated) blocks. So fij bpj1 and fij
                           imply b0 = bpj1. I can have that *)
                        clear Hdecbpj1.
                        apply (domain_invalid (weak_obs_eq (strong_obs Hsim_c_ci)))
                          in Hinvalidmcbpj1.
                        specialize (Hinjective _ _ _ Hfid0' Hinvalidmcbpj1 Hfij0' Hfijp).
                        subst b0'. by assumption.
                        apply (codomain_valid (weak_obs_eq (strong_obs Hsimij))) in Hfijp.
                        erewrite restrPermMap_valid in Hfijp. by exfalso.
                      }
                      rewrite <- Hundef_mcj in Hvalmcj_mf.
                      inversion Hvalmcj_mf.
                        by constructor.
                } 
            }
            { (* Proof that block ownership is preserved*)
              subst f'.
              intros k pffk' Hjk b1 b2 ofs Hf' Hfi.
              destruct (valid_block_dec mc b1) as [Hvalidmc | Hinvalidmc].
              - (* If b1 is valid in mc then it should be in f and
                since fi is an extension of f it should be in fi as
                well *)
                apply (domain_valid HsimWeak) in Hvalidmc.
                destruct Hvalidmc as [? Hf].
                apply Hincr in Hf. by congruence.
              - destruct (valid_block_dec mc'' b1) as [Hvalidmc'' | Hinvalidmc''];
                first by congruence.
                destruct (valid_block_dec mcj' b1) as [Hvalidmcj' | Hinvalidmcj'].
                destruct (Hinverse _ Hvalidmcj' Hinvalidmc'') as [b0 [Hg [Hfij ?]]].
                rewrite Hg in Hf'.
                unfold inject_separated in Hsep.
                specialize (Hsep _ _ _ H Hfij).
                destruct Hsep as [Hinvalidb0 _].
                apply (domain_invalid HsimWeak) in Hinvalidb0.
                assert (pffk: containsThread tpf k)
                  by (eapply suspendF_containsThread with (cnti := pff); eauto).
                specialize (Hownedj _ pffk Hjk _ _ ofs Hf' Hinvalidb0).
              erewrite <- gsoThreadR_suspendF with (cntj := pffk); eauto.
              by discriminate.
            }
          }
          }
        { (* Proof that the fine grained invariant is preserved *)
            by eapply suspendF_invariant with (pff := pff); eauto.
        }
        { (* Proof the max_inv is preserved *)
            by auto.
        }
      }
    Qed.
                      
            
End SimDefs.
End SimDefs.
