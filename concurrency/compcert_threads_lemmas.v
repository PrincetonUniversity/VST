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

Definition coarse_semantics:=
  myCoarseSemantics.MachineSemantics.

Definition fine_semantics:=
  myFineSemantics.MachineSemantics.


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
      injective: forall b1 b1' b2, f b1 = Some (b2,0%Z) ->
                              f b1' = Some (b2,0%Z) ->
                              b1 = b1';
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
      assert (cntj := cntUpdateC' _ _ _ (Krun c) ctn cntj').
      specialize (Hcompatible _ cnt).
      unfold getThreadR in *. auto.
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
                      internal_step_perm Hneq  pfj pfj0' Hcomp0' Hstep0 b ofs).
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

  End InternalSteps.
End InternalSteps.

Module SimDefs.

  Import Concur DryMachine MemObsEq.
  Import DryMachine.ThreadPool SEM.
  Import mySchedule CoreLanguage InternalSteps.
  Require Import sepcomp.closed_safety.
  
  Notation cstep := (cstep the_ge).
  Notation Sch := schedule.
  Notation cmachine_step := (@myCoarseSemantics.MachStep the_ge).
  Notation fmachine_step := (@myFineSemantics.MachStep the_ge).
  Notation CoarseSem := (myCoarseSemantics.MachineSemantics).
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
      rewrite H.  auto.
    Qed.

    
    Lemma containsThread_fstep :
      forall tp tp' m m' i (cnti: containsThread tp i)
        (Hinternal: cnti @ I)
        (Hstep: forall U,
            fmachine_step (i :: U, tp) m (U, tp') m'),
        containsThread tp' i.
    Proof.
      intros. specialize (Hstep empty).
      absurd_internal Hstep;
        [by apply cntUpdateC | by apply cntUpdate].
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
      
    Lemma fmachine_step_perm :
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
      Admitted.
     
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
    
    (** Proofs of internal step safety and simulation*)
    Lemma strong_tsim_internal:
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
    
    Lemma weak_tsim_internal:
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
        by (eapply containsThread_internal in pfc; eauto).
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
      destruct (strong_tsim_internal HmaxF HinvF Htsim Hstep')
        as [tpf' [mf' [fi' [HstepF [HmaxF' [Hincr' [Htsim' Howned']]]]]]].
      assert (pfc'': containsThread tpc'' i)
        by (eapply containsThread_internal_step; eauto).
      assert (pff': containsThread tpf' i)
        by admit.
      assert (memCompC'': mem_compatible tpc'' mc'').
      eapply internal_step_compatible with (Hcompatible := memCompC'); eauto.
      assert (memCompF': mem_compatible tpf' mf')
        by admit.
      exists tpf' mf'.
      split.
      (** Proof that the fine-grained execution steps *)
      assumption.
      (** Proof that the simulation is preserved*)
      clear HsafeC HcorestepN.
      eapply Build_sim with (mem_compc := HmemCompC) (mem_compf := memCompF').
      - admit.
      - apply (safeCoarse Hsim).
      - (** Proof of weak simulation between threads *)
        intros j pfcj pffj'.
        assert (pffj: containsThread tpf j)
          by admit. (*containsThread_backward for machine step *)
        eapply weak_tsim_internal with (pffi := pff); eauto.
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
              by admit. (* containsThread for machine step*)

            Lemma gsoThreadR_fstep:
              forall tp tp' m m' i j
                (Hneq: i <> j)
                (pfi: containsThread tp i)
                (pfj: containsThread tp j)
                (pfj': containsThread tp' j)
                (Hinternal: pfi @ I)
                (Hstep: forall U, fmachine_step (i :: U, tp) m (U, tp') m'),
                getThreadR pfj = getThreadR pfj'.
            Proof. Admitted.
            
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
            by admit. (*containsThread back for machine step*)
          destruct (HsimStrong j pfcj pffj)
            as [fj [tpcj' [mcj' [Hincrj [Hsyncedj [Hexecj [Htsimj Hownedj]]]]]]].
          exists fj tpcj' mcj'. split; auto. split; [ by auto| split; auto].
          split.
          (* difficult part: simulation between tpf' and tpcj' *)
          intros pfcj' memCompCj'.
          specialize (Htsimj pfcj' memCompCj').
          inversion Htsimj as [code_eqjj memObsEqj].
          constructor; first by
              (rewrite code_eqjj; admit). (* need gsoThreadC_step for fstep*)
            (*by (eapply gsoThreadC_step; eauto).*)
          constructor. (*mem_obs_eq proof*)
          { constructor.
            - apply (domain_invalid (weak_obs_eq memObsEqj)).
            - apply (domain_valid (weak_obs_eq memObsEqj)).
            - assert (Hcodomain := (codomain_valid (weak_obs_eq memObsEqj))).
              intros b1 b2 Hfj.
              specialize (Hcodomain b1 b2 Hfj).
              admit. (*lift valid block for fmachine_step*)
            - apply (injective (weak_obs_eq memObsEqj)).
            - intros b1 b2 ofs.
              rewrite <- fmachine_step_perm with
              (Hcomp := (mem_compf Hsim)) (U := empty) (i := i) (pfi := pff)
                                          (pfj := pffj)
                                          (Hcomp' := memCompF'); auto.
              apply (perm_obs_weak (weak_obs_eq memObsEqj)).
          }
          { intros b1 b2 ofs.
            rewrite <- fmachine_step_perm with
            (Hcomp := (mem_compf Hsim)) (i := i) (U := empty) (pfi := pff)
                                        (pfj := pffj) (Hcomp' := memCompF'); auto.
            apply (perm_obs_strong memObsEqj).
          }
          { intros b1 b2 ofs Hfj Hperm. unfold restrPermMap. simpl.
            assert (Hval := val_obs_eq memObsEqj).
            specialize (Hval b1 b2 ofs Hfj Hperm).
            unfold restrPermMap in Hval. simpl in Hval.
            assert (Hpermf: Mem.perm (restrPermMap (HmemCompF _ pffj))
                                     b2 ofs Cur Readable).
            { specialize (HstepF empty).
              assert (Hperm_eqf :=
                        fmachine_step_perm Heq pff pffj pffj' HmemCompF memCompF'
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
              eauto. 
          }
          (* block ownership *)
          intros k pffk' Hjk b1 b2 ofs Hfj Hf.
          assert (pffk: containsThread tpf k).
            by admit. (* containsThread_backward for executions*)
            specialize (Hownedj _ pffk Hjk b1 b2 ofs Hfj Hf).
            destruct (i == k) eqn:Hik; move/eqP:Hik=>Hik.
            - subst k.
              assert (pfcj': containsThread tpcj' j)
                by (eapply containsThread_internal; eauto).
              assert (Hcompcj': mem_compatible tpcj' mcj')
                by (eapply internal_execution_compatible with (tp := tpc) (m := mc);
                     eauto).
              specialize (Htsimj pfcj' Hcompcj').
              assert (Hcodomain := (codomain_valid (weak_obs_eq
                                                      (strong_obs Htsimj)))).
              specialize (Hcodomain _ _ Hfj).
              
            Lemma fmachine_decay :
              forall tp m tp' m' i (cnt: containsThread tp i)
                (Hinternal: cnt @ I)
                (Hcomp: mem_compatible tp m)
                (Hstep : forall U,
                    fmachine_step (i :: U, tp) m (U, tp') m'),
                decay (restrPermMap (Hcomp _ cnt)) m'.
            Admitted.

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
    Qed.

    (** Proof of simulation for stop steps *)

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

    Lemma suspend_step_compatible:
      forall (tp : thread_pool) (m : mem) (i : tid) (c : code)
        (ctn : containsThread tp i)
        (Hget: getThreadC ctn = Krun c)
        (Hcomp: mem_compatible tp m),
        mem_compatible (updThreadC ctn (Kstop c)) m.
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
      by apply suspend_step_compatible.
    Qed.

    Corollary suspendF_compatible:
      forall tp tp' m i (cnt: containsThread tp i)
        (Hcomp: mem_compatible tp m)
        (Hsuspend: myFineSemantics.suspend_thread cnt tp'),
        mem_compatible tp' m.
    Proof.
      intros. inversion Hsuspend; subst.
        by apply suspend_step_compatible.
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

    Lemma suspend_step_invariantF:
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
        (* inject_separated f f' m1 m1' *)
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
          as [m2' [f' [Hcorestep' [Hobs_eq [Hincr [Hseparated Hinverse]]]]]].
        exists (updThread pf1j' (Krun c') (getCurPerm m2')) m2' f'.
        assert (Hinternal':
                  internal_step pf1j' Hcomp1'
                                (updThread pf1j' (Krun c') (getCurPerm m2')) m2')
          by (left; econstructor; eauto).
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
        split; first by
            (exists (fun b : block => Some (b, 0%Z)); intros; by exfalso).
        assert (pf2j := containsThread_internal_step Hstep pf1j).
        assert (pf2j' := containsThread_internal_step Hinternal' pf1j').
        assert (Hcomp2 := internal_step_compatible Hstep).
        assert (Hcomp2' := internal_step_compatible Hinternal').
        exists pf2j pf2j' Hcomp2 Hcomp2'.
        constructor; first by do 2 rewrite gssThreadCC.
        destruct Hmem_obs_eq
          as [[Hinvalid' Hvalid' Hinj' Hcodomain Hweak_perm] Hstrong_perm Hval].
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
        (Hsim: strong_tsim f pf1j pf1j' Hcomp1 Hcomp1')
        (Hexec: internal_execution [seq x <- xs | x == j] tp1 m1 tp2 m2),
      exists tp2' m2' f',
        internal_execution [seq x <- xs | x == j] tp1' m1' tp2' m2' /\
        inject_incr f f' /\
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
     (* intros.
      generalize dependent tp1.
      generalize dependent m1.
      induction xs as [|x xs]; simpl; intros.
      - inversion Hexec; subst.
        exists tp1' m1' f.
        split; first by constructor.
        split; first by auto.
        split. exists (fun b : block => Some (b,0%Z)). intros. by exfalso.
        do 4 eexists; eauto.
        simpl in HschedN; inversion HschedN.
      - destruct (x == j) eqn:Hxj; move/eqP:Hxj=>Hxj.
        + subst x. inversion Hexec; subst.
          simpl in Htrans. simpl in HschedN;
            inversion HschedN; subst; clear HschedN. *)
    Admitted.

      (* this can be a lemma on ctl injections and suspend_thread only,
         TODO: make the change at some point*)

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
    
    Lemma sim_suspend : sim_suspend_def.
    Proof.
      unfold sim_suspend_def.
      intros.
      inversion Hsim as
          [HnumThreads HmemCompC HmemCompF HsafeC HsimWeak HsimStrong HinvF HmaxF].
      assert (pfc: containsThread tpc i)
        by (eapply containsThread_eq; eauto).
      destruct (HsimStrong i pfc pff)
        as [fi [tpc' [mc' [Hincr [Hsynced [Hexec [Htsim Hownedi]]]]]]];
        clear HsimStrong.
      assert (pfc': containsThread tpc' i)
        by (eapply containsThread_internal in pfc; eauto).
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

          Lemma suspend_step_det:
            forall tp tp' tp'' i (cnt: containsThread tp i)
              (Hsuspend: cnt @ S)
              (Hstep: myCoarseSemantics.suspend_thread cnt tp')
              (Hstep': myCoarseSemantics.suspend_thread cnt tp''),
              tp' = tp''.
          Admitted.
          destruct (suspend_step_inverse pfc' Hstop_pfc' Hstep'0)
            as [? [? [_ Hsuspend]]]; subst U' mc''0.
          assert (tpc''0 = tpc'')
            by (eapply suspend_step_det; eauto);
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
          { (* fi is injective *)
              by apply (injective (weak_obs_eq (strong_obs Htsim))).
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
                                            b2 ofs Cur).
            { inversion HstepF; subst.
              assert (HinvF': invariant (updThreadC ctn (Kstop c))) by admit.
              assert (Hrestr' := restrPermMap_correct (memCompF' _ pffj')).
              destruct (Hrestr' b2 ofs) as [_ Hrestr_cur']; clear Hrestr'.
              assert (Hrestr := restrPermMap_correct (HmemCompF _ pffj)).
              destruct (Hrestr b2 ofs) as [_ Hrestr_cur]; clear Hrestr.
              rewrite Hrestr_cur' Hrestr_cur.
                by pf_cleanup.
            }
            rewrite Hperm_eqF.
            (* Likewise for the coarse-grained machine*)
            (* TODO: factor these two into gThreadR_suspend lemmas*)
            assert (pfcj': containsThread tpc' j) by admit.
            assert (Hperm_eqC: permission_at (restrPermMap (memCompC'' _ pfcj''))
                                             b1 ofs Cur =
                               permission_at (restrPermMap (memCompC' _ pfcj'))
                                             b1 ofs Cur).
            { inversion HsuspendC; subst.
              assert (HinvC'': invariant (updThreadC ctn (Kstop c))) by admit.
              assert (Hrestr' := restrPermMap_correct (memCompC'' _ pfcj'')).
              destruct (Hrestr' b1 ofs) as [_ Hrestr_cur']; clear Hrestr'.
              assert (Hrestr := restrPermMap_correct (memCompC' _ pfcj')).
              destruct (Hrestr b1 ofs) as [_ Hrestr_cur]; clear Hrestr.
              rewrite Hrestr_cur' Hrestr_cur.
                by pf_cleanup.
            }
            rewrite Hperm_eqC.
            clear Hperm_eqF Hperm_eqC HcorestepN HstepF Hstep'.
            destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
            { (* Case j = i *)
              subst.
              clear - Htsim Hfi.
              destruct Htsim as [_ Hstrong]; destruct Hstrong as [Hweak _ _];
              destruct Hweak as [_ _ _ _ Hperm_weak].
              specialize (Hperm_weak b1 b2 ofs Hfi).
                by pf_cleanup.
            }
            { (* Case j <> i *)
              assert (pfcj: containsThread tpc j) by admit.  (*TODO: containsThread backward for execution*)
              specialize (HsimWeak _ pfcj pffj). 
              inversion HsimWeak as [Hinvdomain Hdomain Hcodomain Hinj Hobs_weak].
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
            (* TODO: containsThread for suspend step and transitivity*)
            assert (pfci'': containsThread tpc'' i) by admit. 
            assert (pffi': containsThread tpf' i) by admit.
            specialize (Htsim' memCompC'' memCompF' pfci'' pffi').
            assert (pfcj: containsThread tpc j) by admit.
            (* The original <tpc, mc> strongly injects into <tpc'',mc''> where
               <tpc, mc> -->i <tpc', mc'> -->iS <tpc'',mc'>  with the id map*)
            (*TODO: This is the strong simulation with id function. Factor it out
                   as a separate lemma.*)

            assert (Hsim_c_ci: strong_tsim (fun b => if valid_block_dec mc b then
                                                    Some (b,0%Z) else None)
                                           pfcj pfcj'' HmemCompC memCompC'').
            { assert (pfcj': containsThread tpc' j) by admit.
              (*TODO: containsThread backward for suspend step*)
              constructor.
              - (* codes are equal*)
                assert (Hcode := gsoThreadC_suspendC pfcj' pfcj'' Hij HsuspendC).
                rewrite <- Hcode.
                by erewrite gsoThreadC_exec with (pfj' := pfcj'); eauto.
              - (* mem_obs_eq *)
                constructor.
                + (*weak_mem_obs_eq*)
                  constructor.
                  * (*invalid domain of fid*)
                    intros b Hinvalid.
                    destruct (valid_block_dec mc b) as [Hcontra | ?];
                      [unfold Mem.valid_block in *;
                        rewrite restrPermMap_nextblock in Hinvalid;
                          by exfalso | by reflexivity].
                  * (*valid domain of fid*)
                    intros b Hvalid.
                    by destruct (valid_block_dec mc b);
                      [exists b; by reflexivity | unfold Mem.valid_block in *;
                           rewrite restrPermMap_nextblock in Hvalid; by exfalso].
                  * (*codomain of fid *)
                    intros b1 b2 Hfid.
                    destruct (valid_block_dec mc b1); simpl in Hfid;
                    try discriminate.
                    inversion Hfid; subst.
                    erewrite restrPermMap_valid.
                    
                    Lemma internal_execution_valid :
                      forall tp m tp' m' xs
                        (Hexec: internal_execution xs tp m tp' m'),
                      forall b, Mem.valid_block m b -> Mem.valid_block m' b.
                    Admitted.
                    
                    eapply internal_execution_valid; by eauto.
                  * (* fid is injective *)
                    intros b1 b1' b2 Hb1 Hb1'.
                    destruct (valid_block_dec mc b1), (valid_block_dec mc b1');
                      simpl in Hb1, Hb1'; inversion Hb1; inversion Hb1';
                        by subst. 
                  * (* Permissions of memc are higher than memc''*)
                    intros b1 b2 ofs Hfid.
                    destruct (valid_block_dec mc b1); simpl in Hfid;
                    try discriminate.
                    inversion Hfid; subst.
                    do 2 rewrite restrPermMap_Cur.
                    erewrite <- gsoThreadR_suspendC with
                    (cntj' := pfcj'') (cntj := pfcj') by eauto.
                    erewrite <- gsoThreadR_execution with (pfj' := pfcj')
                                                           (pfj := pfcj); eauto.
                    destruct ((getThreadR pfcj) # b2 ofs); simpl;
                    by constructor.
                + (* Permissions of memc'' are higher than mc*)
                  intros b1 b2 ofs Hfid.
                  destruct (valid_block_dec mc b1); simpl in Hfid;
                  try discriminate.
                  inversion Hfid; subst.
                  do 2 rewrite restrPermMap_Cur.
                  erewrite <- gsoThreadR_suspendC with
                  (cntj' := pfcj'') (cntj := pfcj') by eauto.
                  erewrite <- gsoThreadR_execution with (pfj' := pfcj')
                                                         (pfj := pfcj); eauto.
                  destruct ((getThreadR pfcj) # b2 ofs); simpl;
                  by constructor.
                + (* j-Values of mc and mc'' are equal up to injection*)
                  intros b1 b2 ofs Hfid Hreadable.
                  destruct (valid_block_dec mc b1); simpl in Hfid;
                  try discriminate.
                  inversion Hfid; subst.
                  simpl.
                  erewrite <- internal_exec_disjoint_val
                  with (tp := tpc) (xs := xs) (tp' := tpc') (m' := mc''); eauto.
                  destruct (Maps.ZMap.get ofs (Mem.mem_contents mc) # b2);
                    constructor.
                  destruct v0; try constructor.
                  admit. (* need the mem_wd invariant to show this*)
            }
            
            assert (pffj: containsThread tpf j) by admit.
            assert (Htsimj := (simStrong Hsim) j pfcj pffj).
            (* executing the internal steps for thread j gives us a strong 
             * simulation between the coarse and fine-grained states. *)
            destruct Htsimj as
                [fj [tpcj [mcj [Hincrj [Hsyncedj [Hexecj [Htsimj Hownedj]]]]]]].
            (* strong simulation between mcj and mcj', where mcj'
              mc -->i --> mci -->j mcj' *)
            assert (Hsimjj':= strong_tsim_execution xs Hsim_c_ci Hexecj).
            (* TODO: 4/5, probably strengthen strong_tsim_execution*)
            destruct Hsimjj'
              as [tpcj' [mcj' [fij [Hexecij [Hincr'
                                               [Hinverse Hsimjj']]]]]].
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
               Lemma internal_step_valid:
                 forall tp m tp' m' i (cnt: containsThread tp i)
                   (Hcomp: mem_compatible tp m)
                   (Hstep: internal_step cnt Hcomp tp' m') b
                   (Hvalid: Mem.valid_block m b),
                   Mem.valid_block m' b.
               Admitted.

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
                    by (eapply containsThread_internal; eauto).
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
                  - (* f' is injective *)
                    intros b1 b1' b2 Hb1 Hb1'.
                    repeat match goal with
                           | [H: context[match valid_block_dec ?M ?B with
                                         | _ => _ end] |- _] =>
                             destruct (valid_block_dec M B)
                           end;
                      try (by (eapply (injective (weak_obs_eq (strong_obs Htsimj)));
                                eauto)).
                    (* this part of the proof, is ugly (and a bit brute-forced*)
                    + assert (H := domain_valid HsimWeak).
                      specialize (H b1'). erewrite restrPermMap_valid in H.
                      specialize (H v). destruct H as [b2' Hfb1'].
                      assert (b2 = b2')
                        by (apply Hincrj in Hfb1'; rewrite Hfb1' in Hb1';
                            inversion Hb1'; by subst); subst.
                      apply Hincr in Hfb1'.
                      eapply (injective (weak_obs_eq (strong_obs Htsim))); eauto.
                    + destruct (Hinverse b1 v0 n0) as [b0 [Hg [Hfij Hf]]].
                      rewrite Hg in Hb1.
                      assert (b1' = b0)
                        by (eapply (injective (weak_obs_eq (strong_obs Htsimj)));
                             eauto); subst b0.
                      destruct (valid_block_dec mc b1'); try congruence.
                      simpl in Hf. discriminate.
                    + assert (H := domain_valid HsimWeak).
                      specialize (H b1). erewrite restrPermMap_valid in H.
                      specialize (H v0). 
                      destruct H as [b2' Hfb1].
                      assert (b2 = b2')
                        by (apply Hincrj in Hfb1; rewrite Hfb1 in Hb1;
                            inversion Hb1; by subst); subst.
                      apply Hincr in Hfb1.
                      eapply (injective (weak_obs_eq (strong_obs Htsim))); eauto.
                    + eapply (injective (weak_obs_eq (strong_obs Htsim))); eauto.
                    + Focus 2.
                      destruct (Hinverse b1' v n0) as [b0 [Hg [Hfij Hf]]].
                      rewrite Hg in Hb1'.
                      assert (b1 = b0)
                       by (eapply (injective (weak_obs_eq (strong_obs Htsimj)));
                            eauto); subst b0.
                      destruct (valid_block_dec mc b1); try congruence.
                      simpl in Hf. discriminate.
                      admit. admit. admit. 
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
                        assert (Hsep: inject_separated
                                        (fun b : block =>
                                           if is_left (valid_block_dec mc b)
                                           then Some (b, 0%Z)
                                           else None) fij mc mc'') by admit.
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
                           (Separated) blocks. So fij bpj1 and fij
                           imply b0 = bpj1. I can have that *)
                        admit.
                        apply (codomain_valid (weak_obs_eq (strong_obs Hsimij))) in Hfijp.
                        erewrite restrPermMap_valid in Hfijp. by exfalso.
                      }
                      rewrite <- Hundef_mcj in Hvalmcj_mf_b1.
                      inversion Hvalmcj_mf_b1.
                        by constructor.
                  - destruct (valid_block_dec mc'' b1) as [Hvalidmc'' | Hinvalidmc''].
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
                        assert (Hsep: inject_separated
                                        (fun b : block =>
                                           if is_left (valid_block_dec mc b)
                                           then Some (b, 0%Z)
                                           else None) fij mc mc'') by admit.
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
                        destruct Hinverse as [b0' [Hg' [Hfij0' _]]].
                        rewrite Hg'.
                        (* NOTE: i need injectivity for the newly
                           (Separated) blocks. So fij bpj1 and fij
                           imply b0 = bpj1. I can have that *)
                        admit.
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
              admit. (*Contradiction *)
              destruct (valid_block_dec mc'' b1) as [Hvalidmc'' | Hinvalidmc''].
              admit. (*contradiction*)
              destruct (valid_block_dec mcj' b1) as [Hvalidmcj' | Hinvalidmcj'].
              destruct (Hinverse _ Hvalidmcj' Hinvalidmc'') as [b0 [Hg [Hfij ?]]].
              rewrite Hg in Hf'.
              assert (Hsep: inject_separated
                              (fun b : block =>
                                 if is_left (valid_block_dec mc b)
                                 then Some (b, 0%Z)
                                 else None) fij mc mc'') by admit.
              unfold inject_separated in Hsep.
              specialize (Hsep _ _ _ H Hfij).
              destruct Hsep as [Hinvalidb0 _].
              apply (domain_invalid HsimWeak) in Hinvalidb0.
              assert (pffk: containsThread tpf k) by admit.
              (*TODO: backward containsThread for susp*)
              specialize (Hownedj _ pffk Hjk _ _ ofs Hf' Hinvalidb0).
              erewrite <- gsoThreadR_suspendF with (cntj := pffk); eauto.
              by discriminate.
            }
          }
          }
        { (* Proof that the fine grained invariant is preserved *)
            by eapply suspend_step_invariantF with (pff := pff); eauto.
        }
        { (* Proof the max_inv is preserved *)
            by auto.
        } Grab Existential Variables. auto. auto. auto. auto. auto.
      }
    Qed.
                      
            

End SimDefs.
End SimDefs.

Module MachineSimulations.
  Section MachineSimulations.

    Import MemoryObs SimDefs ThreadPool Concur.
    Context {Sem : CoreSemantics mySem.G mySem.cT Mem.mem}.
    
    Notation thread_pool := (t mySem.cT).
    Variable the_ge : mySem.G.
    Notation fstep := ((corestep fine_semantics) the_ge).
    
    Context { cR : @CodeRen mySem.cT }.

    Inductive StepType : Type :=
    | Internal | Concurrent | Halted | Resume.
            
    Definition getStepType {i tp} (cnt : containsThread tp i) : StepType :=
      match getThreadC cnt with
      | Krun c => match halted the_sem c with
                 | Some _ => Halted
                 | None => Internal
                 end
      | Kstop c => Concurrent (* at_external = None -> contradiction by safety?*)
      | Kresume c => Resume
      end.

    Class MachineSimulation :=
      {      
        internal_inv : forall tp1 tp2 m1 m2 i sched
                         (cnt: containsThread tp1 i) (α : renaming),
          getStepType cnt = Internal \/ getStepType cnt = Resume ->
          fstep (i :: sched, tp1) m1 (sched, tp2) m2 ->
          forall j tp1' m1' α,
            i <> j ->
            sim tp1 tp1' m1 m1' j α ->
            sim tp2 tp1' m2 m1' j α;
      
        internal_sim : forall (tp1 tp2 tp1' : thread_pool) (m1 m2 m1' : mem) α
                         i (cnt: containsThread tp1 i) sched sched',
            getStepType cnt = Internal \/ getStepType cnt = Resume ->
            sim tp1 tp1' m1 m1' i α ->
            fstep (i :: sched, tp1) m1 (sched, tp2) m2 ->
            exists tp2' m2' α',
              fstep (i :: sched', tp1') m1' (sched', tp2') m2' /\
              (forall tid, sim tp1 tp1' m1 m1' tid α ->
                      sim tp2 tp2' m2 m2' tid α');        
        
        conc_sim : forall (tp1 tp2 tp1' : thread_pool) (m1 m2 m1' : mem) α
                     i (cnt: containsThread tp1 i) sched sched',
            getStepType cnt = Concurrent ->
            sim tp1 tp1' m1 m1' i α ->
            sim tp1 tp1' m1 m1' ls_id α ->
            sim tp1 tp1' m1 m1' sp_id α ->
            fstep (i :: sched, tp1) m1 (sched, tp2) m2 ->
            exists tp2' m2',
              fstep (i :: sched', tp1') m1' (sched', tp2') m2' /\
              (forall tid, sim tp1 tp1' m1 m1' tid α ->
                      sim tp2 tp2' m2 m2' tid α);

        swap:
          forall (tp1 tp2 tp3 tp1' : thread_pool) (m1 m2 m3 m1' : mem) α
            (i j : nat) (cnti: containsThread tp1 i) (cntj: containsThread tp2 j)
            sched sched',
            i <> j ->
            sim tp1 tp1' m1 m1' i α ->
            sim tp1 tp1' m1 m1' j α ->
            getStepType cnti = Internal ->
            (getStepType cntj = Internal \/ (getStepType cntj = Concurrent /\
                                            sim tp1 tp1' m1 m1' ls_id α /\
                                            sim tp1 tp1' m1 m1' sp_id α)) ->
            fstep (i :: j :: sched, tp1) m1 (j :: sched, tp2) m2 ->
            fstep (j :: sched, tp2) m2 (sched,tp3) m3 ->
            exists tp2' m2' tp3' m3' α',
              fstep (j :: i :: sched', tp1') m1' (i :: sched', tp2') m2' /\
              fstep (i :: sched', tp2') m2' (sched', tp3') m3' /\
              forall tid,
                sim tp1 tp1' m1 m1' tid α -> sim tp3 tp3' m3 m3' tid α'
        
      }.

End MachineSimulations.
End MachineSimulations.

Module Traces.

  Import Concur ThreadPool MemoryObs SimDefs.

  Context {the_ge : mySem.G}.

  Notation fstep := ((corestep fine_semantics) the_ge).
  Definition trace := list (nat * mySem.thread_pool).

  Lemma cat_inv :
    forall {A} xs ys (x y : A),
      xs ++ [:: x] = ys ++ [:: y] ->
      x = y /\ xs = ys.
  Proof.
    intros A xs ys x y Heq. generalize dependent ys.
    induction xs; intros.
    simpl in Heq. destruct ys; simpl in *;
                  [inversion Heq; subst; auto | destruct ys; simpl in *; inversion Heq].
    destruct ys; [destruct xs; simpl in *|]; inversion Heq.
    subst. eapply IHxs in H1. destruct H1; by subst.
  Qed.

  Lemma cat_inv2 :
    forall {A} xs ys (x x' y y' : A),
      xs ++ [:: x;x'] = ys ++ [:: y;y'] ->
      x = y /\ x' = y' /\ xs = ys.
  Proof.
    intros A xs ys x x' y y' Heq. generalize dependent ys.
    induction xs; intros.
    - simpl in Heq. destruct ys; simpl in *;
                    [inversion Heq; subst; auto | destruct ys; simpl in *; inversion Heq].
      subst. destruct ys; simpl in *; congruence.
    - destruct ys; [destruct xs; simpl in *|]; inversion Heq;
      subst.
      destruct xs; simpl in *; congruence.
      eapply IHxs in H1. destruct H1 as [? [? ?]]; by subst.
  Qed.

  Inductive isTrace : trace -> Prop :=
  | init_tr : forall (st : nat * mySem.thread_pool),
                  isTrace [:: st]
  | cons_tr : forall (st st' : nat * mySem.thread_pool) (tr : trace)
                (Htrace: isTrace (tr ++ [:: st]))
                (Hstep: (exists m m', fstep ([:: st.1], st.2) m ([::],st'.2) m')),
                isTrace (tr ++ [:: st;st']).

  Lemma isTrace_forward :
    forall tr tid tp tid' tp' 
      (Htrace: isTrace ((tid', tp') :: tr))
      (Hstep: exists m m', fstep ([:: tid],tp) m ([::],tp') m'),
      isTrace ((tid, tp) :: (tid', tp') :: tr).
  Proof.
    intros tr. induction tr as [|tr [tid' tp']] using last_ind.
    - intros tid tp tid' tp' Htrace Hstep. rewrite <- cat0s. constructor.
      rewrite cat0s. constructor.
      simpl. assumption.
    - intros tid tp tid'0 tp'0 Htrace Hstep. rewrite <- cats1 in *.
      inversion Htrace as [[tid0 tp0] Heq|]; subst. destruct tr; simpl in *; congruence.
      destruct tr0.
      destruct tr.
      simpl in *. inversion H0; subst.
      replace ([:: (tid, tp); (tid'0, tp'0); (tid', tp')]) with
      ([::(tid,tp)] ++ [::(tid'0,tp'0); (tid', tp')]) by reflexivity.
      constructor. simpl.
      rewrite <- cat0s. constructor. constructor. simpl. auto.
      simpl. auto.
      simpl in *.
      destruct tr; simpl in *; subst; congruence.
      destruct tr using last_ind. simpl in *.
      destruct tr0; simpl in *;
      [congruence| destruct tr0; simpl in *; congruence].
      clear IHtr0.
      rewrite <- cats1 in *. simpl in *.
      rewrite <- catA in H0. simpl in H0.
      inversion H0.
      apply cat_inv2 in H2.
      destruct H2 as [? [? ?]]. subst.
      clear H0.
      replace ([:: (tid, tp), (tid'0, tp'0) & tr ++ [:: x; (tid', tp')]]) with
      (((tid, tp) :: (tid'0, tp'0) :: tr) ++ [:: x; (tid', tp')]) by reflexivity.
      constructor. eapply IHtr; eauto.
      simpl. auto.
  Qed.
      
  Lemma corestepN_rcons:
    forall sched sched' tid tp m tp' m'
      (HcorestepN: corestepN fine_semantics the_ge (size (sched ++ [:: tid]))
                             ((sched ++ [:: tid]) ++ sched', tp) m (sched', tp') m'),
    exists tp'' m'',
      corestepN fine_semantics the_ge (size sched)
                ((sched ++ [:: tid]) ++ sched', tp) m (tid :: sched', tp'') m'' /\
      corestep fine_semantics the_ge (tid :: sched', tp'') m'' (sched', tp') m'.
  Proof.
    intros sched. induction sched as [|n sched]; intros; simpl in HcorestepN.
    - destruct HcorestepN as [? [? [Hstep Heq]]]; inversion Heq; subst.
      do 2 eexists; split; simpl; eauto. 
    - destruct HcorestepN as [st0 [m0 [Hstep HcorestepN]]].
      destruct st0 as [sched0 tp0].
      assert (Hsched: sched0 = (sched ++ [:: tid]) ++ sched')
        by (inversion Hstep; subst; simpl in *; auto).
      rewrite Hsched in HcorestepN, Hstep.
      clear Hsched.
      eapply IHsched in HcorestepN.
      destruct HcorestepN as [tp'' [m'' [HcorestepN Hstep']]].
n      exists tp'' m''. split.
      simpl. do 2 eexists; eauto.
      assumption.
  Qed.

  Notation mstate := myFineSemantics.MachState.
  
  Inductive execution : seq mstate -> Prop :=
  | init_exec : forall st,
                  execution [:: st]
  | cons_exec : forall (st st' : mstate) (exec : seq mstate)
                (Hexec: execution (exec ++ [:: st]))
                (Hstep: (exists m m', fstep st m st' m')),
                  execution (exec ++ [:: st;st']).

  Lemma execution_red:
    forall exec st st' exec'
      (Hexec: execution (st :: exec ++ exec' ++ [::st'])),
      execution (exec ++ exec' ++ [::st']).
  Proof.
    intros.
    generalize dependent st'. generalize dependent exec'.
    induction exec using last_ind; intros.
    - simpl in *.
      generalize dependent st'. induction exec' using last_ind.
      + intros. constructor.
      + intros. rewrite <- cats1.
        rewrite <- cats1 in Hexec.
        rewrite <- catA in Hexec.
        inversion Hexec; subst. destruct exec'; simpl in *; congruence.
        destruct exec. simpl in H0.
        destruct exec'; simpl in *; [congruence | destruct exec'; simpl in *; congruence].
        simpl in H0. inversion H0; subst.
        assert (Heq: exec = exec' /\ st0 = x /\ st'0 = st').
        { clear - H2.
          generalize dependent exec'.
          induction exec; intros.
          - destruct exec'. simpl in *. inversion H2; subst. auto.
            destruct exec'; simpl in *; try congruence.
            destruct exec'; simpl in *; try congruence.
          - destruct exec'; simpl in *.
            destruct exec; simpl in *; try congruence.
            destruct exec; simpl in *; try congruence.
            inversion H2; subst.
            eapply IHexec in H1. by destruct H1 as [? [? ?]]; subst.
        }
        destruct Heq as [? [? ?]]; subst.
        eapply IHexec' in Hexec0.
        rewrite <- catA. constructor. assumption.
        assumption.
    - rewrite <- cats1 in Hexec. rewrite <- cats1.
      rewrite <- catA in Hexec.
      specialize (IHexec ([:: x] ++ exec') st').
      rewrite <- catA in IHexec. apply IHexec in Hexec.
      rewrite <- catA. auto.
  Qed.
                
  Lemma corestepN_execution_strong :
    forall tp m tp' m' tid sched sched'
      (HcorestepN: corestepN fine_semantics the_ge (size (tid :: sched))
                             ((tid :: sched) ++ sched', tp) m (sched', tp') m'),
    exists (exec : seq mstate),
      execution (((tid :: sched) ++ sched', tp) :: exec ++ [:: (sched', tp')]).
  Proof.
    intros.
    generalize dependent tp. generalize dependent m.
    generalize dependent sched'. generalize dependent tp'. generalize dependent m'.
    generalize dependent tid.
    induction sched as [|sched x] using last_ind; intros.
    - exists (nil : seq mstate).
        rewrite <- cat0s.
        simpl in HcorestepN. destruct HcorestepN as [? [? [Hstep Heq]]].
        inversion Heq; subst.
        constructor; [constructor | do 2 eexists; eauto].
    - rewrite <- cats1 in HcorestepN.
      eapply corestepN_rcons with (sched := tid :: sched) in HcorestepN.
      destruct HcorestepN as [tp'' [m'' [HcorestepN Hstep]]].
      rewrite <- catA in HcorestepN.
      eapply IHsched in HcorestepN.
      destruct HcorestepN as [exec Hexec].
      exists (exec ++ [:: (x :: sched', tp'')]).
      rewrite <- catA. simpl.
      rewrite <- cat_cons.
      constructor.
      rewrite <- cats1. simpl.
      rewrite <- catA. auto.
      do 2 eexists. eauto.
  Qed.

  Inductive closed_execution : seq mstate -> Prop :=
  | closed_exec : forall exec st,
                    execution (exec ++ [:: st]) ->
                    st.1 = nil ->
                    closed_execution (exec ++ [:: st]).
  
  Corollary corestepN_execution :
    forall tp m tp' m' tid sched
      (HcorestepN: corestepN fine_semantics the_ge (size (tid :: sched))
                             (tid :: sched, tp) m (nil, tp') m'),
    exists (exec : seq mstate),
     closed_execution ((tid :: sched, tp) :: exec ++ [:: (nil, tp')]).
  Proof.
    intros.
    replace (tid :: sched, tp) with ((tid :: sched) ++ nil, tp) in HcorestepN
      by (by rewrite cats0).
    eapply corestepN_execution_strong in HcorestepN.
    destruct HcorestepN as [exec Hexec].
    exists exec.
    rewrite <- cat_cons. constructor.
    rewrite cats0 in Hexec. auto.
    reflexivity.
  Qed.
  
  Inductive flatten_execution (i : nat): seq mstate -> seq (nat * mySem.thread_pool) -> Prop :=
  | flat_single : forall tp,
                    flatten_execution i [:: ([::],tp)] [:: (i,tp)]
  | flat_cons : forall tp tr ftr sched tid
                  (Hflat: flatten_execution i tr ftr),
                  flatten_execution i ((tid :: sched, tp) :: tr) ((tid, tp) :: ftr).

  Lemma flatten_single :
    forall tr st st' i
      (Hflat : flatten_execution i [:: st] (tr ++ [:: st'])),
      i = st'.1 /\ tr = nil /\ st.2 = st'.2 /\ st.1 = nil.
  Proof.
    intros. inversion Hflat.
    subst. destruct tr; simpl in *; subst. destruct st'; inversion H; subst; simpl.
    auto.
    destruct tr; simpl in *; congruence.
    subst. inversion Hflat0.
  Qed.

  Lemma flatten_rcons :
    forall i exec tr tp tp' j
      (Hflatten: flatten_execution i (exec ++ [:: ([::], tp)]) (tr ++ [:: (i, tp)])),
      flatten_execution j (exec ++ [:: ([:: i], tp); ([::], tp')])
                        (tr ++ [:: (i,tp); (j, tp')]).
  Proof.
    intros i exec.
    induction exec as [|st exec]; intros; simpl in *.
    - apply flatten_single in Hflatten. destruct Hflatten as [? [? ?]]; simpl in *.
      subst. constructor. constructor.
    - destruct tr.
      + simpl in *.
        inversion Hflatten; subst;
        [destruct exec; simpl in *; subst; congruence | inversion Hflat].
      + inversion Hflatten; subst.
        destruct exec; simpl in *; subst; congruence.
        simpl. constructor.
          by eapply IHexec.
  Qed.

  Lemma flatten_rcons_inv :
    forall exec tr st st' i
      (Hflatten: flatten_execution i (exec ++ [:: st]) (tr ++ [:: st'])),
      st.2 = st'.2 /\ st.1 = nil.
  Proof.
    intros exec. induction exec as [|st0 exec]; intros.
    - simpl in *. apply flatten_single in Hflatten. by destruct Hflatten as [? [? ?]].
    - inversion Hflatten. subst. destruct exec; simpl in *; congruence.
      subst.
      destruct tr; simpl in *. destruct ftr. inversion Hflat.
      simpl in *; congruence.
      inversion H; subst. eapply IHexec; eauto.
  Qed.
  
  Lemma execution_steps :
    forall exec st exec' st',
      execution (exec ++ [:: st;st'] ++ exec') ->
      exists m m', fstep st m st' m'.
  Proof.
    intros exec st exec'. generalize dependent st. generalize dependent exec.
    induction exec' using last_ind; intros exec st st' Hexec.
    - rewrite cats0 in Hexec.
      inversion Hexec. destruct exec; simpl in *;
                       [congruence | destruct exec; simpl in *; congruence].
      replace (exec0 ++ [:: st0; st'0]) with ((exec0 ++ [:: st0]) ++ [:: st'0]) in H0
        by (rewrite <- catA; auto).
      replace (exec ++ [:: st; st']) with ((exec ++ [:: st]) ++ [:: st']) in H0
        by (rewrite <- catA; auto).
      apply cat_inv in H0. destruct H0 as [Heq1 Heq2].
      apply cat_inv in Heq2. destruct Heq2; subst.
      eauto.
    - rewrite <- cats1 in Hexec.
      inversion Hexec.
      destruct exec; simpl in *; [congruence| destruct exec; simpl in *; congruence].
      destruct exec' using last_ind; simpl in *.
      + assert (Heq: exec0 = exec ++ [:: st] /\ st0 = st' /\ st'0 = x) by admit.
        destruct Heq as [? [? ?]]; subst.
        rewrite <- catA in Hexec0. simpl in Hexec0.
        eapply IHexec' in Hexec0. eauto.
      + clear IHexec'0.
        rewrite <- cats1 in H0. rewrite <- catA in H0.
        simpl in H0. rewrite <- cats1 in IHexec', Hexec.
        assert (Heq: exec0 = exec ++ [:: st, st' & exec'] /\ st0 = x0 /\ st0 = x).
        admit.
        destruct Heq as [? [? ?]]. subst.
        rewrite <- catA in Hexec0. simpl in Hexec0.
        eapply IHexec' in Hexec0. eauto.
  Qed.
      
  Lemma execution_flatten_trace :
    forall exec i st,
      closed_execution (exec ++ [:: st]) ->
      exists tr,
        flatten_execution i (exec ++ [:: st]) tr /\
        isTrace tr.
  Proof.
    intros exec i. induction exec as [|st' exec]; intros st Hexec.
    - inversion Hexec.
      destruct exec; destruct st0. simpl in *; subst.
      exists [:: (i,m)]. split; constructor.
      destruct exec; simpl in *; congruence.
    - simpl in Hexec.
      inversion Hexec. destruct exec0; simpl in *.
      destruct exec; simpl in *; congruence.
      inversion H.
      apply cat_inv in H4. destruct H4; subst.
      eapply execution_red with (exec' := nil) in H0.
      rewrite cat0s in H0.
      assert (Hclosed: closed_execution (exec ++ [:: st]))
        by (constructor; eauto).
      eapply IHexec in Hclosed; clear IHexec.
      destruct Hclosed as [tr [Hflat Htrace]].
      destruct exec as [|st'' exec]; simpl in *.
      + inversion Hexec as [exec st0 Hstep ? Heq].
        replace ([:: st'; st]) with ([:: st'] ++ [:: st]) in Heq by (apply cat_inv).
        apply cat_inv in Heq. destruct Heq; subst.
        simpl in *. rewrite <- cat0s in Hstep. rewrite <- cats0 in Hstep.
        apply execution_steps with (exec := nil) (exec' := nil) in Hstep.
        destruct Hstep as [m [m' Hstep]].
        assert (Htid: exists tid, mySchedule.schedPeek st'.1 = Some tid)
          by (inversion Hstep; eexists; eauto).
        destruct Htid as [tid Hsched].
        exists ((tid, st'.2) :: tr).
        destruct st' as [sched' tp'], st as [sched tp].
        simpl in *.
        unfold mySchedule.schedPeek in Hsched.
        destruct sched'; simpl in *; inversion Hsched; subst.
        split. by constructor.
        destruct tr. constructor.
        inversion Hflat. subst.
        assert (Hstep_weak: fstep ([:: tid], tp') m ([::], tp) m') by admit.
        eapply isTrace_forward; eauto.
      + inversion Hexec as [exec0 st0 Hstep ? Heq].
        destruct exec0; simpl in *; [congruence | destruct exec0].
        destruct exec; simpl in *; congruence.
        inversion Heq; subst.
        rewrite cat_cons in Hstep.
        replace ([:: st', st'' & exec0 ++ [:: st0]])
        with ([::] ++ [:: st';st''] ++ (exec0 ++ [:: st0])) in Hstep by reflexivity.
        apply execution_steps with (exec' := exec0 ++ [:: st0]) in Hstep.
        destruct Hstep as [m [m' Hstep]].
        assert (Htid: exists tid, mySchedule.schedPeek st'.1 = Some tid)
          by (inversion Hstep; eexists; eauto).
        destruct Htid as [tid Hsched].
        destruct st' as [sched' tp'], st'' as [sched'' tp''].
        destruct sched'; simpl in *; inversion Hsched; subst.
        inversion Heq. apply cat_inv in H4; destruct H4; subst.
        clear Heq H.
        exists ((tid,tp') :: tr).
        split. constructor. assumption.
        inversion Hflat; subst.
        assert (Hstep_weak: fstep([:: tid], tp') m ([::], tp'') m') by admit.
        eapply isTrace_forward; eauto.
        eapply isTrace_forward; eauto.
        assert (Hstep_weak: fstep ([:: tid], tp') m ([::], tp'') m') by admit.
        do 2 eexists; eauto.
  Qed.

  Lemma isTrace_cons :
    forall tr st st',
      isTrace (tr ++ [:: st; st']) ->
      isTrace (tr ++ [:: st]) /\ (exists m m', fstep ([:: st.1], st.2) m ([::], st'.2) m').
  Proof.
    intros tr st st' Htrace. inversion Htrace as [|? ? ? ? ? Heq].
    destruct tr; simpl in *; [congruence| destruct tr; simpl in *; congruence].
    apply cat_inv2 in Heq. destruct Heq as [? [? ?]]; subst.
    auto.
  Qed.

  Lemma flatten_map:
    forall j tp' exec tr tp i,
      flatten_execution i (exec ++ [:: ([::], tp)])
                        (tr ++ [:: (i, tp)]) ->
      flatten_execution j
                        ([seq (st.1 ++ [:: j], st.2) | st <- exec] ++ [:: ([::], tp')])
                        (tr ++ [:: (j, tp')]).
  Proof.
    intros j tp' exec.
    induction exec; intros.
    - simpl in *.
      destruct tr.
      simpl. constructor.
      inversion H. destruct tr; simpl in *; congruence.
    - inversion H. destruct exec; simpl in *; congruence.
      subst.
      destruct ftr using last_ind. inversion Hflat.
      clear IHftr.
      rewrite <- cats1 in *.
      rewrite <- cat_cons in H3.
      apply cat_inv in H3. destruct H3 as [? Heq].
      subst. eapply IHexec in Hflat.
      simpl. constructor. assumption.
  Qed.

  Lemma execution_map:
    forall exec sched,
      execution exec ->
      execution (map (fun st => (st.1 ++ sched, st.2)) exec).
  Proof.
    intros exec sched Hexec.
    induction exec using last_ind.
    inversion Hexec.
    destruct exec; simpl in *; congruence.
    rewrite <- cats1 in *.
    inversion Hexec. destruct exec; simpl in *; inversion H0; subst.
    constructor.
    destruct exec; simpl in *; congruence.
    destruct exec using last_ind.
    destruct exec0; simpl in *; [congruence | destruct exec0; simpl in *; congruence].
    clear IHexec0.
    rewrite <- cats1 in *. rewrite <- catA in *. simpl in *.
    apply cat_inv2 in H0. destruct H0 as [? [? ?]]; subst.
    eapply IHexec in Hexec0.
    rewrite map_cat. simpl.
    constructor.
    assert(Heq: [:: (x0.1 ++ sched, x0.2)] =
                map (fun st => (st.1 ++ sched, st.2)) ([:: (x0.1, x0.2)])) by reflexivity.
    rewrite Heq.
    rewrite <- map_cat.
    destruct x0; simpl. assumption.
    admit.
  Qed.
  
  Lemma flat_trace :
    forall tr st
      (Htrace: isTrace (tr ++ [:: st])),
    exists exec, flatten_execution (st.1) exec (tr ++ [:: st]) /\
            execution exec.
  Proof.
    intros tr. induction tr as [|tr st'] using last_ind; intros.
    - exists ([:: (nil : list nat, st.2)]).
        split.
        simpl.
        destruct st. constructor. constructor.
    - rewrite <- cats1 in *.
      rewrite <- catA in *. simpl in *.
      apply isTrace_cons in Htrace.
      destruct Htrace as [Htrace Hstep].
      eapply IHtr in Htrace. destruct Htrace as [exec [Hflat Hexec]].
      destruct exec as [|exec st0] using last_ind.
      + inversion Hflat.
      + rewrite <- cats1 in *.
        clear IHexec.
        assert (Heq: st0.2 = st'.2 /\ st0.1 = nil) by (eapply flatten_rcons_inv; eauto).
        destruct Heq.
        destruct st0 as [sched0 tp0], st' as [sched' tp'].
        simpl in *. subst.
        exists ((map (fun st => (st.1 ++ [:: sched'], st.2)) exec)
             ++ [:: ([ :: sched'], tp'); ([:: ],st.2)]). split. 
        destruct st as [i tp].
        eapply flatten_rcons.
        eapply flatten_map; eauto.
        constructor; auto.
        assert (Heq: [:: ([:: sched'], tp')] =
                     map (fun st => (st.1 ++ [:: sched'], st.2)) [:: ([::], tp')]) by reflexivity.
        rewrite Heq.
        rewrite <- map_cat. 
          by apply execution_map.
  Qed.

  Variable thread_pool : Type.
  Variable renaming : Type.
  Variable sort : nat -> list nat -> list nat -> Prop.
  Variable sim : renaming -> thread_pool -> thread_pool -> list nat -> Prop.

  Goal  forall ren tp tp' xs ys tid ,
      sort tid xs ys ->
      sim ren tp tp' xs ->
      exists ren', sim ren' tp tp' ys.
  Proof.
    intros ren tp tp' xs. induction xs using last_ind. intros. admit.
    intros.

  
  Inductive ObsEqTrace (tid_last : nat) : trace -> trace -> Prop :=
  | ObsEqNil : ObsEqTrace tid_last nil nil
  | ObsEqConsC : forall tr tr' (st : nat * mySem.thread_pool)
                   (cnt: containsThread st.2 st.1)
                  (HeqTrace: ObsEqTrace tid_last tr tr')
                  (HStepType: getStepType cnt = Concurrent),
      ObsEqTrace tid_last (st :: tr) (st :: tr')
  | ObsEqConsI : forall tr tr' (st : nat * mySem.thread_pool)
                   (cnt: containsThread st.2 st.1)
                   (HeqTrace: ObsEqTrace tid_last tr tr')
                   (HStepType: getStepType cnt = Internal \/ getStepType cnt = Resume)
                   (Hobservable: st.1 = tid_last \/
                                 exists st', In st' tr /\
                                        st'1. = st.1 /\ getStepType cnt = Concurrent),
      ObsEqTrace tid_last (st :: tr) (st :: tr')
  | UnObsEqCons: forall tr tr' (st : nat * mySem.thread_pool)
                 (cnt: containsThread st.2 st.1)
                 (HeqTrace: ObsEqTrace tid_last tr tr')
                 (HStepType: getStepType cnt = Internal \/ getStepType cnt = Resume)
                 (Hunobs: st.1 <> tid_last /\
                          ~ exists st', In st' tr /\
                                   st'1. = st.1 /\ getStepType cnt = Concurrent),
  Fixpoint filter_trace (tid_last : nat) (tr : trace) :=
    match tr with
      | nil => nil
      | st :: tr =>
        if is_concurrent_step st then
          st :: (filter_trace tid_last tr)
        else
          if (st.1 == tid_last) ||
                                (List.existsb (fun st' =>
                                                 (st'.1 == st.1) && is_concurrent_step st')) tr then
            st :: (filter_trace tid_last tr)
          else
            filter_trace tid_last tr
    end.

End Traces.

Module StepLemmas.
  Section StepLemmas.

    Import ThreadPool Concur.
    Context {cT G : Type} {the_sem : CoreSemantics G cT Mem.mem}.

    Notation cT' := (@ctl cT).
    Notation thread_pool := (t cT).
    Notation perm_map := access_map.
    Notation invariant := (@invariant cT G the_sem).

    Variable the_ge : G.
    Notation dry_step := (@dry_step cT G the_sem the_ge).
    
    Lemma restrPermMap_wf :
      forall (tp : thread_pool) (m m': mem) tid
        (* (Hlt: permMapLt (share_maps tp tid) (getMaxPerm m)) *)
        (Hcompatible: mem_compatible tp m)
        (Hrestrict: restrPermMap (permMapsInv_lt (perm_comp Hcompatible) tid) = m')
        (Hrace : race_free tp),
        shareMap_wf tp (getCurPerm m') (nat_of_ord tid).
    Proof.
      intros. subst.
      unfold restrPermMap, getCurPerm. simpl.
      unfold permMap_wf. intros tid' Htid' Hneq.
      unfold permMapsDisjoint. simpl.
      assert (Hneq' : tid' <> tid) by auto.
      destruct tid as [tid Htid].
      specialize (Hrace tid' tid Htid' Htid Hneq').
      unfold permMapsDisjoint in Hrace.
      destruct Hcompatible as [_ Hcan_mem].
      unfold isCanonical in Hcan_mem.
      unfold getMaxPerm in Hcan_mem. simpl in Hcan_mem.
      intros b ofs. specialize (Hrace b ofs).
      rewrite Maps.PMap.gmap. unfold getThreadR in *.
      
      unfold Maps.PMap.get in *. simpl.
      unfold isCanonical in Hcanonical. rewrite Hcanonical in Hrace.
      rewrite Maps.PTree.gmap. unfold Coqlib.option_map.
      destruct (Maps.PTree.get b (Mem.mem_access m).2) eqn:?;
      destruct (Maps.PTree.get b
                               (perm_maps tp (Ordinal Htid)).2) eqn:?;
      try rewrite Hcanonical; auto.
      destruct (Maps.PTree.get b
                               (perm_maps tp (Ordinal Htid')).2) eqn:?; auto.
      unfold permMapLt in Hlt.
      unfold Maps.PMap.get in Hlt.
      specialize (Hlt b ofs).
      rewrite Heqo0 in Hlt.
      unfold getMaxPerm in Hlt. simpl in Hlt.
      rewrite Maps.PTree.gmap1 in Hlt. unfold Coqlib.option_map in Hlt.
      rewrite Heqo in Hlt.
      apply equal_f with (x := ofs) in Hcan_mem.
      rewrite Hcan_mem in Hlt.
      unfold Mem.perm_order'' in Hlt. destruct (o ofs); auto.
      exfalso. auto.
      rewrite perm_union_comm. apply not_racy_union. constructor.
    Defined.
    


        
    Hypothesis corestep_canonical_max :
      forall c m c' m'
        (Hm_canon: isCanonical (getMaxPerm m))
        (Hcore: corestep the_sem the_ge c m c' m'),
        isCanonical (getMaxPerm m').
    
    Hypothesis corestep_canonical_cur :
      forall c m c' m'
        (Hm_canon: isCanonical (getCurPerm m))
        (Hcore: corestep the_sem the_ge c m c' m'),
        isCanonical (getCurPerm m').

    Hypothesis corestep_permMap_wf : forall tp tid (Htid: tid < @num_threads cT' tp) c m c' m'
                                       (Hperm: permMap_wf tp (getCurPerm m) tid)
                                       (Hcore: corestep the_sem the_ge c m c' m'),
                                       permMap_wf tp (getCurPerm m') tid.

    Lemma updThread_invariants :
      forall (tp tp' : thread_pool) c m m1 c' m1' tid counter
        (Hinv: invariant tp)
        (Hcompatible: mem_compatible tp m)
        (Hcode: getThreadC tp tid = Krun c)
        (Hrestrict_pmap: restrPermMap (permMapsInv_lt (perm_comp Hcompatible) tid) = m1)
        (Hcore: corestep the_sem the_ge c m1 c' m1')
        (Htp': tp' = updThread tp tid (Krun c') (getCurPerm m1') counter),
        invariant tp'.
    Proof.
      intros. destruct Hinv as [Hcanonical Hrace Hlp].
      destruct tid as [tid pf].
      assert (Hcontra: tid <> 0).
      { intros Hcontra. subst tp' tid.
        simpl in *.
        destruct (Hlp pf) as [c0' [Hcode' Hhalted]].
        rewrite Hcode in Hcode'; inversion Hcode'; subst c0'.
        apply corestep_not_halted in Hcore. 
        rewrite Hcore in Hhalted. auto.
      }
      split.
      { intros tid'.
        destruct tid' as [tid' pf'].
        destruct (tid == tid') eqn:Heq'; move/eqP:Heq'=>Heq'; subst tp'; try subst tid'.
        - simpl in *.
          pf_cleanup.
          rewrite eq_refl.
          eapply corestep_canonical_cur with (c := c) (c' := c'); eauto.
          eapply restrPermMap_can; by eauto.
        - simpl in *.
          rewrite if_false.
          eapply Hcanonical.
          apply/eqP. intro Hcontra'. inversion Hcontra'; auto.
      }
      { unfold race_free in *.
        intros.
        destruct (tid == tid0) eqn:Heq0, (tid == tid0') eqn:Heq0'; move/eqP:Heq0=>Heq0;
          move/eqP:Heq0'=>Heq0'; simpl in *.
        - subst tid0 tid0'. exfalso; auto.
        - subst tid0. subst tp'. simpl in *.
          rewrite if_true.
          rewrite if_false.
          assert (Hwf := no_race_wf pf Hrace).
          apply restrPermMap_wf in Hrestrict_pmap; auto.
          assert (Hwf': permMap_wf tp (getCurPerm m1') tid).
          { eapply @corestep_permMap_wf; eauto. }
          unfold permMap_wf in Hwf'.
          specialize (Hwf' _ Htid0' Heq0').
          apply permMapsDisjoint_comm. assumption.
          apply permMapsInv_lt. destruct Hcompatible; auto.
          apply/eqP. intro Hcontra'; inversion Hcontra'. auto.
          rewrite (leq_pf_irr _ _ Htid0 pf). apply eq_refl.
        - subst tid0' tp'; simpl in *.
          rewrite if_false. rewrite if_true.
          assert (Hwf := no_race_wf pf Hrace).
          apply restrPermMap_wf in Hrestrict_pmap; auto.
          assert (Hwf': permMap_wf tp (getCurPerm m1') tid).
          { eapply corestep_permMap_wf; eauto. }
          unfold permMap_wf in Hwf'.
          specialize (Hwf' _ Htid0 Heq0).
          assumption.
          apply permMapsInv_lt. destruct Hcompatible; auto.
          rewrite (leq_pf_irr _ _ Htid0' pf). apply eq_refl.
          apply/eqP. intro Hcontra'. inversion Hcontra'. auto.
        - subst tp'. simpl.
          rewrite if_false. rewrite if_false; simpl in *.
          eapply Hrace; eauto.
          apply/eqP. intro Hcontra'. inversion Hcontra'. auto.
          apply/eqP. intro Hcontra'. inversion Hcontra'. auto.
      }
      { subst tp'. simpl. intros pf0. destruct (Hlp pf0) as [c0 [Hcode Hhalted]].
        exists c0. split; auto.
        rewrite if_false; auto.
        apply/eqP. intro Hcontra'. inversion Hcontra'; auto.
      }     
    Qed.

    Lemma dry_step_invariants :
      forall (tp tp' : thread_pool) m m' (tid : nat) (pf : containsThread tp tid)
        (Hcompatible: mem_compatible tp m)
        (Hinv: invariant tp)
        (Hstep: dry_step pf Hcompatible tp' m'),
        invariant tp'.
    Proof.
      intros. inversion Hstep.
      eapply updThread_invariants; eauto.
    Qed.

    Hypothesis corestep_access :
      forall c m c' m' b ofs
        (Hcore: corestep the_sem the_ge c m c' m'),
        (forall k, Mem.perm_order'' (Maps.PMap.get b (Mem.mem_access m') ofs k)
                               (Maps.PMap.get b (Mem.mem_access m) ofs k))
        \/ (forall k, (Maps.PMap.get b (Mem.mem_access m) ofs k = Some Freeable /\
                 Maps.PMap.get b (Mem.mem_access m') ofs k = None)).
    
    Lemma dry_step_compatible :
      forall (tp tp' : thread_pool) m m' (tid : nat) (pf : containsThread tp tid)
        (Hcompatible: mem_compatible tp m)
        (Hinv: invariant tp)
        (Hstep: dry_step pf Hcompatible tp' m'),
        mem_compatible tp' m'.
    Proof.
      intros; inversion Hstep; subst.
      split.
      { unfold perm_compatible, updThread. simpl.
        intros.
        match goal with
          | [ |- context[if ?Expr then _ else _]] =>
            destruct Expr eqn:Htid
        end; [apply getCur_Max|].
        move/eqP:Htid=>Htid.
        assert (Hlt := (perm_comp Hcompatible) tid0 b ofs). unfold getThreadR in Hlt.
        destruct (corestep_access _ _ c' m' b ofs Hcorestep) as [Hperm | Hperm].
        - specialize (Hperm Max).
          assert (Hlt_max: Mem.perm_order'' (Maps.PMap.get b (getMaxPerm m') ofs)
                                            (Maps.PMap.get b (getMaxPerm m) ofs)).
          { do 2 rewrite getMaxPerm_correct.
            simpl in Hperm.
            unfold Maps.PMap.get in *. simpl in Hperm.
            rewrite Maps.PTree.gmap in Hperm.
            unfold Coqlib.option_map in Hperm.
            destruct (Maps.PTree.get b (Mem.mem_access m).2) eqn:?; auto.
          }
          eapply po_trans; eauto.
        - replace (Maps.PMap.get b (getMaxPerm m') ofs) with (None : option permission)
            by (destruct (Hperm Max) as [_ HmaxNone];
                  by rewrite getMaxPerm_correct).
          destruct (Hperm Cur) as [HCurF HcurNone].
          clear Hperm.
          assert (Hracy: Maps.PMap.get b (perm_maps tp (Ordinal pf)) ofs = Some Freeable).
          { clear Hcorestep Hlt HcurNone.
            unfold Maps.PMap.get in *.
            simpl in *.
            rewrite Maps.PTree.gmap in HCurF.
            unfold Coqlib.option_map in HCurF.
            destruct (Maps.PTree.get b (Mem.mem_access m).2) eqn:?.
            - unfold getThreadR in HCurF.
              unfold Maps.PMap.get in HCurF. auto.
            - discriminate.
          }
          assert (Hno_race := no_race Hinv).
          destruct tid0 as [tid0 pf_tid0].
          assert (Hneq: tid <> tid0)
            by (intro Hcontra; subst; unfold containsThread in *; pf_cleanup; auto).
          specialize (Hno_race tid tid0 pf pf_tid0 Hneq).
          unfold permMapsDisjoint in Hno_race.
          specialize (Hno_race b ofs).
          apply no_race_racy in Hno_race; auto.
          inversion Hno_race. constructor.
          rewrite Hracy. constructor.
      }
      { eapply corestep_canonical_max; eauto.
        unfold isCanonical, getMaxPerm, restrPermMap. simpl.
        apply (mem_canonical Hcompatible).
      }
    Qed.

  End StepLemmas.
End StepLemmas.
        
Module FineStepLemmas.
Section FineStepLemmas.

  Import Concur ThreadPool MemoryObs SimDefs StepLemmas.

  Context {cT G : Type} {the_sem : CoreSemantics G cT Mem.mem}.

  Notation cT' := (@ctl cT).
  Notation thread_pool := (t cT').
  Notation perm_map := access_map.
  Notation invariant := (@invariant cT G the_sem).

  Variable the_ge : G.
  Variable rename_code : (block -> block) -> cT -> cT.
  Notation dry_step := (@dry_step cT G the_sem the_ge).
  Notation rename_core := (@rename_core cT rename_code).
  Notation tp_sim := (@tp_sim cT G the_sem rename_code).
  Notation weak_tp_sim := (@weak_tp_sim cT G the_sem rename_code).
    
  Hypothesis corestep_canonical_max :
    forall c m c' m'
      (Hm_canon: isCanonical (getMaxPerm m))
      (Hcore: corestep the_sem the_ge c m c' m'),
      isCanonical (getMaxPerm m').
  
  Hypothesis corestep_canonical_cur :
    forall c m c' m'
      (Hm_canon: isCanonical (getCurPerm m))
      (Hcore: corestep the_sem the_ge c m c' m'),
      isCanonical (getCurPerm m').

  Hypothesis corestep_permMap_wf : forall tp tid (Htid: tid < @num_threads cT' tp) c m c' m'
                                     (Hperm: permMap_wf tp (getCurPerm m) tid)
                                     (Hcore: corestep the_sem the_ge c m c' m'),
                                     permMap_wf tp (getCurPerm m') tid.

  Hypothesis corestep_access :
    forall c m c' m' b ofs
      (Hcore: corestep the_sem the_ge c m c' m'),
      (forall k, Mem.perm_order'' (Maps.PMap.get b (Mem.mem_access m') ofs k)
                             (Maps.PMap.get b (Mem.mem_access m) ofs k))
      \/ (forall k, (Maps.PMap.get b (Mem.mem_access m) ofs k = Some Freeable /\
               Maps.PMap.get b (Mem.mem_access m') ofs k = None)).


  Hypothesis rename_code_at_ext :
    forall α (c : cT),
      at_external the_sem (rename_code α c) = None <->
      at_external the_sem c = None.


  Lemma corestep_disjoint_mem_obs_id :
    forall c1 c2 m1i m1 m2 p1i p1j p2j
      (Hcanonical: isCanonical (getMaxPerm m1))
      (Hlt1j: permMapLt p1j (getMaxPerm m1))
      (Hlt1i: permMapLt p1i (getMaxPerm m1))
      (Hlt2j: permMapLt p2j (getMaxPerm m2))
      (Heq: p1j = p2j)
      (Hrestr1i: restrPermMap Hlt1i = m1i)
      (Hdisjoint1: permMapsDisjoint p1i p1j)
      (Hstep: corestep the_sem the_ge c1 m1i c2 m2),
      mem_obs_eq (fun b => b) (restrPermMap Hlt1j) (restrPermMap Hlt2j).
  Proof.
    intros. subst p2j.
    split; intros; simpl in Hrenaming; subst b2.
    { unfold Mem.perm in *. simpl in *.
      simpl.
      apply corestep_unchanged_on with (b := b1) (ofs := ofs) in Hstep.
      rewrite <- Hrestr1i in Hstep. simpl in Hstep.
      assumption.
      assert (Hdisjoint1': permMapsDisjoint (getCurPerm m1i) (getCurPerm (restrPermMap Hlt1j)))
        by (eapply restrPermMap_disjoint_inv; eauto).
      intros Hpermi.
      eapply disjoint_norace; eauto.
    }
    { assert (corestepN the_sem the_ge 1 c1 m1i c2 m2)
        by (unfold corestepN; do 2 eexists; eauto);
      assert (Hcanonical1i: isCanonical (getMaxPerm m1i))
        by (eapply restrPermMap_can_max; eauto);
      assert (Hcanonical2: isCanonical (getMaxPerm m2))
        by (eapply corestep_canonical_max; eauto).
      clear -Hcanonical2 Hcanonical Hlt1j Hlt2j Hdisjoint1.
      unfold permMapLt in *.
      unfold getMaxPerm, isCanonical in Hcanonical, Hcanonical2;
        simpl in *.
      specialize (Hlt1j b1 ofs).
      specialize (Hlt2j b1 ofs).
      unfold Maps.PMap.get in *. simpl in *.
      do 2 rewrite Maps.PTree.gmap. rewrite Maps.PTree.gmap1 in Hlt1j;
      rewrite Maps.PTree.gmap1 in Hlt2j.
      unfold Coqlib.option_map in *.
      destruct (Maps.PTree.get b1 (Mem.mem_access m1).2) eqn:Hget1;
        destruct (Maps.PTree.get b1 (Mem.mem_access m2).2) eqn:Hget2; auto;
      [replace ((Mem.mem_access m2).1 ofs Max) with (None : option permission) in Hlt2j
        by (apply equal_f with (x:= ofs) in Hcanonical2; auto);
        unfold Mem.perm_order'' in Hlt2j |
       replace ((Mem.mem_access m1).1 ofs Max) with (None : option permission) in Hlt1j
         by (apply equal_f with (x:= ofs) in Hcanonical; auto);
         unfold Mem.perm_order'' in Hlt1j];
      destruct (Maps.PTree.get b1 p1j.2);
        match goal with
            [H: match ?Expr with _ => _ end |- _] =>
            destruct Expr
        end; tauto.     
    }
  Qed.

  Ltac step_absurd :=
    repeat
      (match goal with
         | [H1: getThreadC ?Tp (@Ordinal _ ?Tid ?Pf1) = _,
                H2: getThreadC ?Tp (@Ordinal _ ?Tid ?Pf2) = _ |- _] =>
           assert (Pf1 = Pf2) by (erewrite leq_pf_irr; reflexivity);
         subst Pf2
         | [H1: getThreadC ?Tp (Ordinal ?Pf) = _,
                H2: getThreadC ?Tp (Ordinal ?Pf) = ?C2 |- _] =>   
           rewrite H2 in H1; inversion H1; try (subst C2; clear H1)
          | [H1: at_external _ ?C1 = None,
                 H2: at_external _ ?C1 = Some _ |- _] =>
           congruence
         | [H1: is_true (leq (n (num_threads ?Tp)) ?I),
                H2: is_true (leq (S ?I) (n (num_threads ?Tp))) |- _] =>
           clear - H1 H2;
         exfalso; ssromega
       end).

  Lemma dry_step_sim_invariant_l :
    forall (tp1 tp1' tp2 : thread_pool) (m1 m2 m1' : mem) (i j : nat)
      (pfi : containsThread tp1 i)
      (α: block -> block) (Hneq: i <> j)
      (Hcompatible1: mem_compatible tp1 m1)
      (Htp_sim: weak_tp_sim tp1 tp1' j α)
      (Hmem_sim: mem_sim tp1 tp1' m1 m1' j α)
      (Hstep: dry_step pfi Hcompatible1 tp2 m2)
      (Hcompatible2: mem_compatible tp2 m2),
      weak_tp_sim tp2 tp1' j α /\ mem_sim tp2 tp1' m2 m1' j α.
  Proof with (eauto 3 with mem).
    intros. inversion Hstep as [tp' c m1i m' c2 Hrestrict Hcode Hcorestep Htp2].
    subst tp' m'.
    split.
    { (* Proof of tp_sim *)
      inversion Htp_sim.
      assert (pf2: j < num_threads tp2)
        by (subst; simpl; auto).
      eapply @Tp_weak_sim with (pf := pf2) (pf' := pf'); simpl; eauto.
      - subst; auto.
      - subst; auto.
      - subst; simpl. rewrite if_false. simpl in pf2. pf_cleanup. eassumption.
        apply/eqP. intros Hcontra; inversion Hcontra; auto.
      - eapply @updThread_invariants with
        (c := c) (m1 := m1i) (c' := c2) (m1' := m2) (tp := tp1); eauto.
    }
    { (* Proof of mem_sim *)
      inversion Hmem_sim as [pf1 pf1' Hcomp Hcompatible'].
      pf_cleanup.
      assert (pf2: j < num_threads tp2)
        by (subst; simpl; auto).
      eapply Mem_sim with (Hcomp := Hcompatible2) (Hcomp' := Hcompatible')
                                                  (pf := pf2) (pf' := pf1')...
      assert (Hobs':
                mem_obs_eq id
                           (restrPermMap (permMapsInv_lt (perm_comp Hcompatible1) (Ordinal pf1)))
                           (restrPermMap (permMapsInv_lt (perm_comp Hcompatible2) (Ordinal pf2)))).
      { eapply corestep_disjoint_mem_obs_id
        with (m1i := m1i) (m2 := m2)
                          (p1j := perm_maps tp1 (Ordinal pf1)).
        - eapply (mem_canonical Hcompatible1).
        - unfold getThreadR. subst tp2. simpl.
          rewrite if_false. pf_cleanup. auto.
          apply/eqP; intro Hcontra; inversion Hcontra; auto.
        - eassumption.
        - inversion Htp_sim. destruct Hinv; eauto.
        - eassumption.
      } 
      assert (mem_obs_eq α (restrPermMap
                              (permMapsInv_lt (perm_comp Hcompatible1)
                                              (Ordinal (n:=num_threads tp1) (m:=j) pf1)))
                         (restrPermMap
                            (permMapsInv_lt (perm_comp Hcompatible')
                                            (Ordinal (n:=num_threads tp1') (m:=j) pf1'))))...
    }
  Qed.

  Lemma dry_step_sim_invariant_r :
    forall (tp1 tp1' tp2' : thread_pool) (m1 m1' m2' : mem) (i j : nat)
      (α: block -> block) (Hneq: i <> j) (pfi': containsThread tp1' i)
      (Hcompatible1': mem_compatible tp1' m1')
      (Htp_sim: weak_tp_sim tp1 tp1' j α)
      (Hmem_sim: mem_sim tp1 tp1' m1 m1' j α)
      (Hstep: dry_step pfi' Hcompatible1' tp2' m2')
      (Hcompatible2: mem_compatible tp2' m2'),
      weak_tp_sim tp1 tp2' j α /\ mem_sim tp1 tp2' m1 m2' j α.
  Proof with (eauto 3 with mem).
    intros; inversion Hstep as [tp' c m1i' m' c2' Hrestrict Hcode Hcorestep Htp2].
    subst tp' m'.
    split.
    { (* Proof of tp_sim *)
      inversion Htp_sim.
      assert (pf2': j < num_threads tp2')
        by (subst; simpl; auto).
      eapply @Tp_weak_sim with (pf := pf) (pf' := pf2'); simpl; eauto.
      - subst; auto.
      - subst; auto.
      - subst; simpl. rewrite if_false. simpl in pf2'. pf_cleanup. eassumption.
        apply/eqP. intros Hcontra; inversion Hcontra; auto.
      - eapply @updThread_invariants with (tp := tp1'); eauto.
    }
    { (* Proof of mem_sim *)
      inversion Hmem_sim as [pf1 pf1' Hcompatible1 ?]. pf_cleanup.
      assert (pf2': j < num_threads tp2')
        by (subst; simpl; auto).
      remember (restrPermMap (permMapsInv_lt (perm_comp Hcompatible2) (Ordinal pf2')))
        as m2'j eqn:Hrestr2_j;
        symmetry in Hrestr2_j.
      pf_cleanup.
      eapply Mem_sim with (Hcomp := Hcompatible1) (Hcomp' := Hcompatible2)
                                                  (pf := pf1) (pf' := pf2')...
      assert (Hobs_12j: mem_obs_eq id (restrPermMap
                                         (permMapsInv_lt (perm_comp Hcompatible1') (Ordinal pf1')))
                                   (restrPermMap
                                      (permMapsInv_lt (perm_comp Hcompatible2)
                                                      (Ordinal  pf2')))).
      { subst tp2'. simpl in Hrestr2_j. simpl.
        pf_cleanup.
        eapply corestep_disjoint_mem_obs_id
        with (m1i := m1i') (m2 := m2')
                          (p1j := perm_maps tp1' (Ordinal pf1')).
        - apply (mem_canonical Hcompatible1').
        - rewrite if_false. pf_cleanup. reflexivity.
          apply/eqP; intro Hcontra; inversion Hcontra; auto.
        - eassumption.
        - inversion Htp_sim. destruct Hinv'. eauto.
        - eassumption.
      }
      eapply mem_obs_trans...
    } 
   Qed.

  Hypothesis corestep_obs_eq :
    forall c1 c2 m1 m1' m2 α
      (Hsim: mem_obs_eq α m1 m1')
      (Hstep: corestep the_sem the_ge c1 m1 c2 m2),
    exists m2',
      corestep the_sem the_ge (rename_code α c1) m1' (rename_code α c2) m2'
      /\ mem_obs_eq α m2 m2'.

  Lemma mem_obs_eq_restr:
    forall (tp tp' : thread_pool) (m m' : mem) (α : block -> block) 
      (i : nat) (pf : i < num_threads tp) (c' : cT)
      (pf' : i < num_threads tp')
      (Hinv: invariant (updThread tp (Ordinal pf) (Krun c') (getCurPerm m) (counter tp)))
      (Hinv': invariant (updThread tp' (Ordinal pf') (rename_core α (Krun c'))
                                   (getCurPerm m') (counter tp')))
      (Hcompatible' : mem_compatible (updThread tp'
                                                (Ordinal pf')
                                                (rename_core α (Krun c')) (getCurPerm m') 
                                                (counter tp')) m')
      (pf2 : i < num_threads (updThread tp (Ordinal pf) (Krun c')
                                        (getCurPerm m) (counter tp)))
      (pf2' : i < num_threads (updThread tp' (Ordinal pf') (rename_core α (Krun c'))
                                         (getCurPerm m') (counter tp')))
      (Hcompatible : mem_compatible
                       (updThread tp (Ordinal pf) (Krun c') (getCurPerm m) (counter tp)) m)
      (Hobs : mem_obs_eq α m m'),
      mem_obs_eq α
                 (restrPermMap (permMapsInv_lt (perm_comp Hcompatible) (Ordinal pf2)))
                 (restrPermMap (permMapsInv_lt (perm_comp Hcompatible') (Ordinal pf2'))).
  Proof.
    intros.
    destruct Hobs as [val_obs_eq cur_obs_eq].
    assert (Hcanonical_max: isCanonical (getMaxPerm m))
      by (apply (mem_canonical Hcompatible)).
    assert (Hcanonical_max': isCanonical (getMaxPerm m'))
      by  (apply (mem_canonical Hcompatible')).
    constructor.
    { simpl.
      intros. unfold Mem.perm in Hperm.
      assert (Heq:= restrPermMap_correct (permMapsInv_lt (perm_comp Hcompatible) (Ordinal pf2))
                                         b1 ofs (canonical Hinv (Ordinal pf2)) Hcanonical_max).
      destruct Heq as [_ HeqCur].
      apply val_obs_eq; auto.
      unfold Mem.perm. rewrite HeqCur in Hperm. simpl in Hperm.
      rewrite if_true in Hperm.
        by rewrite getCurPerm_correct in Hperm.
          by pf_cleanup.
    }
    { intros.
      assert (Heq:= restrPermMap_correct (permMapsInv_lt (perm_comp Hcompatible) (Ordinal pf2))
                                         b1 ofs (canonical Hinv (Ordinal pf2)) Hcanonical_max).
      assert (Heq':= restrPermMap_correct (permMapsInv_lt (perm_comp Hcompatible') (Ordinal pf2'))
                                          b2 ofs (canonical Hinv' (Ordinal pf2')) Hcanonical_max').
      destruct Heq as [_ Heq].
      destruct Heq' as [_ Heq'].
      rewrite Heq Heq'. pf_cleanup. simpl. rewrite if_true; auto.
      rewrite if_true; auto. do 2 rewrite getCurPerm_correct; auto.
    }
  Qed.

  Lemma dry_step_sim_aux :
    forall (tp1 tp2 tp1' : thread_pool) (m1 m2 m1' : mem) α (i : nat)
      (pfi : containsThread tp1 i)
      (pfi' : containsThread tp1' i)
      (Hcompatible1: mem_compatible tp1 m1)
      (Hcompatible1': mem_compatible tp1' m1')
      (Htp_simi: weak_tp_sim tp1 tp1' i α)
      (Hmem_simi: mem_sim tp1 tp1' m1 m1' i α)
      (Hstep1: dry_step pfi Hcompatible1 tp2 m2),
    exists tp2' m2', dry_step pfi' Hcompatible1' tp2' m2' /\
                (forall tid, weak_tp_sim tp1 tp1' tid α -> weak_tp_sim tp2 tp2' tid α) /\
                (forall tid, mem_sim tp1 tp1' m1 m1' tid α ->
                        mem_sim tp2 tp2' m2 m2' tid α).
  Proof with (eauto 3 with mem).
    intros.
    assert (Hcompatible2: mem_compatible tp2 m2)
      by (inversion Htp_simi; eapply dry_step_compatible with (tp := tp1); eauto).
    inversion Hstep1 as [tp' c m1i m' c2 Hrestrict_pmap Hinv Hcode Hcorestep Htp2].
    subst tp' m'.
    inversion Hmem_simi as [pf_tid0 pf_tid0'
                                    Hmem_comp0 Hcompatible'];
      unfold containsThread in *; pf_cleanup.
    rewrite Hrestrict_pmap in Hobs.
    destruct (corestep_obs_eq _ _ _ Hobs Hcorestep) as [m2' [Hcore' Hobs']].
    inversion Htp_simi.
    unfold getThreadC in Hcode.
    pf_cleanup.
    rewrite Hcode in Hpool.
    assert (Hget': getThreadC tp1' (Ordinal pfi') = rename_core α (Krun c))
           by (by unfold getThreadC).
    remember (updThread tp1' (Ordinal pfi') (rename_core α (Krun c2))
                        (getCurPerm m2') (counter tp1')) as tp2' eqn:Htp2'.
    exists tp2'; exists m2'.
    assert (Hstep': dry_step pfi' Hcompatible1' tp2' m2')
      by (eapply step_dry; eauto).
    split; [eassumption |].
    split.
    { (* Proof of tp_sim *)
      intros tid Htp_sim.
      subst tp2' tp2.
      destruct (tid < num_threads ((updThread tp1 (Ordinal pfi)
                                              (Krun c2) (getCurPerm m2)
                                              (counter tp1)))) eqn:pf_tid;
        [|inversion Htp_sim;
          simpl in pf_tid; unfold is_true in *; congruence]. 
      destruct (tid < num_threads
                        ((updThread tp1' (Ordinal (n:=num_threads tp1') pfi')
                                    (rename_core α (Krun c2)) (getCurPerm m2') 
                                    (counter tp1')))) eqn:pf_tid';
        [|inversion Htp_sim;
           simpl in pf_tid'; unfold is_true in *; congruence].
      apply Tp_weak_sim with (pf := pf_tid) (pf' := pf_tid'). simpl. assumption.
      simpl.
      destruct (tid == i) eqn:Htid_eq;
        move/eqP:Htid_eq=>Htid_eq.
      + subst; simpl. rewrite if_true. rewrite if_true.
        reflexivity. apply/eqP. apply f_equal.
        simpl in pf_tid'. erewrite leq_pf_irr; eauto.
        apply/eqP. pf_cleanup. apply f_equal.
        erewrite leq_pf_irr; eauto.
      + rewrite if_false. rewrite if_false.
        inversion Htp_sim.
        simpl in pf_tid, pf_tid'. pf_cleanup.
        assert (pf = pf_tid) by (erewrite leq_pf_irr; eauto); subst pf.
        rewrite Hpool0.
        do 2 apply f_equal.
        erewrite leq_pf_irr; eauto.
        apply/eqP. intro Hcontra. inversion Hcontra; auto.
        apply/eqP. intro Hcontra. inversion Hcontra; auto.
        match goal with
          | [|- invariant ?Expr] => remember Expr as tp2
        end.
        eapply @updThread_invariants with (tp := tp1) (tp' := tp2); eauto.
        match goal with
          | [|- invariant ?Expr] => remember Expr as tp2'
        end.
        eapply @updThread_invariants with (tp := tp1') (tp' := tp2'); eauto.
    }
    { (* Proof of mem_sim *)
      intros tid Hmem_sim. subst tp2'.
      inversion Hmem_sim as [pf_tid pf_tid' Hcomp2 Hcomp2' Hobs_tid].
      assert (pf2_tid: tid < num_threads ((updThread tp1 (Ordinal pfi)
                                                     (Krun c2) (getCurPerm m2) (counter tp1))))
        by (simpl in *; assumption).
      assert (pf2_tid':
                tid < num_threads
                        (updThread tp1' (Ordinal pfi')
                                   (rename_core α (Krun c2)) (getCurPerm m2') 
                                   (counter tp1')))
        by (simpl in *; assumption).
      destruct (tid == i) eqn:Htid_eq; move/eqP:Htid_eq=>Htid_eq.
      + subst tid. subst tp2.
        apply dry_step_compatible in Hstep'; eauto.
        eapply Mem_sim with (pf := pf2_tid) (pf' := pf2_tid') (Hcomp := Hcompatible2)
                                            (Hcomp' := Hstep'); simpl;
        pf_cleanup.
        eapply mem_obs_eq_restr; eauto.
        eapply dry_step_invariants with (tp := tp1); eauto.
        eapply updThread_invariants; eauto.
      + subst tp2.
        assert (Hobs_eq2: mem_obs_eq id
                                     (restrPermMap (permMapsInv_lt (perm_comp Hcompatible1)
                                                                   (Ordinal pf_tid)))
                                     (restrPermMap (permMapsInv_lt (perm_comp Hcompatible2)
                                                                   (Ordinal pf2_tid)))).
        { simpl. eapply corestep_disjoint_mem_obs_id; eauto.
          - apply (mem_canonical Hcompatible1).
          - rewrite if_false. unfold getThreadR. by pf_cleanup.
            apply/eqP; intro Hcontra; inversion Hcontra; auto.
          - apply (no_race Hinv); auto.
        }
        apply dry_step_compatible in Hstep'; eauto.
        assert (Hobs_eq2': mem_obs_eq id
                                     (restrPermMap (permMapsInv_lt (perm_comp Hcompatible1')
                                                                   (Ordinal pf_tid')))
                                     (restrPermMap (permMapsInv_lt (perm_comp Hstep')
                                                                   (Ordinal pf2_tid')))).
        { simpl. eapply corestep_disjoint_mem_obs_id; eauto.
          - apply (mem_canonical Hcompatible1').
          - rewrite if_false. unfold getThreadR. by pf_cleanup.
            apply/eqP; intro Hcontra; inversion Hcontra; auto.
          - apply (no_race Hinv'); auto.
        }
        assert (Hobs_trans : mem_obs_eq α (restrPermMap (permMapsInv_lt (perm_comp Hcompatible2)
                                                                        (Ordinal pf2_tid)))
                                        (restrPermMap (permMapsInv_lt (perm_comp Hcompatible1')
                                                                      (Ordinal pf_tid'))))
          by (pf_cleanup; simpl; eapply mem_obs_trans_comm; eauto).
        eapply Mem_sim with (pf := pf2_tid) (pf' := pf2_tid') (Hcomp := Hcompatible2)
                                            (Hcomp' := Hstep').
        eapply mem_obs_trans; eauto.
    }
  Qed.
  
  Lemma dry_step_sim :
    forall (tp1 tp2 tp3 tp1' : thread_pool) (m1 m2 m3 m1' : mem) α
      (Hinvariant: invariant tp1)
      (Hinvariant': invariant tp1')
      (Hcompatible: mem_compatible tp1 m1)
      (Hcompatible': mem_compatible tp1' m1')
      (Hcompatible2: mem_compatible tp2 m2)
      (Hsim: forall tid, tid < num_threads tp1 -> tp_sim tp1 tp1' tid α /\
                                            mem_sim tp1 tp1' m1 m1' tid α)
      (i j : nat) (Hneq: i <> j) (pfi : containsThread tp1 i) (pfj : containsThread tp2 j)
      (Hstep1: dry_step pfi Hcompatible tp2 m2)
      (Hstep2: dry_step pfj Hcompatible2 tp3 m3),
    exists tp2' m2' tp3' m3' (pfj' : containsThread tp1' j)
      (pfi': containsThread tp2' i) (Hcompatible2': mem_compatible tp2' m2'),
      dry_step pfj' Hcompatible' tp2' m2' /\
      dry_step pfi' Hcompatible2' tp3' m3' /\
      (forall tid, tid < num_threads tp3 -> tp_sim tp3 tp3' tid α /\
                                      mem_sim tp3 tp3' m3 m3' tid α).
  Proof. Admitted.
 (*   intros.
    (* j-simulation of tp2-tp1' *)
    assert (Hsimj_21': tp_sim tp2 tp1' j α /\ mem_sim tp2 tp1' m2 m1' j R).
    { inversion Hstep1; step_absurd; subst;
      try (clear Hupd_mem; step_absurd).
      simpl in pfj. destruct (Hsim _ pfj).
      eapply corestep_sim_invariant_l; eauto.
      rewrite Hsched. reflexivity.
    }
    destruct Hsimj_21' as [Htpsimj_21' Hmemsimj_21'].
    (* j-simulation of tp3-tp2' *)
    assert (Hsimj_32':
              exists tp2' m2',
                fstep tp1' m1' tp2' m2' /\
                (forall tid, tp_sim tp2 tp1' tid α -> tp_sim tp3 tp2' tid R) /\
                (forall tid,
                   mem_sim tp2 tp1' m2 m1' tid α -> mem_sim tp3 tp2' m3 m2' tid R)).
    { eapply corestep_sim_aux with (tp1 := tp2) (tp2 := tp3); eauto.
      - inversion Hstep1; step_absurd; subst; try (clear Hupd_mem; step_absurd).
        simpl. rewrite Hsched. reflexivity.
      - rewrite Hsched'. reflexivity.
    }
    destruct Hsimj_32' as [tp2' [m2' [Hstep1' [Htp_sim32' Hmem_sim32']]]].
    (* i-simulation of tp1-tp2' *)
    assert (Hsimi_12': tp_sim tp1 tp2' i α /\ mem_sim tp1 tp2' m1 m2' i R).
    { assert (pfj': j < num_threads tp1')
        by (inversion Htpsimj_21'; assumption).
      destruct (Hsim _ pfi).
      eapply corestep_sim_invariant_r with (pfi' := pfj') (c := rename_code α c2);
        eauto.
      rewrite Hsched'. reflexivity.
      inversion Htpsimj_21'. unfold getThreadC in *. pf_cleanup. rewrite <- Hpool.
      rewrite Hget2. reflexivity.
        by apply rename_code_at_ext.
    }
    destruct Hsimi_12' as [Htpsimi_12' Hmemsimi_12'].
    (* i-simulation of tp2-tp3' *)
    assert (Hsimi_23':
              exists tp3' m3',
                fstep tp2' m2' tp3' m3' /\
                (forall tid, tp_sim tp1 tp2' tid α -> tp_sim tp2 tp3' tid R) /\
                (forall tid,
                   mem_sim tp1 tp2' m1 m2' tid α -> mem_sim tp2 tp3' m2 m3' tid R)).
    { assert (Hget1': forall pfj',
                        getThreadC tp1' (Ordinal (m := j) pfj') = rename_core α (Krun c2)).
      { intros. inversion Htpsimj_21'. unfold getThreadC in *.
        rewrite <- Hget2. pf_cleanup. rewrite Hpool. reflexivity. }
      assert (Hat_external1': semantics.at_external the_sem (rename_code α c2) = None)
        by (by apply rename_code_at_ext).
      simpl in Hget1'.
      inversion Hstep1';
      repeat match goal with
        | [H1: List.hd_error (schedule ?Tp) = Some ?Tid,
               H2: schedule ?Tp = _ |- _] => rewrite H2 in H1; inversion H1;
                                             subst Tid
        | [pf: is_true (?Tid < n (num_threads tp1')) |- _] => specialize (Hget1' pf)
        | [H1: getThreadC tp1' _ = _, H2: getThreadC tp1' _ = Krun ?C |- _] =>
          rewrite H1 in H2; inversion H2; subst C
             end; step_absurd. subst m m' tp.
      - assert (Heq2': sval pnew = getPermMap m2')
          by (symmetry; eapply updPermMap_get; eauto).
        rewrite <- Hunion in Heq2'.
        eapply corestep_sim_aux with (tp1 := tp1) (tp2 := tp2) (c1 := c1); eauto.
        rewrite Hsched. simpl. reflexivity.
        subst tp'. simpl. rewrite Hsched'. reflexivity. rewrite H1.
        assumption.
        rewrite H1. assumption.
      - inversion Htpsimj_21'. exfalso. clear - Htid0_lt_pf pf'. ssromega.
    }
    destruct Hsimi_23' as [tp3' [m3' [Hstep2' [Htp_sim23' Hmem_sim23']]]].
    exists tp2' m2' tp3' m3'; split; auto; split; auto.
    intros tid pf3_tid.
    assert (Hnum_eq: num_threads tp3 = num_threads tp1).
    { specialize (Htp_sim32' _ Htpsimj_21'). inversion Htpsimi_12';
        inversion Htp_sim32'. rewrite Hnum. assumption. }
    destruct (i == tid) eqn:Htid; move/eqP:Htid=>Htid; subst.
    + eapply corestep_sim_invariant_l; eauto.
      inversion Hstep1; step_absurd; subst; try (clear Hupd_mem; step_absurd).
      simpl. rewrite Hsched. reflexivity.
    + assert (Hsimtid_21': tp_sim tp2 tp1' tid α /\ mem_sim tp2 tp1' m2 m1' tid R).
      { inversion Hstep1; step_absurd; subst; try (clear Hupd_mem; step_absurd).
        simpl in pf3_tid.
        rewrite Hnum_eq in pf3_tid.
        destruct (Hsim _ pf3_tid).
        eapply corestep_sim_invariant_l; eauto.
        rewrite Hsched. reflexivity.
      }
      destruct Hsimtid_21' as [Htpsimtid_21' Hmemsimtid_21'].
      assert (Hget1': forall pfj',
                        getThreadC tp1' (Ordinal (m := j) pfj') = rename_core α (Krun c2)).
      { intros. inversion Htpsimj_21'. unfold getThreadC in *.
        rewrite <- Hget2. pf_cleanup. rewrite Hpool. reflexivity. }
      assert (Hat_external1': semantics.at_external the_sem (rename_code α c2) = None)
        by (by apply rename_code_at_ext).
      simpl in Hget1'.
      inversion Htpsimj_21'.
      inversion Hstep1';
        repeat match goal with
                 | [H1: List.hd_error (schedule ?Tp) = Some ?Tid,
                        H2: schedule ?Tp = _ |- _] => rewrite H2 in H1; inversion H1;
                                                      subst Tid
                 | [pf: is_true (?Tid < n (num_threads tp1')) |- _] => specialize (Hget1' pf)
                 | [H1: getThreadC tp1' _ = _, H2: getThreadC tp1' _ = Krun ?C |- _] =>
                   rewrite H1 in H2; inversion H2; subst C
               end; step_absurd. subst m m' tp tp'.
      inversion  Htpsimi_12'. 
      eapply corestep_sim_invariant_r with
      (j := tid) (tp1' := tp2') (c := rename_code α c1) (pfi' := pf'0);
        eauto.
      subst tp2'.
      simpl. rewrite Hsched'. reflexivity.
      unfold getThreadC in *. 
      pf_cleanup. rewrite Hget1 in Hpool0. simpl in Hpool0. rewrite Hpool0. reflexivity.
        by apply rename_code_at_ext.
  Qed.*)

End FineStepLemmas.
End FineStepLemmas.



  
Module FineSafety.
Section FineSafety.

  Import Concur ThreadPool MemoryObs SimDefs StepLemmas mySem.
  Require Import sepcomp.closed_safety.

  Context {the_ge : G}.
  Notation invariant := (@invariant cT G Sem).
  
  Variable rename_code : (block -> block) -> cT -> cT.

  Variable init_memory : thread_pool -> Mem.mem.

  Definition fstep A := (corestep (fine_semantics A) the_ge).
  Definition coarse_safety (tp : thread_pool) m (sched : myFineSemantics.Sch) A :=
    safeN (coarse_semantics A) the_ge (length sched) (sched,tp) m.

  Definition fine_safety (tp : thread_pool) m sched A :=
    safeN (fine_semantics A) the_ge (length sched) (sched,tp) m.

   Lemma safe_corestepN :
    forall tp m sched A
      (Hsafe: fine_safety tp m sched A),
    exists tp' m',
      corestepN (fine_semantics A) the_ge (size sched)
                (sched,tp) m (nil,tp') m'.
  Proof.
    intros tp m sched A Hsafe.
    generalize dependent tp. generalize dependent m.
    induction sched as [|n sched]; intros.
    - exists tp m. reflexivity.
    - unfold fine_safety in *. simpl in Hsafe.
      destruct Hsafe as [Hstep Hsafe].
      destruct Hstep as [[sched' tp'] [m' Hstep]].
      specialize (Hsafe _ _ Hstep).
      assert (sched' = sched)
        by (inversion Hstep; subst; simpl in *; auto); subst sched'.
      destruct (IHsched _ _ Hsafe) as [tp'' [m'' HcorestepN]].
      exists tp'' m''.
      simpl in *.
      do 2 eexists; eauto.
  Qed.

  Class InternalSteps :=
    { 
  
   
       
 
Module Similar.
Section CoreSimilar.

  Context {sem : Modsem.t}.
  Notation the_sem := (Modsem.sem sem).
  Variable the_ge : Genv.t (Modsem.F sem) (Modsem.V sem).
  
  Class core_similar :=
    {
      mem_similar : mem -> mem -> Prop;
      step_similar : forall c m c' m' m''
                            (Hmem_sim: mem_similar m m'')
                            (Hstep: corestep the_sem the_ge c m c' m'),
                     exists m''', corestep the_sem the_ge c m'' c'  m''' /\ mem_similar m'' m'''
    }.

End CoreSimilar.

Section Similar.

  Import ThreadPool.
  Context {sem : Modsem.t}.

  Notation thread_pool := (t sem).
  Notation the_sem := (Modsem.sem sem).
  Notation perm_map := PermMap.t.

  Variable aggelos : nat -> perm_map.

  Variable the_ge : Genv.t (Modsem.F sem) (Modsem.V sem).

  Inductive tp_similar (tp tp' : thread_pool) : Prop :=
  | tp_sim : forall
               (Hnum_threads: num_threads tp = num_threads tp')
               (Hsim_pool : forall tid, (pool tp) tid = (pool tp') tid)
               (H

  
                            
(* Simulation between fine and coarse grained semantics *)
Section ConcurEquiv.

  Import ThreadPool.
  Import FineConcur Concur.
  Context {sem : Modsem.t}.

  Notation thread_pool := (t sem).
  Notation the_sem := (Modsem.sem sem).
  Notation perm_map := PermMap.t.

  Variable aggelos : nat -> perm_map.

  Variable the_ge : Genv.t (Modsem.F sem) (Modsem.V sem).


  (* Relating a fine grained and a coarse grained schedule*)
  Variable fsched : nat -> nat.
  
   
  Definition trace (step : forall sem : Modsem.t,
                             (nat -> perm_map) ->
                             (nat -> nat) ->
                             Genv.t (Modsem.F sem) (Modsem.V sem) ->
                             Top.pool sem -> mem -> Top.pool sem -> mem -> Prop)
             (sched : nat -> nat) :=
    {xs : seq (thread_pool * mem) |
     forall x y, In2 x y xs ->
                 step _ aggelos sched the_ge (fst x) (snd x) (fst y) (snd y)}.
  
  Inductive obs (tp : thread_pool) : trace -> Prop :=
  | obs_chd : forall tr tp' m m',
                  

  Lemma pf1 : 1 < 5. auto. Defined.
  Lemma pf2 : 2 < 5. auto. Defined.
  
  Eval compute in buildSched ((schedCore (Ordinal pf1)) ::
                                                        (schedCore (Ordinal pf2)) ::
                                                        (schedCore (Ordinal pf1)) ::
                                              (schedCore (Ordinal pf2)) ::
                                              (schedExt (Ordinal pf1)) ::
                                              (schedExt (Ordinal pf2)) ::
                                              (schedCore (Ordinal pf2)) :: nil).
  
  
  Require Import Coq.Relations.Relation_Operators.

  Definition multifine sched :=
    clos_trans _ (fun p1 p2 => fstep aggelos sched the_ge
                                     (fst p1) (snd p1) (fst p2) (snd p2)).

  Lemma csched_exists :
    forall {m} (pf: m > 0) (fs : seq (schedType m)) (counter : nat),
    exists (csched : nat -> nat),
      forall i,
        i < size (buildSched fs) ->
        csched (counter + i) =
        nth 0
            (map (fun (x : schedType m) => match x with
                        | schedCore n => nat_of_ord n
                        | schedExt n => nat_of_ord n
                                           end) (buildSched fs)) i.
  Proof.
    intros.
    generalize dependent (buildSched fs).
    apply last_ind.
    { simpl.
      exists (fun (n : nat) => 0).
      intros ? Hcontra.
      exfalso. by rewrite ltn0 in Hcontra. }
    { intros cs c IHcs.
      destruct IHcs as [csched IHcs].
      exists (fun n => if n == (counter0 + size cs) then
                         nat_of_ord (match c with
                                       | schedCore k => k
                                       | schedExt k => k end)
                       else csched n).
      intros i Hsize.
      rewrite size_rcons ltnS leq_eqVlt in Hsize.
      move/orP:Hsize => [/eqP Heq | Hprev].
      { subst. rewrite eq_refl.
        erewrite nth_map.
        erewrite nth_rcons. rewrite ltnn eq_refl.
        case c; auto.
          by rewrite size_rcons. }
      { rewrite ifN_eq.
        specialize (IHcs i Hprev).
        erewrite nth_map in *; auto.
        erewrite nth_rcons. rewrite Hprev. eauto.
        rewrite size_rcons. auto.
        apply contraNneq with (b:= false). auto. move/eqP => Hcontra. exfalso.
        rewrite eqn_add2l in Hcontra.
        move/eqP: Hcontra => Hcontra. subst. by rewrite ltnn in Hprev.
        auto.
        Grab Existential Variables. auto.
        auto. auto.
      }
    }
  Qed. 

                End ConcurEquiv.


                
(*
(* Computing the union of permission maps*)
Section PermMapConstruction.

 Import Maps SeqLemmas.

 (* This cannot be partial because we do not know the domain of the functions on ofs*)
 Definition pmap_union (pmap1 pmap2 : PermMap.t)
             (Hcanonical1: isCanonical pmap1)
             (Hcanonical2: isCanonical pmap2)
             (Hdisjoint : permMapsDisjoint pmap1 pmap2) : PermMap.t.
   refine
     ({| PermMap.next := Pos.max (PermMap.next pmap1) (PermMap.next pmap2);
          PermMap.map :=
            (fun ofs kind => None,
             Maps.PTree.combine 
               (fun of1 of2 =>                  
                  let f1 := match of1 with
                              | Some f1 => f1
                              | None => (fst (PermMap.map pmap1))
                            end in
                  let f2 := match of2 with
                              | Some f2 => f2
                              | None => (fst (PermMap.map pmap2))
                            end in   
                  match of1, of2 with
                    | None, None => None
                    | _, _ => 
                      Some (fun ofs kind =>
                              let p1 := f1 ofs kind in
                              let p2 := f2 ofs kind in
                              match kind with
                                | Max =>
                                  perm_max p1 p2
                                | Cur =>
                                  match perm_union p1 p2 with
                                    | Some pu' => pu'
                                    | None => _
                                  end
                              end)
                  end)
               (snd (PermMap.map pmap1)) (snd (PermMap.map pmap2)));
          PermMap.max := _;
          PermMap.nextblock := _ |}).
   Proof.
     {
       unfold Maps.PMap.get. unfold isCanonical in *. simpl. intros.
       rewrite PTree.gcombine.
       destruct (Hdisjoint b ofs) as [pu Hunion].
       unfold permMapsDisjoint in Hdisjoint.
       destruct (((PermMap.map pmap1).2) ! b)
         as [f1|] eqn:Hget1, (((PermMap.map pmap2).2) ! b) as [f2|] eqn:Hget2.
       - unfold PMap.get in Hunion. rewrite Hget1 Hget2 in Hunion.
         rewrite Hunion.
         destruct pmap1, pmap2. simpl in *.
         unfold PMap.get in max, max0.
         eapply permOrd_monotonic; eauto.
         specialize (max b ofs). rewrite Hget1 in max. auto.
         specialize (max0 b ofs). rewrite Hget2 in max0. auto.
       - rewrite Hcanonical2. rewrite perm_max_comm.
         rewrite perm_union_comm. simpl.
         destruct pmap1. simpl in *.
         specialize (max b ofs). unfold PMap.get in max. rewrite Hget1 in max.
         destruct (f1 ofs Max) as [p|]; auto. destruct p; auto.
       - rewrite Hcanonical1. destruct pmap2. simpl in *.
         specialize (max b ofs). unfold PMap.get in max.
         rewrite Hget2 in max.  destruct (f2 ofs Max) as [p|]; auto.
       destruct p; auto.
       - constructor.
       - reflexivity.
     }
     { intros b ofs k Hnext. clear Hdisjoint. unfold isCanonical in *.
       unfold PMap.get. rewrite PTree.gcombine.
       destruct pmap1 as [next map max nextblock],
                         pmap2 as [next2 map2 max2 nextblock2]; simpl in *.
       assert (Hnext1: ~ Coqlib.Plt b next).
       { apply Pos.le_nlt in Hnext.
         apply Pos.max_lub_l in Hnext.
         unfold Coqlib.Plt.  intro Hcontra.
         apply Pos.le_nlt in Hnext. auto.
       }
       assert (Hnext2: ~ Coqlib.Plt b next2).
       { apply Pos.le_nlt in Hnext.
         apply Pos.max_lub_r in Hnext.
         unfold Coqlib.Plt.  intro Hcontra.
         apply Pos.le_nlt in Hnext. auto.
       }
       specialize (nextblock b ofs k Hnext1).
       specialize (nextblock2 b ofs k Hnext2).
       unfold PMap.get in nextblock, nextblock2.
       destruct (map.2 ! b)
         as [f1|] eqn:Hget1, (map2.2 ! b) as [f2|] eqn:Hget2; auto;
       rewrite nextblock; rewrite nextblock2; simpl;
       destruct k; reflexivity.
       reflexivity.
       Grab Existential Variables. auto. auto.
     }
   Defined.

   Lemma pmap_union_result :
     forall pmap1 pmap2 pmap12
            (Hcanonical1: isCanonical pmap1)
            (Hcanonical2: isCanonical pmap2)
            (Hdisjoint : permMapsDisjoint pmap1 pmap2) 
            (Hunion: pmap_union Hcanonical1 Hcanonical2 Hdisjoint = pmap12)
            b ofs,
       PMap.get b (PermMap.map pmap12) ofs Cur = PMap.get b (PermMap.map pmap1) ofs Cur \/
       PMap.get b (PermMap.map pmap12) ofs Cur = PMap.get b (PermMap.map pmap2) ofs Cur.
   Proof.
     intros. unfold pmap_union in Hunion; unfold isCanonical in *.
     rewrite <- Hunion. simpl. clear Hunion.  destruct (Hdisjoint b ofs) as [pu Hpu].
     unfold PMap.get in *. simpl. rewrite PTree.gcombine.
     destruct ((PermMap.map pmap1).2 ! b) as [f1|] eqn:Hget1;
       destruct ((PermMap.map pmap2).2 ! b) as [f2|] eqn:Hget2;
     try match goal with
       | [H: perm_union ?Expr1 ?Expr2 = _ |- _] =>
         destruct (perm_union_result Expr1 Expr2 H) as [? | ?]; subst; rewrite H 
     end; auto. rewrite Hcanonical1. auto. reflexivity.
   Defined.

   Lemma pmap_union_result_union :
     forall pmap1 pmap2 pmap12
            (Hcanonical1: isCanonical pmap1)
            (Hcanonical2: isCanonical pmap2)
            (Hdisjoint : permMapsDisjoint pmap1 pmap2) 
            (Hunion: pmap_union Hcanonical1 Hcanonical2 Hdisjoint = pmap12)
            b ofs,
       Some (PMap.get b (PermMap.map pmap12) ofs Cur) =
       perm_union ((PermMap.map pmap1) !! b ofs Cur) ((PermMap.map pmap2) !! b ofs Cur). 
   Proof.
     intros. unfold pmap_union in Hunion.
     rewrite <- Hunion. simpl. clear Hunion.  destruct (Hdisjoint b ofs) as [pu Hpu].
     unfold PMap.get in *. simpl. rewrite PTree.gcombine.
     destruct ((PermMap.map pmap1).2 ! b) as [f1|] eqn:Hget1;
       destruct ((PermMap.map pmap2).2 ! b) as [f2|] eqn:Hget2;
     try match goal with
       | [H: perm_union ?Expr1 ?Expr2 = _ |- _] =>
         destruct (perm_union_result Expr1 Expr2 H) as [? | ?]; subst; rewrite H 
         end; auto. rewrite Hcanonical1. reflexivity. rewrite Hcanonical2.  reflexivity.
     reflexivity.
   Defined.

   Lemma pmap_union_result_max :
     forall pmap1 pmap2 pmap12
            (Hcanonical1: isCanonical pmap1)
            (Hcanonical2: isCanonical pmap2)
            (Hdisjoint : permMapsDisjoint pmap1 pmap2) 
            (Hunion: pmap_union Hcanonical1 Hcanonical2 Hdisjoint = pmap12)
            b ofs,
       PMap.get b (PermMap.map pmap12) ofs Max =
       perm_max ((PermMap.map pmap1) !! b ofs Max) ((PermMap.map pmap2) !! b ofs Max). 
   Proof.
     intros. unfold pmap_union in Hunion.
     rewrite <- Hunion. simpl. clear Hunion.  destruct (Hdisjoint b ofs) as [pu Hpu].
     unfold PMap.get in *. simpl. rewrite PTree.gcombine.
     destruct ((PermMap.map pmap1).2 ! b) as [f1|] eqn:Hget1;
       destruct ((PermMap.map pmap2).2 ! b) as [f2|] eqn:Hget2;
     try match goal with
       | [H: perm_union ?Expr1 ?Expr2 = _ |- _] =>
         destruct (perm_union_result Expr1 Expr2 H) as [? | ?]; subst; rewrite H 
         end; auto. rewrite Hcanonical1 Hcanonical2. reflexivity. reflexivity.
   Defined.

   Lemma pmap_union_ord :
     forall pmap1 pmap2 pmap12
            (Hcanonical1: isCanonical pmap1)
            (Hcanonical2: isCanonical pmap2)
            (Hdisjoint : permMapsDisjoint pmap1 pmap2) 
            (Hunion: pmap_union Hcanonical1 Hcanonical2 Hdisjoint = pmap12)
            b ofs k,
       Mem.perm_order'' (PMap.get b (PermMap.map pmap12) ofs k)
                        (PMap.get b (PermMap.map pmap1) ofs k) /\
       Mem.perm_order'' (PMap.get b (PermMap.map pmap12) ofs k)
                        (PMap.get b (PermMap.map pmap2) ofs k).
   Proof.
     intros. unfold pmap_union in Hunion.
     rewrite <- Hunion. simpl. clear Hunion.  destruct (Hdisjoint b ofs) as [pu Hpu].
     unfold PMap.get in *. simpl. rewrite PTree.gcombine.
     destruct ((PermMap.map pmap1).2 ! b) as [f1|] eqn:Hget1;
       destruct ((PermMap.map pmap2).2 ! b) as [f2|] eqn:Hget2; destruct k;
       try rewrite Hpu;
       try match goal with
         | [|- context[Max]] => eapply perm_max_ord
         | [|- context[Cur]] => eapply perm_union_ord
       end; eauto.
     rewrite Hcanonical1 Hcanonical2. reflexivity.
     rewrite Hcanonical1 Hcanonical2. reflexivity.
     reflexivity.
   Defined.
   
   Lemma pmap_union_canonical :
     forall pmap1 pmap2 pmap12
            (Hcanonical1: isCanonical pmap1)
            (Hcanonical2: isCanonical pmap2)
            (Hdisjoint : permMapsDisjoint pmap1 pmap2) 
            (Hunion: pmap_union Hcanonical1 Hcanonical2 Hdisjoint = pmap12),
       (PermMap.map pmap12).1 = fun _ _ => None.
     intros. rewrite <- Hunion. unfold pmap_union. simpl. reflexivity.
   Defined.
       
   Lemma pmap_union_inv :
     forall (pmap1 pmap2 pmap3 pu12 : PermMap.t)
            (Hcanonical1: isCanonical pmap1)
            (Hcanonical2: isCanonical pmap2)
            (Hcanonical3: isCanonical pmap3)
            (Hdisjoint12: permMapsDisjoint pmap1 pmap2)
            (Hdisjoint13: permMapsDisjoint pmap1 pmap3)
            (Hdisjoint23: permMapsDisjoint pmap2 pmap3)
            (Hunion12: pmap_union Hcanonical1 Hcanonical2 Hdisjoint12 =
                       pu12),
     exists pf pu, pmap_union (pmap_union_canonical Hunion12) Hcanonical3 pf = pu.
   Proof.
     intros.
     assert (pf : permMapsDisjoint (pu12) (pmap3)).
     { unfold permMapsDisjoint in *. intros b ofs.
       destruct (Hdisjoint12 b ofs) as [p12 Hp12],
                (Hdisjoint13 b ofs) as [p13 Hp13],
                                       (Hdisjoint23 b ofs) as [p23 Hp23].
       destruct (pmap_union_result Hunion12 b ofs) as [Hu12 | Hu12];
         rewrite Hu12; eexists; eauto.
     }
     exists pf.
     eexists. eauto.
   Defined.

   Context {sem : Modsem.t}.
   Variable (tp : ThreadPool.t sem).
   
   Import ThreadPool.
   
   Notation num_threads := (@ThreadPool.num_threads sem tp).

   Lemma permMapsUnion_oblig1:
     forall {A:Type} (l : seq A)
            (p : A) (l' : seq A) (Heq : p :: l' = l),
       List.In p l.
   Proof.
     intros. rewrite <- Heq. left. reflexivity.
   Defined.

   Require Import Coq.Sorting.Sorted.
   Definition ord_lt := fun (x y : 'I_num_threads)  => (nat_of_ord x) < (nat_of_ord y).

   Lemma ord_lt_trans : Relations_1.Transitive ord_lt.
   Proof.
     unfold Relations_1.Transitive. intros x y z Hxy Hyz.
     unfold ord_lt in *. ssromega.
   Defined.

   Definition ord_step := fun (x y : 'I_num_threads) => S (nat_of_ord x) = (nat_of_ord y).

   Definition base_pf : ((n num_threads)-1) < (n num_threads).
     destruct num_threads.
     ssromega.
   Defined.
   
   Inductive threadSeq : nat -> list 'I_num_threads -> Type :=
   | thrSeqN : forall pf,
       threadSeq ((n num_threads)-1) [:: @Ordinal num_threads ((n num_threads) -1) pf]
   | thrSeqS : forall thrSeq i pf
                  (Hseq: threadSeq (S i) thrSeq),
                  threadSeq i ((@Ordinal num_threads i pf) :: thrSeq).

   Definition threadSeq_ordpf {i l} (ts : threadSeq (S i) l) : is_true (i < (n num_threads)).
   Proof.
     inversion ts as [|? ? ? Hts']; subst; clear ts. destruct num_threads. ssromega.
          clear Hts'. destruct num_threads.  simpl in *. ssromega.
   Defined.

   Definition elim_eq_thr {a b l} (Ha: threadSeq a l) :
     forall (H: a == b), threadSeq b l.
     move/eqP=>H. by subst.
   Defined.
                        
   Definition threadsList : sigT (threadSeq 0).
     refine (let fix aux i acc (pf_acc: threadSeq i acc) :=
                 match i with
                   | 0 => fun (Heq : i == 0) =>
                            existT (threadSeq 0) acc _
                   | S n => fun (Heq : i == S n) =>
                              aux n ((@Ordinal
                                        num_threads n (threadSeq_ordpf (elim_eq_thr pf_acc Heq)))
                                       :: acc) _
                 end (eq_refl i)
             in aux ((n num_threads) - 1) [:: @Ordinal num_threads ((n num_threads)-1) base_pf]
                    (thrSeqN base_pf)).
     Proof.
       {move/eqP:Heq=>Heq; by subst. }
       { assert (i = S n) by (move/eqP:Heq; by subst).
         subst. constructor. assumption. }
     Defined.

     Lemma threadSeq_size_pos : forall n l (Hseq: threadSeq n l),
                              size l > 0.
     Proof.
       intros. inversion Hseq; simpl; auto.
     Defined.

     Lemma threadSeq_val : forall n x l (Hl: threadSeq n (x :: l)),
                             n = nat_of_ord x.
     Proof.
       intros. inversion Hl; subst; reflexivity.
     Defined.

     Lemma threadSeq_step : forall n l (Hl: threadSeq n l),
       Sorted ord_step l.
     Proof.
       intros n l. generalize dependent n. induction l as [|a l'].
       - intros. inversion Hl.
       - intros.
         destruct l'. constructor; auto.
         inversion Hl; subst. apply threadSeq_val in Hseq.
         inversion Hl as [|? ? ? Hseq0]; subst.
         constructor. eapply IHl'; eauto.
         constructor. unfold ord_step. rewrite <- Hseq. reflexivity.
     Defined.

     Lemma threadSeq_lt : forall n l (Hl: threadSeq n l),
       Sorted ord_lt l.
     Proof.
       intros n l. generalize dependent n. induction l as [|a l'].
       - intros. inversion Hl.
       - intros.
         destruct l'. constructor; auto.
         inversion Hl; subst. apply threadSeq_val in Hseq.
         inversion Hl as [|? ? ? Hseq0]; subst.
         constructor. eapply IHl'; eauto.
         constructor. unfold ord_lt. rewrite <- Hseq. simpl. ssromega.
     Defined.

     
     Lemma threadSeq_complete :
       forall tid i l (Hl: threadSeq i l) (Hle: i <= tid)
              (Hmax: tid <= num_threads -1),
       exists (pf': tid < num_threads), List.In (Ordinal pf') l.
     Proof.
       intros tid i l. generalize dependent tid. generalize dependent i.
       induction l.
       - intros. inversion Hl.
       - intros. inversion Hl; subst.
         assert (H: tid = num_threads -1) by ssromega.
         rewrite H. exists pf. left. reflexivity.
         rewrite leq_eqVlt in Hle.
         move/orP:Hle=>[Heq | Hlt].
         + move/eqP:Heq=>Heq. subst. exists pf. left; auto.
         + specialize (IHl _ _ Hseq Hlt Hmax). destruct IHl as [pf' HIn].
           exists pf'. right. assumption.
     Defined.
         
      Lemma subSeq_cons : forall {T:eqType} x (s' s : seq T) (Hneq: s' <> x :: s)
                                (Hsub: subSeq s' (x :: s)), subSeq s' s.
     Proof.
       unfold subSeq. intros.
       simpl in Hsub. destruct ((size s).+1 - size s') eqn:Hn.
       exfalso; move/eqP:Hsub=>Hsub. auto.
       replace (size s - size s') with n by ssromega.
       assumption.
     Defined.
      
     Lemma threadSeq_size :
       forall i l (Hseq: threadSeq i l),
         size l = ((n num_threads) - i).
     Proof.
       intros i l. generalize dependent i. induction l; intros.
       - inversion Hseq.
       - inversion Hseq as [|? ? ? Hseq']; subst.
         simpl. clear Hseq IHl. destruct num_threads. ssromega.
         simpl. eapply IHl in Hseq'.
         clear Hseq IHl. destruct num_threads.
         simpl in *. ssromega.
     Defined.
         
     Lemma threadSeq_subSeq :
       forall i l l' (Hseq: threadSeq i l) (Hsub: subSeq l' l)
              (Hl' : l' <> nil),
         threadSeq ((n num_threads) - (size l')) l'.
     Proof.
       intros. generalize dependent l'. generalize dependent i.
       induction l; intros.
       unfold subSeq in Hsub. simpl in Hsub. exfalso. move/eqP:Hsub. auto.
       inversion Hseq as [|? ? ? Hseq']; subst.
       - simpl in *.
         unfold subSeq in Hsub. simpl in Hsub.
         destruct (1- size l') as [|n] eqn:Hn. move/eqP:Hsub=>Hsub.
         rewrite <- Hsub. simpl. constructor.
         exfalso; move/eqP:Hsub=>Hsub; auto.
       - unfold subSeq in Hsub. move/eqP:Hsub=>Hsub.
         simpl in Hsub.
         destruct ((size l).+1 - size l') as [|n] eqn:Hn;
         rewrite Hn in Hsub.
         rewrite <- Hsub; simpl.
         erewrite threadSeq_size; eauto.
         replace (num_threads - (num_threads - i.+1).+1) with i by
             (clear Hsub Hseq Hseq' IHl; destruct num_threads; simpl in *; ssromega).
         assumption.
         eapply IHl; eauto.
         unfold subSeq.
         assert (Heq: size l - size l' = n)
           by (destruct l'; simpl in *; ssromega).
         rewrite Heq. by move/eqP:Hsub.
     Defined.

     (* For the constructive version we assumed that all perm maps are canonical,
        we can lift this assumption since we can compute a canonical version of a perm map.
        Let's use the hypothesis for now and instantiate it later*)
     Hypothesis permMapsCanonical :
       forall tid, isCanonical (perm_maps tp tid).                                   

     Lemma empty_disjoint : forall pmap,
                              permMapsDisjoint pmap emptyPermMap.
     Proof.
       unfold permMapsDisjoint. intros.
       unfold PMap.get. simpl. rewrite PTree.gempty.
       unfold perm_union. destruct ((PermMap.map pmap).2 !b) eqn:Hget;
       match goal with
         | [ |- context[match ?Expr with | _ => _ end]] => destruct Expr
       end; eexists; reflexivity.
     Defined.

     Hypothesis Hrace : race_free tp.
     
     Definition permMapsUnion : {p : PermMap.t | permMapsInv tp p}.
       refine (
           let fix aux l
                   acc (Hl': forall x, List.In x l -> permMapsDisjoint (perm_maps tp x) acc)
                   (Hacc: isCanonical acc)
                   (Hsub: subSeq l (tag threadsList))
                   (Hnext: forall x lhd (Hlst: (tag threadsList) = lhd ++ l)
                                  (HIn: List.In x lhd),
                             ~ Coqlib.Plt (PermMap.next acc) (PermMap.next (getThreadPerm tp x)))
                   (Hperm_ord: forall tid b ofs k lhd (Hlst: (tag threadsList) = lhd ++ l)
                                      (HIn: List.In tid lhd),
                                 Mem.perm_order'' ((PermMap.map acc) !! b ofs k)
                                                  ((PermMap.map (getThreadPerm tp tid)) !! b ofs k))
                   (Hinit: tag threadsList = l -> acc = emptyPermMap)
                   (Hinv_eq: forall lhd (Hlhd: lhd <> [::]) (Hlst: (tag threadsList) = lhd ++ l),
                               (exists tid, List.In tid lhd /\
                                            PermMap.next acc = PermMap.next (getThreadPerm tp tid))
                               /\ (forall (ofs : Z) (b : positive),
                                   exists tid : 'I_num_threads, List.In tid lhd /\
                                                                (PermMap.map (perm_maps tp tid)) !! b ofs Cur =
                                                                (PermMap.map acc) !! b ofs Cur)
                               /\ (forall (ofs : Z) (b : positive),
                                   exists tid : 'I_num_threads,
                                     List.In tid lhd /\
                                     (PermMap.map (perm_maps tp tid)) !! b ofs Max =
                                     (PermMap.map acc) !! b ofs Max))
               :=
               match l with
                 | nil => fun Heq =>
                            exist (fun p => permMapsInv tp p) acc _
                 | tid :: l' =>
                   fun (Heq: tid :: l' = l) =>
                     let p := perm_maps tp tid in
                     aux l'
                         (@pmap_union p acc (permMapsCanonical tid)
                                      Hacc (Hl' tid (permMapsUnion_oblig1 Heq))) _ _ _ _ _ _ _
               end (Logic.eq_refl l)
           in aux (tag threadsList) emptyPermMap _ _ _ _ _ _ _).
       Proof.
         { (* permMapsInv *)
           clear aux. subst. split; [idtac | split; [idtac | split; [idtac | split]]].
           - clear Hinv_eq Hinit Hperm_ord Hnext Hsub Hl'. assumption.
           - intros.
             destruct tid as [tid pf].
             destruct threadsList as [l Hl].
             assert (Hle: 0 <= tid) by ssromega.
             assert (Hmax: tid <= num_threads - 1) by ssromega.
             destruct (threadSeq_complete tid Hl Hle Hmax) as [pf' HIn].
             simpl in Hnext.
             specialize (Hnext (Ordinal pf') l).
             rewrite cats0 in Hnext. specialize (Hnext (Logic.eq_refl l) HIn).
             intros Hcontra.
             assert (Hget: getThreadPerm tp (Ordinal (n:=num_threads) (m:=tid) pf') =
                           getThreadPerm tp (Ordinal (n:=num_threads) (m:=tid) pf)).
             {
               unfold getThreadPerm.
               rewrite (leq_pf_irr _ _ pf pf'). reflexivity. }
             rewrite Hget in Hnext. apply Hnext. assumption. 
           - intros.
             destruct tid as [tid pf].
             destruct threadsList as [l Hl].
             assert (Hle: 0 <= tid) by ssromega.
             assert (Hmax: tid <= num_threads - 1) by ssromega.
             destruct (threadSeq_complete tid Hl Hle Hmax) as [pf' HIn].
             simpl in Hnext.
             specialize (Hperm_ord (Ordinal pf') b ofs Cur l).
             rewrite cats0 in Hperm_ord. specialize (Hperm_ord (Logic.eq_refl l) HIn).
             assert (Hget: getThreadPerm tp (Ordinal (n:=num_threads) (m:=tid) pf') =
                           getThreadPerm tp (Ordinal (n:=num_threads) (m:=tid) pf)).
             {
               unfold getThreadPerm.
               rewrite (leq_pf_irr _ _ pf pf'). reflexivity. }
             rewrite Hget in Hperm_ord.  assumption.
           - intros.
             destruct tid as [tid pf].
             destruct threadsList as [l Hl].
             assert (Hle: 0 <= tid) by ssromega.
             assert (Hmax: tid <= num_threads - 1) by ssromega.
             destruct (threadSeq_complete tid Hl Hle Hmax) as [pf' HIn].
             simpl in Hnext.
             specialize (Hperm_ord (Ordinal pf') b ofs Max l).
             rewrite cats0 in Hperm_ord. specialize (Hperm_ord (Logic.eq_refl l) HIn).
             assert (Hget: getThreadPerm tp (Ordinal (n:=num_threads) (m:=tid) pf') =
                           getThreadPerm tp (Ordinal (n:=num_threads) (m:=tid) pf)).
             {
               unfold getThreadPerm.
               rewrite (leq_pf_irr _ _ pf pf'). reflexivity. }
             rewrite Hget in Hperm_ord.  assumption.
           - clear Hnext Hperm_ord. specialize (Hinv_eq (tag threadsList)).
             destruct (threadsList) as [l Hl]. simpl in *.
             assert (Hempty: l <> [::]) by (inversion Hl; intro Hcontra; discriminate).
             rewrite cats0 in Hinv_eq.
             destruct (Hinv_eq Hempty (Logic.eq_refl _)) as [Hnext [Hcur Hmax]]; clear Hinv_eq.
             split; [idtac | split].
             + clear Hcur Hmax. destruct Hnext as [tid [Hin Hnext]].
               exists tid. assumption.
             + intros ofs b. destruct (Hcur ofs b) as [tid [_ ?]].
               eexists; eassumption.
             + intros ofs b. destruct (Hmax ofs b) as [tid [_ ?]].
               eexists; eassumption. 
         }
         { (* l is race free*)
           clear aux.
           intros tid' Hin.
           assert (Hdis_tid'_acc: permMapsDisjoint acc (perm_maps tp tid')).
           { apply permMapsDisjoint_comm. eapply Hl'.
             rewrite <- Heq. right; assumption. }
           destruct threadsList as [threadsListV threadsListP].
           simpl in *.
           eapply threadSeq_subSeq in threadsListP; eauto.
           apply threadSeq_lt in threadsListP.
           assert (Hdis_tid'_tid: permMapsDisjoint (perm_maps tp tid) (perm_maps tp tid')).
           { rewrite <- Heq in threadsListP.
             apply Sorted_extends in threadsListP.
             eapply List.Forall_forall with (x:=tid') in threadsListP; eauto.
             assert (Hneq: nat_of_ord tid <> nat_of_ord tid').
             { intros Hcontra. subst. unfold ord_lt in threadsListP. ssromega. }
             destruct tid as [ntid pf_tid], tid' as [ntid' pf_tid'].
             eapply Hrace. intros Hcontra; subst. eapply Hneq. simpl. reflexivity.
             apply ord_lt_trans.
           }
           assert (Hdis_tid_acc: permMapsDisjoint (perm_maps tp tid) acc).
           { eapply Hl'. rewrite <-Heq. left; auto. }
           remember ((pmap_union (permMapsCanonical tid) Hacc
                                 (Hl' tid (permMapsUnion_oblig1 Heq)))) as pu.
           symmetry in Heqpu.
           destruct (pmap_union_inv (permMapsCanonical tid') Hdis_tid'_tid Hdis_tid'_acc Heqpu)
             as [pf ?].
           rewrite Heqpu. by apply permMapsDisjoint_comm.
           rewrite <- Heq. intro. discriminate.
         }
         { (* acc is canonical*) clear aux. reflexivity. }
         { (* l is a subSeq of threadsList*)
           unfold subSeq in *.
           rewrite <- Heq in Hsub.
           simpl in Hsub.
           move/eqP:Hsub=>Hsub.
           assert (Hlt: size (tid :: l') <= size (tag threadsList))
             by (eapply drop_size_lt; eapply Hsub).
           simpl in Hlt.
           assert (Hdrop: drop ((size (tag threadsList) - (size l').+1).+1) (tag threadsList) = l')
             by (eapply dropS; eauto).
           assert (Heq': (size (tag threadsList) - (size l').+1).+1 =
                         (size (tag threadsList) - size l')) by ssromega.
           rewrite Heq' in Hdrop. move/eqP:Hdrop; auto.
         }
         { (* Hnext_rec *)
           clear aux Hinv_eq Hinit Hperm_ord.
           intros. simpl.
           destruct l as [|o l]; inversion Heq. subst o. subst l'.
           destruct lhd as [|lhd tid'] using last_ind. by inversion HIn. clear IHlhd.
           rewrite <- cats1 in Hlst.
           rewrite <- catA in Hlst. simpl in Hlst.
           assert (Hsub': subSeq (tid' :: l) (tag threadsList)).
           { unfold subSeq. rewrite Hlst.
             simpl. rewrite size_cat. simpl.
             replace ((size lhd + (size l).+1 - (size l).+1)) with (size lhd) by ssromega.
             apply/eqP.
             apply drop_size_cat. reflexivity.
           }
           assert (Heq': tid' :: l = tid :: l)
             by (eapply subSeq_det; eauto).
           inversion Heq'; subst.
           eapply in_rcons in HIn.
           destruct HIn as [|HIn]; subst.
           assert (Hp: p = getThreadPerm tp tid) by auto. rewrite Hp.
           intros Hcontra.
           unfold Coqlib.Plt in Hcontra.
           apply Pos.max_lub_lt_iff in Hcontra.
           destruct Hcontra as [Hcontra _]. by apply Pos.lt_irrefl in Hcontra.
           specialize (Hnext _ _ Hlst HIn).
           unfold Coqlib.Plt in *. intros Hcontra.
           apply Pos.max_lub_lt_iff in Hcontra.
           destruct Hcontra as [_ Hcontra]. auto.
         }
         { (*Hperm_ord rec*)
           clear aux Hnext.
           intros tid0 b ofs k lhd Hlst HIn.
           destruct l as [|o l]; inversion Heq. subst o. subst l'.
           destruct lhd as [|lhd x] using last_ind. by inversion HIn. clear IHlhd.
           rewrite <- cats1 in Hlst.
           rewrite <- catA in Hlst. simpl in Hlst.
           assert (Hsub': subSeq (x :: l) (tag threadsList)).
           { unfold subSeq. rewrite Hlst.
             simpl. rewrite size_cat. simpl.
             replace ((size lhd + (size l).+1 - (size l).+1)) with (size lhd) by ssromega.
             apply/eqP.
             apply drop_size_cat. reflexivity.
           }
           assert (Heq': x :: l = tid :: l)
             by (eapply subSeq_det; eauto).
           inversion Heq'; subst.
           eapply in_rcons in HIn.
           destruct HIn as [|HIn]; subst.
         - remember (@pmap_union p acc (permMapsCanonical tid) Hacc
                                 (Hl' tid (@permMapsUnion_oblig1 'I_num_threads (tid :: l) tid l Heq)))
             as pu eqn:Hpu.
           symmetry in Hpu.
           eapply (pmap_union_ord Hpu).
         - specialize (Hperm_ord tid0 b ofs k lhd Hlst HIn).
           remember (@pmap_union p acc (permMapsCanonical tid) Hacc
                                 (Hl' tid (@permMapsUnion_oblig1 'I_num_threads (tid :: l) tid l Heq)))
             as pu eqn:Hpu.
           symmetry in Hpu.
           eapply pmap_union_ord with (b := b) (ofs := ofs) (k := k) in Hpu.
           destruct Hpu as [_ Hacc_ord].
           eapply po_trans; eauto. }
        { (*Hinit rec*)
         clear aux Hnext Hperm_ord Hinv_eq.
         intro Hlst. exfalso. rewrite Hlst in Hsub. rewrite <- Heq in Hsub.
         unfold subSeq in Hsub. simpl in Hsub.
         move/eqP:Hsub=>Hsub.
         assert (Hcontra := drop_size_lt _ _ Hsub).
         simpl in Hcontra. ssromega.
        }
        { (*Hinv_eq rec*)
          clear aux Hnext Hperm_ord. intros.
          destruct l as [|o l]; inversion Heq. subst o. subst l'.
          destruct lhd as [|lhd x] using last_ind.
          exfalso; auto.
          clear IHlhd.
          rewrite <- cats1 in Hlst.
          rewrite <- catA in Hlst. simpl in Hlst.
          assert (Hsub': subSeq (x :: l) (tag threadsList)).
          { unfold subSeq. rewrite Hlst.
            simpl. rewrite size_cat. simpl.
            replace ((size lhd + (size l).+1 - (size l).+1)) with (size lhd) by ssromega.
            apply/eqP.
            apply drop_size_cat. reflexivity.
          }
          assert (Heq': x :: l = tid :: l)
            by (eapply subSeq_det; eauto).
          inversion Heq'; subst.
          destruct lhd as [|tid' lhd].
          - apply Hinit in Hlst. subst.
            split; [idtac | split].
            { exists tid. split. simpl. by left.
              simpl. apply Pos.max_1_r. }
            { intros. exists tid. split. simpl. auto.
              remember ((pmap_union (permMapsCanonical tid) Hacc
                                    (Hl' tid (permMapsUnion_oblig1 Heq)))) as pu eqn:Hpu.
              symmetry in Hpu.
              assert (Hres := pmap_union_result_union Hpu).
              specialize (Hres b ofs).
              rewrite Hpu.
              assert (Hgoal: Some ((PermMap.map (perm_maps tp tid)) !! b ofs Cur) =
                             Some ((PermMap.map pu) !! b ofs Cur)).
              rewrite Hres. simpl. unfold PMap.get at 3. simpl.
              rewrite PTree.gempty. unfold perm_union.
              destruct ((PermMap.map (perm_maps tp tid)) !! b ofs Cur); reflexivity.
              inversion Hgoal. reflexivity. }
            { intros. exists tid. split. simpl. auto.
              remember ((pmap_union (permMapsCanonical tid) Hacc
                                    (Hl' tid (permMapsUnion_oblig1 Heq)))) as pu eqn:Hpu.
              symmetry in Hpu.
              assert (Hres := pmap_union_result_max Hpu).
              specialize (Hres b ofs).
              rewrite Hpu. rewrite Hres. simpl. unfold PMap.get at 3. simpl.
              rewrite PTree.gempty. unfold perm_max.
              destruct ((PermMap.map (perm_maps tp tid)) !! b ofs Max) as [p0|];
                [destruct p0 |]; reflexivity.
            }      
          - assert (Hlhd': tid' :: lhd <> [::]) by (intros; discriminate).
            destruct (Hinv_eq _ Hlhd' Hlst) as [Hnext [Hcur Hmax]];
              clear Hinv_eq. split; [idtac| split].
            { simpl.
              clear Hcur Hmax. destruct Hnext as [tid'' [HIn Hnext_acc]].
              apply List.in_inv in HIn. rewrite Hnext_acc.
              destruct (Pos.max_dec (PermMap.next p) (PermMap.next (getThreadPerm tp tid'')))
                as [Hmax | Hmax].
              + exists tid. split. right.
                apply in_rcons_refl.
                assumption.
              + exists tid''. split.
                destruct HIn as [? | HIn]; auto.
                right.
                  by apply in_rcons_weaken.
                  assumption.
            }
            { clear Hnext Hmax. intros.
              destruct (Hcur ofs b) as [tid'' [HIn Hacc_cur]].
              apply List.in_inv in HIn.
              remember (pmap_union (permMapsCanonical tid) Hacc
                                   (Hl' tid (permMapsUnion_oblig1 Heq))) as pu eqn:Hpu.
              symmetry in Hpu.
              assert (Hres := pmap_union_result_union Hpu).
              specialize (Hres b ofs).
              rewrite Hpu.
              symmetry in Hres.
              apply perm_union_result in Hres. destruct Hres as [Hres | Hres];
                rewrite Hres; eexists; split; eauto.
              apply in_rcons_refl.
              destruct HIn as [? | HIn]; subst.
              simpl; by left.
              simpl. right. by apply in_rcons_weaken.
            }
            { clear Hnext Hcur. intros.
              destruct (Hmax ofs b) as [tid'' [HIn Hacc_max]].
              apply List.in_inv in HIn.
              remember (pmap_union (permMapsCanonical tid) Hacc
                                   (Hl' tid (permMapsUnion_oblig1 Heq))) as pu eqn:Hpu.
              symmetry in Hpu.
              assert (Hres := pmap_union_result_max Hpu).
              specialize (Hres b ofs).
              rewrite Hpu.
              symmetry in Hres.
              apply perm_max_result in Hres. destruct Hres as [Hres | Hres].
              exists tid. split.
              apply in_rcons_refl. auto. 
              exists tid''. split.
              destruct HIn as [? | HIn]; subst.
              simpl; by left.
              simpl. right. by apply in_rcons_weaken.
              rewrite Hacc_max. rewrite Hres. reflexivity.
            }
        }
        { (* emptyPermMap is disjoint from all maps *)
          intros tid Hin. apply empty_disjoint. }
        { (* all maps are canonical *) reflexivity. }
        { unfold subSeq. rewrite subnn. by rewrite drop0. }
        { (* Hnext init*)
          intros. destruct lhd. inversion HIn.
          assert (H: size (tag threadsList) = size ((o :: lhd) ++ tag threadsList)) by
              (rewrite <- Hlst; reflexivity).
          simpl in H. rewrite size_cat in H. exfalso. ssromega. }
        {  (*Hperm_ord init*)
          intros. destruct lhd. inversion HIn.
          assert (H: size (tag threadsList) = size ((o :: lhd) ++ tag threadsList)) by
              (rewrite <- Hlst; reflexivity).
          simpl in H. rewrite size_cat in H. exfalso. ssromega. }
        { (*Hacc init*) reflexivity. }
        { (* Hinv_eq init*)
          intros. destruct lhd. exfalso; auto.
          assert (H: size (tag threadsList) = size ((o :: lhd) ++ tag threadsList)) by
              (rewrite <- Hlst; reflexivity).
          simpl in H. rewrite size_cat in H. exfalso. ssromega. }
       Defined.
   
End PermMapConstruction.
 *)

                    (* Lemma updThread_ext_invariants : *)
    (*   forall (tp tp' : thread_pool) c' tid0 (pf: tid0 < num_threads tp) *)
    (*     pmap counter *)
    (*     (Hinv: invariant tp) *)
    (*     (Hpmap_wf: permMap_wf tp pmap tid0) *)
    (*     (Hpmap_can: isCanonical pmap) *)
    (*     (Hthread: exists t, *)
    (*                 getThreadC tp (Ordinal pf) = Kstage t.1 t.2.1 t.2.2) *)
    (*     (Htp': tp' = updThread tp (Ordinal pf) (Krun c') pmap counter), *)
    (*     invariant tp'. *)
    (* Proof. *)
    (*   intros. destruct Hinv as [Hcanonical Hrace Hlp Hlp_max]; split. *)
    (*   { intros tid'.  unfold isCanonical in *. *)
    (*     destruct tid' as [tid' pf']. *)
    (*     subst tp'. simpl in *. *)
    (*     destruct (tid' == tid0) eqn:Heq; move/eqP:Heq=>Heq; subst. *)
    (*     - rewrite if_true. auto. *)
    (*       pf_cleanup. apply eq_refl. *)
    (*     - rewrite if_false. auto. *)
    (*       apply/eqP. intro Hcontra. inversion Hcontra; by subst. *)
    (*   } *)
    (*   { unfold race_free. intros. *)
    (*     destruct (tid0 == tid1) eqn:Heq0, (tid0 == tid0') eqn:Heq0'; *)
    (*       move/eqP:Heq0=>Heq0; move/eqP:Heq0'=>Heq0'; subst; simpl in *. *)
    (*     - exfalso. auto. *)
    (*     - rewrite if_true. rewrite if_false. *)
    (*       unfold permMap_wf in Hpmap_wf. *)
    (*       apply permMapsDisjoint_comm. *)
    (*       eapply Hpmap_wf; eauto. *)
    (*       apply/eqP. intro Hcontra. inversion Hcontra; by subst. *)
    (*       apply/eqP. rewrite (leq_pf_irr _ _ Htid0 pf). reflexivity. *)
    (*     - rewrite if_false. rewrite if_true. *)
    (*       eapply Hpmap_wf; eauto. rewrite (leq_pf_irr _ _ Htid0' pf). apply eq_refl. *)
    (*       apply/eqP. intro Hcontra. inversion Hcontra; by subst. *)
    (*     - rewrite if_false. rewrite if_false. eapply Hrace; eauto. *)
    (*       apply/eqP. intro Hcontra; inversion Hcontra; by subst. *)
    (*       apply/eqP. intro Hcontra; inversion Hcontra; by subst. *)
    (*   } *)
    (*   { intros. subst tp'; simpl in *. *)
    (*     destruct (Hlp pf0) as [c0 [Hthread0 Hhalted]]. *)
    (*     destruct (tid0 == 0) eqn:Htid0; move/eqP:Htid0=>Htid0. *)
    (*     - subst. pf_cleanup.  *)
    (*       destruct Hthread as [? Hthread]. rewrite Hthread0 in Hthread. *)
    (*       discriminate. *)
    (*       exists c0. rewrite if_false. *)
    (*       split; auto. *)
    (*       apply/eqP. intro Hcontra. inversion Hcontra; auto. *)
    (*   }    *)
    (* Defined. *)

    (* Lemma addThread_ext_invariants : *)
    (*   forall (tp tp' : thread_pool) c' pmap *)
    (*     (Hinv: invariant tp) *)
    (*     (Hpmap_wf: newPermMap_wf tp pmap) *)
    (*     (Hpmap_can: isCanonical pmap) *)
    (*     (Htp': tp' = addThread tp (Krun c') pmap), *)
    (*     invariant tp'. *)
    (* Proof. *)
    (*   intros. destruct Hinv as [Hcanonical Hrace Hlp]; split. *)
    (*   { intros tid. unfold isCanonical in *. *)
    (*     destruct tid as [tid pf]. *)
    (*     subst tp'. simpl in *. *)
    (*     destruct ( unlift (ordinal_pos_incr (num_threads tp)) *)
    (*                       (Ordinal (n:=(num_threads tp).+1) (m:=tid) pf)) eqn:Heqo; rewrite Heqo; auto. *)
    (*   } *)
    (*   { unfold race_free in *. intros. subst. simpl. *)
    (*     unfold newPermMap_wf in Hpmap_wf. *)
    (*     destruct (unlift (ordinal_pos_incr (num_threads tp)) *)
    (*                      (Ordinal (n:=(num_threads tp).+1) (m:=tid0) Htid0)) as [o|] eqn:Heqo. *)
    (*     + rewrite Heqo. *)
    (*       apply unlift_m_inv in Heqo. subst. *)
    (*       destruct (unlift (ordinal_pos_incr (num_threads tp)) *)
    (*                        (Ordinal (n:=(num_threads tp).+1) (m:=tid0') Htid0')) as [o'|] eqn:Heqo'. *)
    (*       * rewrite Heqo'. apply unlift_m_inv in Heqo'. subst. *)
    (*         unfold race_free in Hrace. *)
    (*         destruct o, o'. *)
    (*         eapply Hrace; eauto. *)
    (*       * rewrite Heqo'. unfold newPermMap_wf in Hpmap_wf. *)
    (*         destruct o. *)
    (*         eapply Hpmap_wf; eauto. *)
    (*     + rewrite Heqo. *)
    (*       destruct (unlift (ordinal_pos_incr (num_threads tp)) *)
    (*                        (Ordinal (n:=(num_threads tp).+1) (m:=tid0') Htid0')) as [o'|] eqn:Heqo'. *)
    (*       * rewrite Heqo'. destruct o'. unfold newPermMap_wf in Hpmap_wf. *)
    (*         apply permMapsDisjoint_comm. *)
    (*         eapply Hpmap_wf. *)
    (*       * exfalso. *)
    (*         assert (Hcontra: unlift_spec (ordinal_pos_incr (num_threads tp)) *)
    (*                                      (Ordinal (n:=(num_threads tp).+1) (m:=tid0) Htid0) None) *)
    (*           by (rewrite <- Heqo; apply/unliftP). *)
    (*         inversion Hcontra as [|Hcontra']. *)
    (*         unfold ordinal_pos_incr in Hcontra'. inversion Hcontra'. subst. *)
    (*         assert (Hcontra2: unlift_spec (ordinal_pos_incr (num_threads tp)) *)
    (*                                       (Ordinal (n:=(num_threads tp).+1) (m:=tid0') Htid0') None) *)
    (*           by (rewrite <- Heqo'; apply/unliftP). *)
    (*         inversion Hcontra2 as [|Hcontra2']. *)
    (*         unfold ordinal_pos_incr in *. inversion Hcontra2'. subst. *)
    (*         ssromega. *)
    (*   } *)
    (*   { intros. subst tp'. simpl. *)
    (*     destruct (unlift (ordinal_pos_incr (num_threads tp)) *)
    (*                      (Ordinal (n:=(num_threads tp).+1) (m:=0) pf)) eqn:Hunlift. *)
    (*     - simpl in pf. *)
    (*       assert (pf0: 0 < num_threads tp) by (clear -pf; destruct num_threads; ssromega). *)
    (*       destruct (Hlp pf0) as [c0 [Hget Hhalted]]. destruct o.  *)
    (*       rewrite Hunlift.  *)
    (*       apply unlift_m_inv in Hunlift. simpl in *. subst.  pf_cleanup. exists c0. *)
    (*       auto. *)
    (*     - rewrite Hunlift. simpl in pf. *)
    (*       assert (pf0: 0 < num_threads tp) by (clear -pf; destruct num_threads; ssromega). *)
    (*       exfalso. *)
    (*       assert (Hun:= unliftP (ordinal_pos_incr (num_threads tp)) *)
    (*                             (Ordinal (n:=(num_threads tp).+1) (m:=0) pf)). *)
    (*       rewrite Hunlift in Hun. *)
    (*       inversion Hun. inversion H. ssromega. *)
    (*   } *)
    (* Defined. *)
    
    (* Lemma mklock_inv : *)
    (*   forall tp tp' tp'' m m1 b ofs m1' c' tid0 pmap_tid' pmap_lp *)
    (*     (Htid0_lt_pf : tid0 < num_threads tp) *)
    (*     (pf_lp : 0 < num_threads tp) *)
    (*     (pf_lp' : 0 < num_threads tp') counter, *)
    (*     let: tid := Ordinal Htid0_lt_pf in *)
    (*     let: lp := Ordinal pf_lp in *)
    (*     let: lp' := Ordinal pf_lp' in *)
    (*     let: pmap_tid := getThreadPerm tp tid in *)
    (*     forall *)
    (*       (Hinv: invariant tp) *)
    (*       (Hcompatible: mem_compatible tp m) *)
    (*       (Hrestrict_pmap: restrPermMap (permMapsInv_lt Hcompatible tid) = m1) *)
    (*       (Hstore: Mem.store Mint32 m1 b (Int.intval ofs) (Vint Int.zero) = Some m1') *)
    (*       (Hdrop_perm: *)
    (*          setPerm (Some Nonempty) (getPerm b (Int.intval ofs) Max pmap_tid) *)
    (*                  (store_perm_order b ofs Hinv Hrestrict_pmap Hstore) *)
    (*                  b (Int.intval ofs) pmap_tid = pmap_tid') *)
    (*       (Hlp_perm: setPerm (Some Writable) (Some Freeable) (perm_F_any Writable) *)
    (*                          b (Int.intval ofs) (getThreadPerm tp lp) = pmap_lp) *)
    (*       (Hthread: exists t, *)
    (*                   getThreadC tp tid = Kstage (fst t) (fst (snd t)) (snd (snd t))) *)
    (*       (Htp': tp' = updThread tp tid (Krun c') pmap_tid' counter) *)
    (*       (Htp'': tp'' = updThreadP tp' lp' pmap_lp), *)
    (*       invariant tp''. *)
    (* Proof. *)
    (*   intros. destruct Hinv as [Hcanonical Hrace Hlp]. subst tp'. subst tp''. *)
    (*   simpl in *. pf_cleanup. *)
    (*   assert (Hpmap: PermMap.map (getThreadPerm tp (Ordinal Htid0_lt_pf)) = *)
    (*                  Mem.mem_access m1). *)
    (*   { rewrite <- Hrestrict_pmap. *)
    (*     unfold restrPermMap. reflexivity. } *)
    (*   assert (Hcontra: tid0 <> 0). *)
    (*   { intros Hcontra. subst tid0. *)
    (*     simpl in *. *)
    (*     destruct (Hlp Htid0_lt_pf) as [c0' [Hthread' Hhalted]]. *)
    (*     destruct Hthread as [? Hthread]. *)
    (*     rewrite Hthread in Hthread'. inversion Hthread'. } *)
    (*   clear Hthread. *)
    (*   split. *)
    (*   { simpl. intros [tid tid_pf]. *)
    (*     repeat match goal with *)
    (*              | [|- context[if ?Expr then _ else _]] => destruct Expr eqn:? *)
    (*              | [H: _ == _ = _ |- _] => move/eqP:H=>H *)
    (*              | [H: @Ordinal _ _ _ = @Ordinal _ _ _ |- _] => inversion H; clear H *)
    (*            end; subst; auto; apply setPerm_canonical; auto. *)
    (*   } *)
    (*   { unfold race_free, updThreadP, updThread. simpl. *)
    (*     intros tid1 tid2 Htid1 Htid2 Hneq. *)
    (*     assert (Hracy_tid0: racy (getPerm b (Int.intval ofs) Cur *)
    (*                                       (getThreadPerm tp (Ordinal Htid0_lt_pf)))). *)
    (*     { clear - Hrestrict_pmap Hstore Hpmap. *)
    (*       apply Mem.store_valid_access_3 in Hstore. *)
    (*       apply Mem.valid_access_perm with (k := Cur) in Hstore. *)
    (*       unfold Mem.perm, Mem.perm_order' in *. unfold getPerm, getThreadPerm. *)
    (*       rewrite Hpmap. destruct (Maps.PMap.get b (Mem.mem_access m1) (Int.intval ofs) Cur); *)
    (*         inversion Hstore; subst; auto; constructor. *)
    (*     } *)
    (*     assert (Hnotracy: forall tid, nat_of_ord tid <> tid0 -> *)
    (*                              not_racy (getPerm b (Int.intval ofs) Cur *)
    (*                                                (getThreadPerm tp tid))). *)
    (*     { clear - Hrace Hracy_tid0. *)
    (*       intros tid Hneq. *)
    (*       eapply racy_disjoint; eauto. *)
    (*       unfold getThreadPerm; destruct tid. auto. *)
    (*     }  *)
    (*     assert (Hcur1_notracy: not_racy (Some Nonempty)) by constructor. *)
    (*     unfold getThreadPerm in *. *)
    (*     repeat match goal with *)
    (*              | [|- context[if ?Expr then _ else _]] => destruct Expr eqn:? *)
    (*              | [H: _ == _ = _ |- _] => move/eqP:H=>H *)
    (*              | [H: @Ordinal _ _ _ = @Ordinal _ _ _ |- _] => inversion H; clear H *)
    (*            end; subst; try (by (exfalso; auto)); auto; *)
    (*     try match goal with *)
    (*           | [|- permMapsDisjoint (setPerm (Some Writable) _ _ _ _ _) *)
    (*                                 (setPerm (Some Nonempty) _ _ _ _ _)] => *)
    (*             apply permMapsDisjoint_comm; apply setPerm_noracy1; auto *)
    (*           | [|- permMapsDisjoint (setPerm (Some Nonempty) _ _ _ _ _) *)
    (*                                 (setPerm (Some Writable) _ _ _ _ _)] => *)
    (*             apply setPerm_noracy1; auto *)
    (*           | [|- permMapsDisjoint (setPerm (Some Writable) _ _ _ _ _) (perm_maps _ _)] => *)
    (*             apply setPerm_noracy3; auto *)
    (*           | [|- permMapsDisjoint (perm_maps _ _) (setPerm (Some Writable) _ _ _ _ _)] => *)
    (*             apply permMapsDisjoint_comm; apply setPerm_noracy3; auto *)
    (*           | [|- permMapsDisjoint (setPerm (Some Nonempty) _ _ _ _ _) (perm_maps _ _)] => *)
    (*             apply setPerm_noracy2; auto *)
    (*           | [|- permMapsDisjoint (perm_maps _ _) (setPerm (Some Nonempty) _ _ _ _ _)] => *)
    (*             apply permMapsDisjoint_comm; apply setPerm_noracy2; auto *)
    (*         end; *)
    (*     apply Hnotracy; intros Hcontra';  *)
    (*     subst tid0; simpl in *; pf_cleanup; auto. *)
    (*   } *)
    (*   { simpl. intros. rewrite if_false. auto. *)
    (*     apply/eqP; intros Hcontra'. inversion Hcontra'; auto. *)
    (*   } *)
    (* Qed. *)

    (* Lemma freelock_inv : *)
    (*   forall tp tp' tp'' m m1 c' b ofs pmap_lp', *)
    (*     let: n := counter tp in *)
    (*     forall tid0 *)
    (*       (Htid0_lt_pf : tid0 < num_threads tp) *)
    (*       (pf_lp : 0 < num_threads tp) *)
    (*       (pf_lp' : 0 < num_threads tp'), *)
    (*       let: tid := Ordinal Htid0_lt_pf in *)
    (*       let: lp := Ordinal pf_lp in *)
    (*       let: lp' := Ordinal pf_lp' in *)
    (*       let: pmap_lp := getThreadPerm tp lp in *)
    (*       forall *)
    (*         (Hinv: invariant tp) *)
    (*         (Heq: sval (permMapsUnion (canonical Hinv) (no_race Hinv)) = getMaxPerm m) *)
    (*         (Hcompatible: mem_compatible tp m) *)
    (*         (Hrestrict_pmap: restrPermMap (permMapsInv_lt Hcompatible tid) = m1) *)
    (*         (Hdrop_perm: setPerm None (Some Freeable) I b (Int.intval ofs) pmap_lp = pmap_lp') *)
    (*         (Hangel_wf: permMap_wf tp (aggelos n) tid0) *)
    (*         (Hangel_canonical: isCanonical (aggelos n)) *)
    (*         (Hthread: exists t, *)
    (*                     getThreadC tp tid = Kstage (fst t) (fst (snd t)) (snd (snd t))) *)
    (*         (Htp': tp' = updThread tp tid (Krun c') (aggelos n) (n+1))             *)
    (*         (Htp'': tp'' = updThreadP tp' lp' pmap_lp'), *)
    (*         invariant tp''. *)
    (* Proof. *)
    (*   intros. destruct Hinv as [Hcanonical Hrace Hlp]. subst tp'. subst tp''. *)
    (*   simpl in *. pf_cleanup. *)
    (*   assert (Hpmap: PermMap.map (getThreadPerm tp (Ordinal Htid0_lt_pf)) = *)
    (*                  Mem.mem_access m1). *)
    (*   { rewrite <- Hrestrict_pmap. *)
    (*     unfold restrPermMap. reflexivity. } *)
    (*   assert (Hcontra: tid0 <> 0). *)
    (*   { intros Hcontra. subst tid0. *)
    (*     simpl in *. *)
    (*     destruct (Hlp Htid0_lt_pf) as [c0' [Hthread' Hhalted]]. *)
    (*     destruct Hthread as [? Hthread]. *)
    (*     rewrite Hthread in Hthread'. inversion Hthread'. } *)
    (*   split; simpl. *)
    (*   { intros. *)
    (*     destruct (tid == Ordinal (n:=num_threads tp) (m:=0) pf_lp); auto. *)
    (*     rewrite <- Hdrop_perm. *)
    (*     apply setPerm_canonical. auto. *)
    (*     destruct (tid == Ordinal (n:=num_threads tp) (m:=tid0) Htid0_lt_pf); auto. *)
    (*   } *)
    (*   { unfold race_free. simpl. intros tid1 tid2 Htid1 Htid2 Hneq. *)
    (*     unfold getThreadPerm in *. *)
    (*     unfold permMap_wf in Hangel_wf. *)
    (*     assert (Hnotracy: not_racy None) by constructor. *)
    (*     repeat match goal with *)
    (*              | [|- context[if ?Expr then _ else _]] => destruct Expr eqn:? *)
    (*              | [H: _ == _ = _ |- _] => move/eqP:H=>H *)
    (*              | [H: @Ordinal _ _ _ = @Ordinal _ _ _ |- _] => inversion H; clear H *)
    (*            end; subst; try (by (exfalso; auto)); auto; *)
    (*     try (apply setPerm_noracy2; auto); *)
    (*     try (apply permMapsDisjoint_comm; apply setPerm_noracy2; auto). *)
    (*     apply permMapsDisjoint_comm. auto. *)
    (*   } *)
    (*   { simpl. intros. rewrite if_false. auto. *)
    (*     apply/eqP; intros Hcontra'. inversion Hcontra'; auto. *)
    (*   } *)
    (* Defined. *)