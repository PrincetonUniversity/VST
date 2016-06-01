Require Import compcert.lib.Axioms.

Require Import concurrency.sepcomp. Import SepComp.
Require Import sepcomp.semantics_lemmas.

Require Import concurrency.pos.

From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
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

Require Import concurrency.threads_lemmas.
Require Import concurrency.permissions.
Require Import concurrency.concurrent_machine concurrency.dry_context.

Import DryMachine ThreadPool.

Global Notation "a # b" := (Maps.PMap.get b a) (at level 1).
Global Ltac pf_cleanup :=
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
                H2: containsThread (@updThreadC _ ?TP _ _) ?M |- _] =>
           apply cntUpdateC' in H2;
             assert (H1 = H2) by (by eapply cnt_irr); subst H2
         | [H1: containsThread ?TP ?M,
                H2: containsThread (@updThread _ ?TP _ _ _) ?M |- _] =>
           apply cntUpdate' in H2;
             assert (H1 = H2) by (by eapply cnt_irr); subst H2
         end.

(*TODO: Check if this module is still relevant*)
Module ThreadPoolWF.
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
      forall tp vf arg p (Hwf: newPermMap_wf tp p) (Hrace: race_free tp),
        race_free (addThread tp vf arg p).
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
    
    Lemma lockSetGuts_1:
      forall tp b ofs rmap,
        lockRes tp (b,ofs) = Some rmap ->
        Maps.PMap.get b (lockSet tp) ofs = Some Writable.
    Proof.
    Admitted.

    Lemma lockSetGuts_2:
      forall tp b ofs,
        Maps.PMap.get b (lockSet tp) ofs = Some Writable ->
        exists rmap,
          lockRes tp (b,ofs) = Some rmap.
    Proof.
    Admitted.
    
    Lemma lock_valid_block:
      forall (tpc : thread_pool) (mc : mem) (bl1 : block) 
        (ofs : Z) rmap1
        (HmemCompC: mem_compatible tpc mc)
        (Hl1: lockRes tpc (bl1, ofs) = Some rmap1),
        Mem.valid_block mc bl1.
    Proof.
      intros.
      assert (HlockSet := lockSetGuts_1 _ _ _ Hl1).
      destruct (valid_block_dec mc bl1) as [? | Hinvalid]; auto.
      exfalso.
      apply (Mem.nextblock_noaccess) with (k:= Max) (ofs := ofs) in Hinvalid.
      assert (H:= compat_ls HmemCompC).
      unfold permMapLt in H.
      specialize (H bl1 ofs).
      rewrite getMaxPerm_correct in H.
      unfold permission_at in H.
      rewrite Hinvalid in H.
      rewrite HlockSet in H;
        by simpl in H.
    Qed.

    
End ThreadPoolWF.


(** ** Lemmas about threadwise semantics*)
Module CoreLanguage.
  
  Import SEM.
  Section CoreLanguage.
  (** Assumptions on thread's corestep (e.g PPC semantics) *)
    Class corestepSpec :=
      { corestep_det: corestep_fun Sem;
        corestep_unchanged_on:
          forall the_ge c m c' m' b ofs
            (Hstep: corestep Sem the_ge c m c' m')
            (Hstable: ~ Mem.perm m b ofs Cur Writable),
            Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m)) =
            Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m'));
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
      forall (tp : thread_pool) (m m' : mem) (i : tid)
        (pf : containsThread tp i) (c c': C)
        (Hinv: invariant tp)
        (Hcode: getThreadC pf = Krun c)
        (Hcompatible : mem_compatible tp m)
        (Hcorestep: corestep SEM.Sem the_ge c (restrPermMap (Hcompatible i pf)) c' m'),
        mem_compatible (updThread pf (Krun c') (getCurPerm m')) m'.
    Proof.
      intros.
      constructor. 
      { intros tid cnt b ofs.
        destruct (tid == i) eqn:Htid;
          move/eqP:Htid=>Htid;
          first by (subst; erewrite gssThreadRes; eapply getCur_Max).
        assert (cnt0 : containsThread tp tid)
          by (eapply cntUpdate' in cnt; auto).
        assert (Hlt := Hcompatible tid cnt0 b ofs).
        assert (HdecayCur := corestep_decay _ _ _ _ Hcorestep).
        apply decay_decay' in HdecayCur.
        destruct (valid_block_dec (restrPermMap (Hcompatible i pf)) b)
          as [Hvalid|Hinvalid].
        - destruct (HdecayCur b ofs) as [ _ Hdecay].
          destruct (Hdecay Hvalid) as [Hfreed | Heq]; clear Hdecay.
          + destruct Hfreed as [HFree Hdrop].
            assert (Hempty: (getThreadR cnt) # b ofs = None).
            { assert (Hp := restrPermMap_Cur (Hcompatible i pf) b ofs).
              unfold permission_at in Hp. rewrite Hp in HFree.
              assert (Hno_race := no_race Hinv).
              unfold race_free in Hno_race.
              specialize (Hno_race _ _ cnt0 pf Htid).
              unfold permMapsDisjoint in Hno_race.
              specialize (Hno_race b ofs).
              assert (Hnot_racy : not_racy ((getThreadR cnt0) # b ofs)).
              rewrite perm_union_comm in Hno_race.
              eapply no_race_racy with (p1 := (getThreadR pf) # b ofs); eauto.
              rewrite HFree. constructor.
              rewrite gsoThreadRes; auto.
                by inversion Hnot_racy.
            }
            rewrite Hempty.
            destruct ((getMaxPerm m') # b ofs); simpl; auto.
          + rewrite getMaxPerm_correct. unfold permission_at.
            admit.
        - apply Mem.nextblock_noaccess with (ofs := ofs) (k := Max) in Hinvalid.
          assert (Hp := restrPermMap_Max (Hcompatible i pf) b ofs).
          unfold permission_at in Hp. rewrite Hp in Hinvalid.
          rewrite Hinvalid in Hlt.
          simpl in Hlt.
          rewrite gsoThreadRes; auto.
          destruct ((getThreadR cnt0) # b ofs);
            [by exfalso| destruct ((getMaxPerm m') # b ofs); simpl; by auto].
      }
      { intros l pmap Hres b ofs.
        rewrite gsoThreadLPool in Hres.
        assert (Hlt := compat_lp Hcompatible _ Hres b ofs).
        admit.
      }
      { rewrite gsoThreadLock. intros b ofs.
        assert (Hlt := compat_ls Hcompatible b ofs).
        admit. (* TODO: need lennart's new lemma about max perm*)
      }
    Admitted.

    Lemma decay_disjoint:
      forall m m' p
        (Hdecay: decay m m')
        (Hlt: permMapLt p (getMaxPerm m))
        (Hdisjoint: permMapsDisjoint (getCurPerm m) p),
        permMapsDisjoint (getCurPerm m') p.
    Proof.
      intros.
      unfold permMapsDisjoint in *.
      intros.
      apply decay_decay' in Hdecay.
      unfold decay' in Hdecay.
      destruct (Hdecay b ofs) as [_ Hold].
      clear Hdecay.
      specialize (Hdisjoint b ofs).
      destruct (valid_block_dec m b) as [Hvalid | Hinvalid].
      - destruct (Hold Hvalid) as [Hfree | Heq].
        + destruct Hfree as [_ Hm']. rewrite getCurPerm_correct.
          assert (not_racy (permission_at m' b ofs Cur))
            by (unfold permission_at; rewrite Hm'; constructor).
          by eapply not_racy_union.
        + rewrite getCurPerm_correct. unfold permission_at.
          rewrite <- Heq. rewrite getCurPerm_correct in Hdisjoint.
          unfold permission_at in Hdisjoint. assumption.
      - assert (Hnone: (p # b ofs) = None).
        { apply Mem.nextblock_noaccess with (ofs := ofs) (k := Max) in Hinvalid.
          unfold permMapLt in Hlt.
          specialize (Hlt b ofs).
          rewrite getMaxPerm_correct in Hlt.
          unfold permission_at in Hlt.
          rewrite Hinvalid in Hlt. simpl in Hlt.
          destruct (p # b ofs); tauto.
        }
        rewrite Hnone.
        rewrite perm_union_comm.
        eapply not_racy_union;
          by constructor.
    Qed.

    Opaque getThreadR.
    Lemma corestep_invariant:
      forall (tp : thread_pool) (m : mem) (i : nat)
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
      apply corestep_decay in Hcorestep.
      constructor.
      { (* non-interference in threads *)
        unfold race_free in *.
        intros j k.
        destruct (i == j) eqn:Heqj, (i == k) eqn:Heqk; move/eqP:Heqj=>Heqj;
          move/eqP:Heqk=>Heqk; simpl in *; intros cntj' cntk' Hneq;
                        assert (cntk: containsThread tp k)
                          by (eapply cntUpdate'; eauto);
                        assert (cntj: containsThread tp j)
                          by (eapply cntUpdate'; eauto).
        - subst j k; exfalso; auto.
        - subst j.
          erewrite gssThreadRes.
          erewrite @gsoThreadRes with (cntj := cntk); eauto.
          specialize (Hrace _ _ pf cntk Hneq).
          assert (Hlt := compat_th Hcompatible cntk).
          subst m1.
          eapply decay_disjoint; eauto.
          unfold permMapLt in *.
          intros b ofs.
          rewrite getMaxPerm_correct;
            by rewrite restrPermMap_Max.
          intros b ofs.
          rewrite getCurPerm_correct;
            by rewrite restrPermMap_Cur.
        - subst k.
          erewrite @gsoThreadRes with (cntj := cntj); auto.
          erewrite gssThreadRes.
          specialize (Hrace _ _ pf cntj Heqj).
          assert (Hlt := compat_th Hcompatible cntj).
          subst m1.
          eapply permMapsDisjoint_comm.
          eapply decay_disjoint; eauto.
          unfold permMapLt in *.
          intros b ofs.
          rewrite getMaxPerm_correct;
            by rewrite restrPermMap_Max.
          intros b ofs.
          rewrite getCurPerm_correct;
            by rewrite restrPermMap_Cur.
        - erewrite @gsoThreadRes with (cntj := cntj); auto.
          erewrite @gsoThreadRes with (cntj := cntk); auto.
      }
      { (* non-interference with lockpool*)
        intros j cntj.
        rewrite gsoThreadLock.
        destruct (i == j) eqn:Hij; move/eqP:Hij=>Hik; subst.
        - erewrite gssThreadRes. apply permMapsDisjoint_comm.
          assert (Hlt := compat_ls Hcompatible).
          eapply decay_disjoint; eauto.
          intros b ofs.
          rewrite getMaxPerm_correct;
            by rewrite restrPermMap_Max.
          intros b ofs. rewrite perm_union_comm.
          rewrite getCurPerm_correct.
          rewrite restrPermMap_Cur.
            by eapply Hlp.
        - erewrite @gsoThreadRes with (cntj := cntUpdate' _ _ _ cntj);
            by eauto.
      }
      { intros l pmap j cntj Hres.
        rewrite gsoThreadLPool in Hres.
        destruct (i == j) eqn:Hij; move/eqP:Hij=>Hik; subst.
        - erewrite gssThreadRes. apply permMapsDisjoint_comm.
          assert (Hlt := compat_lp Hcompatible _ Hres).
          eapply decay_disjoint; eauto.
          intros b ofs.
          rewrite getMaxPerm_correct;
            by rewrite restrPermMap_Max.
          intros b ofs. rewrite perm_union_comm.
          rewrite getCurPerm_correct.
          rewrite restrPermMap_Cur;
            by (eapply lock_res_threads0; eauto).
        - erewrite @gsoThreadRes with (cntj := cntUpdate' _ _ _ cntj);
            by eauto.
      }
      { intros l pmap Hres.
        rewrite gsoThreadLock.
        rewrite gsoThreadLPool in Hres;
          by eauto.
      }
    Admitted.

    Lemma corestep_disjoint_val:
      forall (tp : thread_pool) (m m' : mem) (i j : tid) (Hneq: i <> j)
        (c c' : C) 
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
        unfold Mem.perm_order' in *.
        clear - Hcontra Hreadable Hdisjoint.
        specialize (Hdisjoint b ofs). destruct Hdisjoint as [pu Hunion].
        destruct ((getThreadR pfi) # b ofs);
          try (exfalso; assumption);
          inversion Hcontra; subst; simpl in Hunion;
          destruct ((getThreadR pfj) # b ofs);
          try match goal with
              | [H: Some _ = Some _ |- _] => inversion H; subst
              | [H: match ?Expr with _ => _ end = _ |- _] => destruct Expr
              end; try discriminate; inversion Hreadable.
      }
      apply corestep_unchanged_on with (b := b) (ofs := ofs) in Hcorestep; auto.
    Qed.

    Lemma corestep_disjoint_val_lockset:
      forall (tp : thread_pool) (m m' : mem) (i : tid)
        (c c' : C) 
        (pfi : containsThread tp i)
        (Hcomp : mem_compatible tp m) (b : block) (ofs : Z) 
        (Hreadable: Mem.perm (restrPermMap (compat_ls Hcomp)) b ofs Cur Readable)
        (Hcorestep: corestep Sem the_ge c (restrPermMap (Hcomp i pfi)) c' m')
        (Hinv: invariant tp),
        Maps.ZMap.get ofs (Mem.mem_contents m) # b =
        Maps.ZMap.get ofs (Mem.mem_contents m') # b.
    Proof.
      intros.
      assert (Hstable: ~ Mem.perm (restrPermMap (Hcomp _ pfi))
                         b ofs Cur Writable).
      { intros Hcontra.
        assert (Hdisjoint := lock_set_threads Hinv pfi).
        assert (Hpermi := restrPermMap_correct (Hcomp _ pfi) b ofs).
        destruct Hpermi as [_ Hpermi].
        assert (Hpermls := restrPermMap_correct ((compat_ls Hcomp)) b ofs).
        destruct Hpermls as [_ Hpermls].
        unfold permission_at, Mem.perm in *.
        rewrite Hpermi in Hcontra.
        rewrite Hpermls in Hreadable.
        unfold Mem.perm_order' in *.
        clear - Hcontra Hreadable Hdisjoint.
        specialize (Hdisjoint b ofs). destruct Hdisjoint as [pu Hunion].
        destruct ((getThreadR pfi) # b ofs);
          try (exfalso; assumption);
          inversion Hcontra; subst; simpl in *;
          destruct ((lockSet tp) # b ofs); simpl in *;
          try match goal with
              | [H: Some _ = Some _ |- _] => inversion H; subst
              | [H: match ?Expr with _ => _ end = _ |- _] => destruct Expr
              end; try discriminate; inversion Hreadable.
      }
      apply corestep_unchanged_on with (b := b) (ofs := ofs) in Hcorestep; auto.
    Qed.

    Lemma corestep_disjoint_val_lockpool :
      forall (tp : thread_pool) (m m' : mem) (i : tid) (c c' : code)
        (pfi : containsThread tp i) (Hcomp : mem_compatible tp m) addr pmap
        (Hlock: lockRes tp addr = Some pmap)
        (b : block) (ofs : Z)
        (Hreadable: Mem.perm (restrPermMap (compat_lp Hcomp addr Hlock))
                             b ofs Cur Readable)
        (Hcorestep: corestep Sem the_ge c (restrPermMap (Hcomp i pfi)) c' m')
        (Hinv: invariant tp),
        Maps.ZMap.get ofs (Mem.mem_contents m) # b =
        Maps.ZMap.get ofs (Mem.mem_contents m') # b.
    Proof.
      intros.
      assert (Hstable: ~ Mem.perm (restrPermMap (Hcomp _ pfi))
                         b ofs Cur Writable).
      { intros Hcontra.
        assert (Hdisjoint := lock_res_threads Hinv _ pfi Hlock).
        assert (Hpermi := restrPermMap_Cur (Hcomp _ pfi) b ofs).
        assert (Hpermls := restrPermMap_Cur ((compat_lp Hcomp _ Hlock)) b ofs).
        unfold permission_at, Mem.perm in *.
        rewrite Hpermi in Hcontra.
        rewrite Hpermls in Hreadable.
        unfold Mem.perm_order' in *.
        clear - Hcontra Hreadable Hdisjoint.
        specialize (Hdisjoint b ofs). destruct Hdisjoint as [pu Hunion].
        destruct ((getThreadR pfi) # b ofs);
          try (exfalso; assumption);
          inversion Hcontra; subst; simpl in *;
          destruct (pmap # b ofs); simpl in *;
          try match goal with
              | [H: Some _ = Some _ |- _] => inversion H; subst
              | [H: match ?Expr with _ => _ end = _ |- _] => destruct Expr
              end; try discriminate; inversion Hreadable.
      }
      apply corestep_unchanged_on with (b := b) (ofs := ofs) in Hcorestep; auto.
    Qed.
    
  End CoreLanguage.
End CoreLanguage.

Module StepLemmas.

  Lemma updThreadC_compatible:
    forall (tp : thread_pool) m (i : tid) (c : ctl)
      (ctn : containsThread tp i)
      (Hcomp: mem_compatible tp m),
      mem_compatible (updThreadC ctn c) m.
  Proof.
    intros.
    constructor.
    intros j cntj'.
    assert (cntj := cntUpdateC' c ctn cntj').
    specialize (Hcomp _ cntj).
    erewrite @gThreadCR with (cntj := cntj);
      by auto.
    intros.
    erewrite gsoThreadCLPool in H.
    destruct Hcomp;
      by eauto.
    erewrite @gsoThreadCLock;
      by destruct Hcomp.
  Qed.

  Lemma updThreadC_invariant:
    forall (tp : thread_pool) (i : tid) (c : ctl)
      (ctn : containsThread tp i)
      (Hinv : invariant tp),
      invariant (updThreadC ctn c).
  Proof.
    intros. 
    inversion Hinv;
      constructor; unfold race_free in *;
      simpl;
        by auto.
  Qed.

  (** Lemmas about suspend steps*)
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
        (cntj' : containsThread (updThreadC cnti (Kblocked c)) j),
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
    
    Lemma suspendC_invariant:
      forall tp tp' i
        (pff: containsThread tp i)
        (Hinv: invariant tp)
        (Hsuspend: myCoarseSemantics.suspend_thread pff tp'),
        invariant tp'.
    Proof.
      intros.
      inversion Hsuspend; subst.
        by apply updThreadC_invariant.
    Qed.
      
    Lemma suspendF_invariant:
      forall tp tp' i
        (pff: containsThread tp i)
        (Hinv: invariant tp)
        (Hsuspend: myFineSemantics.suspend_thread pff tp'),
        invariant tp'.
    Proof.
      intros.
      inversion Hsuspend; subst.
        by apply updThreadC_invariant.
    Qed.

    Lemma suspendF_lockSet:
      forall tp tp' i
        (pff: containsThread tp i)
        (Hsuspend: myFineSemantics.suspend_thread pff tp'),
        lockSet tp = lockSet tp'.
    Proof.
      intros.
      inversion Hsuspend; subst.
        by erewrite gsoThreadCLock.
    Qed.

    Lemma suspendC_lockSet:
      forall tp tp' i
        (pff: containsThread tp i)
        (Hsuspend: myCoarseSemantics.suspend_thread pff tp'),
        lockSet tp = lockSet tp'.
    Proof.
      intros.
      inversion Hsuspend; subst.
        by erewrite gsoThreadCLock.
    Qed.

    Lemma suspendC_lockPool :
      forall (tp tp' : thread_pool) (i : tid) (pfc : containsThread tp i)
        (Hsuspend: myCoarseSemantics.suspend_thread pfc tp') addr,
        lockRes tp addr = lockRes tp' addr.
    Proof.
      intros. inversion Hsuspend; subst.
        by erewrite gsoThreadCLPool.
    Qed.
    
    Lemma suspendF_lockPool :
      forall (tp tp' : thread_pool) (i : tid) (pff : containsThread tp i)
        (Hsuspend: myFineSemantics.suspend_thread pff tp') addr,
        lockRes tp addr = lockRes tp' addr.
    Proof.
      intros. inversion Hsuspend; subst.
        by erewrite gsoThreadCLPool.
    Qed.
    
    
End StepLemmas.
