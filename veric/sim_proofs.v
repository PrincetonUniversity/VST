Require Import veric.base.
Require Import veric.sim.
Require Import compcert.Events.
(*Require Import compcert.Mem_inject.*)

Module Sim_proof <: SIMULATIONS.

Lemma mem_forward_refl : forall m,
  mem_forward m m.
Proof.
  repeat intro; auto.
Qed.

Lemma mem_forward_trans : forall m1 m2 m3,
  mem_forward m1 m2 ->
  mem_forward m2 m3 ->
  mem_forward m1 m3.
Proof.
  repeat intro; auto.
  apply H in H1. destruct H1.
  apply H0 in H1. destruct H1.
  split; auto.
Qed.

Lemma free_mem_forward :  forall m1 b lo hi m2,
  Mem.free m1 b lo hi = Some m2 ->
  mem_forward m1 m2.
Proof.
  repeat intro.
  split.
  eapply Mem.valid_block_free_1; eauto.
  intros. 
  apply (Mem.perm_free_3 _ _ _ _ _ H _ _ _ _ H1).
Qed.

Lemma store_mem_forward : forall chunk m1 b ofs v m2,
  Mem.store chunk m1 b ofs v = Some m2 ->
  mem_forward m1 m2.
Proof.
  repeat intro. split.
  eapply Mem.store_valid_block_1; eauto.
  intros.
  eapply Mem.perm_store_2. apply H. apply H1.
Qed.

Lemma alloc_mem_forward : forall m1 b lo hi m2,
  Mem.alloc m1 lo hi = (m2,b) ->
  mem_forward m1 m2.
Proof.
  repeat intro. split.
  eapply Mem.valid_block_alloc; eauto.
  intros.
  eapply Mem.perm_alloc_4. apply H. apply H1.
  intros ZZ; subst.
  apply (Mem.fresh_block_alloc _ _ _ _ _  H H0).
Qed.

Lemma allowed_core_modification_refl : forall m,
  allowed_core_modification m m.
Proof.
  clear. intros.
  hnf. split; auto.
  apply mem_forward_refl.
Qed.

Lemma allowed_core_modification_trans : forall m1 m2 m3,
  allowed_core_modification m1 m2 ->
  allowed_core_modification m2 m3 ->
  allowed_core_modification m1 m3.
Proof.
  intros. destruct H. destruct H0.
  split.
  eapply mem_forward_trans; eauto.
  destruct H1; destruct H2.
  split; intros.
  specialize (H1 b ofs p H5).
  destruct H1.
  specialize (H2 b ofs p H1).
  destruct H2; auto.
  right. destruct H2; split; auto.
  destruct H3. apply H3; auto.
  apply Mem.perm_valid_block in H5. auto.
  destruct H1.
  right. split; auto.
  repeat intro.
  eapply H6.
  destruct H4. eapply H4; eauto.
  apply Mem.perm_valid_block in H5. 
  apply H in H5. destruct H5; auto.
  
  split; intros.
  destruct H3. destruct H4.
  apply H3; auto.
  apply H4; auto.
  apply H in H5. destruct H5; auto.
  destruct H3; destruct H4.
  generalize H5; intros.
  apply H6 in H5. destruct H5.
  generalize H5; intros.
  apply H7 in H5. destruct H5. auto.
  destruct H5 as [ofs [? ?]].
  right. exists ofs. split; auto.
  apply H3; auto.

  apply Mem.loadbytes_range_perm in H8.
   unfold Mem.range_perm in H8.
   eapply Mem.perm_valid_block. apply H8. apply H5.

  right. apply H5. 
Qed.

Require Import Zwf.

(*
Lemma getN_clearN : forall n ofs' m1 b lo hi,
  ofs' + n <= lo \/ hi <= ofs' ->
  Mem.getN (nat_of_Z n) ofs' (Mem.clearN (Mem.mem_contents m1) b lo hi b) =
  Mem.getN (nat_of_Z n) ofs' (Mem.mem_contents m1 b).
Proof.
  intro n.
  induction n using (well_founded_induction (Zwf_well_founded 0)).
  intros.
  assert (n <= 0 \/ n > 0) by omega.
  destruct H1.
  replace (nat_of_Z n) with O. simpl. auto.
  symmetry. apply nat_of_Z_neg. auto.
  replace n with (1 + (n - 1)) by omega.
  rewrite nat_of_Z_plus. 2: omega. 2: omega.
  simpl. f_equal.
  unfold Mem.clearN.
  destruct (zeq b b).
  destruct (zle lo ofs').
  destruct (zlt ofs' hi).
  elimtype False. omega.
  simpl; auto. simpl; auto.
  elim n0; auto.
  apply H.
  red. omega.
  omega.
Qed.
*)

Lemma free_allowed_core_mod : forall m1 b lo hi m2,
  Mem.free m1 b lo hi = Some m2 ->
  allowed_core_modification m1 m2.
Proof.
  intros. split.
  eapply free_mem_forward; eauto.
  split; intros.
  unfold block in *.
  assert 
    ((b0 <> b \/ ofs < lo \/ hi <= ofs) \/
     (b = b0 /\ lo <= ofs /\ ofs < hi)) by omega.
  destruct H1.
  left. eapply Mem.perm_free_1; eauto.
  destruct H1; subst.
  right. split.
  apply Mem.free_range_perm in H.
  apply H. auto.
  intro. eapply Mem.perm_free_2; eauto.

  split; intros.
  eapply Mem.perm_free_3; eauto.
(*  unfold block in *.
  assert 
    ((b0 <> b \/ ofs' < lo \/ hi <= ofs') \/
     (b = b0 /\ lo <= ofs' /\ ofs' < hi)) by omega.
  destruct H1.
(*  Focus 2. destruct H1; subst. right. exists ofs'.  *)

  apply Mem.loadbytes_range_perm in H0. unfold Mem.range_perm in H0.
  specialize H0 with ofs'.
  left. assert (ZZ:= Mem.perm_free_1 _ _ _ _ _ H _ _ Cur Readable H1).
        assert (ZZZ: Mem.perm m2 b0 ofs' Cur Readable).
          apply ZZ. apply H0. split. omega. omega. eomga.
         Mem.range_perm_loadbytes destru
 impl in H0.
  apply Mem.free_result in H. subst.
    apply Mem.loadbytes_range_perm in H0.
    left. unfold Mem.perm. unfold Mem.unchecked_free; simpl.
    apply Mem.loadbytes_range_perm in H0.
    unfold Mem.loadbytes in H0. inversion H0. Mem.loadbytes
              unfold Mem.loadbytes.
 simpl.
  assert (Z:= Mem.free_result _ _ _ _ _ H). clear H. subst.
  rewrite Mem.free_result; auto.
  destruct (Mem.valid_access_dec m2 chunk b ofs' Readable).
  rewrite pred_dec_true. 
  rewrite free_result; auto.
  eapply valid_access_free_inv_1; eauto. 
  rewrite pred_dec_false; auto.
  red; intro; elim n. eapply valid_access_free_1; eauto. 


  left. assert (ZZ:= Mem.load_free _ _ _ _ _ H). _ _ _ _ _ H1). eapply Mem.perm_free_1; eauto.
  destruct H1; subst.
  right. split.
  apply Mem.free_range_perm in H.
  apply H. auto.
  intro. eapply Mem.perm_free_2; eauto.

  assert (ZZ:= Mem.perm_free_1 _ _ _ _ _ H).*)
  admit. (*whatever*)
Qed.

Lemma alloc_allowed_core_mod : forall m1 lo hi m2 b,
  Mem.alloc m1 lo hi = (m2,b) ->
  allowed_core_modification m1 m2.
Proof.
  intros. split.
  eapply alloc_mem_forward; eauto.

  split; intros.
  left. eapply Mem.perm_alloc_1; eauto.
  split; intros.
  eapply Mem.perm_alloc_inv in H1; eauto.
  destruct (zeq b0 b); subst; auto.
  elimtype False. revert H0.
  eapply Mem.fresh_block_alloc; eauto.

  assert (forall ofs : Z,
     ofs' <= ofs < ofs' + n -> Mem.perm m1 b0 ofs Cur Readable).
    intros. apply (Mem.loadbytes_range_perm _ _ _ _ _ H0 _ H1).
  assert (forall ofs : Z,
     ofs' <= ofs < ofs' + n -> Mem.perm m2 b0 ofs Cur Readable).
    intros. specialize H1 with ofs. 
            apply (Mem.perm_alloc_1 _ _ _ _ _ H).
            apply H1.  apply H2.
(*  destruct (Mem.valid_access_dec m2 chunk b0 ofs' Readable).
  assert (X:= Mem.load_valid_access). 
   remember (Mem.range_perm_dec m1 b0 ofs' (ofs' + n) Cur Readable) as X1.
     destruct X1. 
           unfold Mem.range_perm_loadbytes in H0. simpl in H0.
   remember (range_perm_dec m2 b0 ofs' (ofs' + n) Cur Readable) as X.
   unfold Mem.range_perm_loadbytes.
   Mem.range_perm_loadbytes _ _ _ _ 
 H2). apply (Mem.loadbytes_range_perm _ _ _ _ _ H0 _ H1).
  left. 
    assert (AL:= Mem.perm_alloc_1 _ _ _ _ _ H).
    assert (MP:= Mem.loadbytes_range_perm _ _ _ _ _ H0). unfold Mem.range_perm in *.
    apply MP. apply H1.
 unfold Mem.range_perm.

  left.Mem.loadbytes_range_perm*)
  admit. (*whatever*)
Qed.


Lemma store_allowed_core_mod : forall m1 chunk v b ofs m2,
  Mem.store chunk m1 b ofs v = Some m2 ->
  allowed_core_modification m1 m2.
Proof.
  intros. split.
  eapply store_mem_forward; eauto.

  split; intros.
  left. eapply Mem.perm_store_1; eauto.
  split; intros.
  eapply Mem.perm_store_2; eauto.
  rename b0 into b'.
  unfold block in *.
  assert
    ((b' <> b \/ n <= 0 \/ ofs' + n <= ofs \/ ofs + size_chunk chunk <= ofs') \/
     (b' = b /\ 0 < n /\ ofs < ofs' + n /\ ofs' < ofs + size_chunk chunk)) by omega.
  destruct H1.
  left. erewrite Mem.loadbytes_store_other; eauto.
  destruct H1; subst.
  right.
  apply Mem.store_valid_access_3 in H.
  assert (ofs' <= ofs \/ ofs < ofs') by omega.
  destruct H1.
  exists ofs. split. omega.
  apply H. destruct chunk; simpl; omega.
  assert (ofs + size_chunk chunk < ofs' +  n \/ ofs' + n  <= ofs + size_chunk chunk) by omega.
  destruct H3.
  exists (ofs + size_chunk chunk - 1).
  split. omega.
  apply H.
  destruct chunk; simpl in *; omega.
  exists ofs'. split. omega.
  apply H.
  omega.
Qed.

Module Sim_eq.
Section Forward_simulation_equals. 
  Context {G1 C1 G2 C2:Type}
          {Sem1 : CompcertCoreSem G1 C1}
          {Sem2 : CompcertCoreSem G2 C2}

          {ge1:G1}
          {ge2:G2}
          {entry_points : list (val * val * signature)}.

  Record Forward_simulation_equals :=
  { core_data:Type;

    match_core : core_data -> C1 -> C2 -> Prop;
    core_ord : core_data -> core_data -> Prop;
    core_ord_wf : well_founded core_ord;

    core_diagram : 
      forall st1 m st1' m', corestep Sem1 ge1 st1 m st1' m' ->
      forall d st2, match_core d st1 st2 ->
        exists st2', exists d',
          match_core d' st1' st2' /\
          ((corestep_plus Sem2 ge2 st2 m st2' m') \/
            corestep_star Sem2 ge2 st2 m st2' m' /\
            core_ord d' d);

    core_initial : forall v1 v2 sig,
      In (v1,v2,sig) entry_points ->
        forall vals,
          Forall2 (Val.has_type) vals (sig_args sig) ->
          exists cd, exists c1, exists c2,
            make_initial_core Sem1 ge1 v1 vals = Some c1 /\
            make_initial_core Sem2 ge2 v2 vals = Some c2 /\
            match_core cd c1 c2;

    core_halted : forall cd c1 c2 (v:int),
      match_core cd c1 c2 ->
      safely_halted Sem1 ge1 c1 = Some v ->
      safely_halted Sem2 ge2 c2 = Some v;

    core_at_external : 
      forall d st1 st2 e args,
        match_core d st1 st2 ->
        at_external Sem1 st1 = Some (e,args) ->
        ( at_external Sem2 st2 = Some (e,args) /\
          Forall2 Val.has_type args (sig_args (ef_sig e)) );

    core_after_external :
      forall d st1 st2 ret e args,
        match_core d st1 st2 ->
        at_external Sem1 st1 = Some (e,args) ->
        at_external Sem2 st2 = Some (e,args) ->
        Forall2 Val.has_type args (sig_args (ef_sig e)) ->
        Val.has_type ret (proj_sig_res (ef_sig e)) ->
        exists st1', exists st2', exists d',
          after_external Sem1 ret st1 = Some st1' /\
          after_external Sem2 ret st2 = Some st2' /\
          match_core d' st1' st2'
  }.
End Forward_simulation_equals. 

Implicit Arguments Forward_simulation_equals [[G1] [C1] [G2] [C2]].
End Sim_eq.

Definition siminj (j: meminj) (m1 m2 : mem) :=
  (forall b, ~(Mem.valid_block m1 b) -> j b = None) /\
  (forall b b' delta, j b = Some(b', delta) -> Mem.valid_block m2 b').

Module Sim_inj.
(* An axiom for passes that use memory injections. *)
Section Forward_simulation_inject. 
  Context {G1 C1 G2 C2:Type}
          {Sem1 : CompcertCoreSem G1 C1}
          {Sem2 : CompcertCoreSem G2 C2}

          {ge1:G1}
          {ge2:G2}
          {entry_points : list (val * val * signature)}.

  Record Forward_simulation_inject := {
    core_data : Type;

    match_state : core_data -> meminj -> C1 -> mem -> C2 -> mem -> Prop;
    core_ord : core_data -> core_data -> Prop;
    core_ord_wf : well_founded core_ord;

    match_state_siminj: 
      forall d j st1 m1 st2 m2,
        match_state d j st1 m1 st2 m2 -> siminj j m1 m2;

    core_diagram : 
      forall st1 m1 st1' m1', corestep Sem1 ge1 st1 m1 st1' m1' ->
      forall cd st2 j m2,
        match_state cd j st1 m1 st2 m2 ->
        exists st2', exists m2', exists cd', exists j',
          inject_incr j j' /\
          inject_separated j j' m1 m2 /\
          match_state cd' j' st1' m1' st2' m2' /\
          ((corestep_plus Sem2 ge2 st2 m2 st2' m2') \/
            corestep_star Sem2 ge2 st2 m2 st2' m2' /\
            core_ord cd' cd);

    core_initial : forall v1 v2 sig,
      In (v1,v2,sig) entry_points ->
        forall j vals vals' m1 m2,
          Forall2 (val_inject j) vals vals' ->
          Forall2 (Val.has_type) vals' (sig_args sig) ->
          Mem.inject j m1 m2 ->
          exists cd, exists c1, exists c2,
            make_initial_core Sem1 ge1 v1 vals = Some c1 /\
            make_initial_core Sem2 ge2 v2 vals' = Some c2 /\
            match_state cd j c1 m1 c2 m2;

    core_halted : forall cd j c1 m1 c2 m2 (v1:int),
      match_state cd j c1 m1 c2 m2 ->
      safely_halted Sem1 ge1 c1 = Some v1 ->
        (safely_halted Sem2 ge2 c2 = Some v1 /\
         Mem.inject j m1 m2); (*conjunct Mem.inject j m1 m2 could maybe deleted here?*)

    core_at_external : 
      forall cd j st1 m1 st2 m2 e vals1,
        match_state cd j st1 m1 st2 m2 ->
        at_external Sem1 st1 = Some (e,vals1) ->
        exists vals2,
          Mem.inject j m1 m2 /\
          Forall2 (val_inject j) vals1 vals2 /\
          Forall2 (Val.has_type) vals2 (sig_args (ef_sig e)) /\
          at_external Sem2 st2 = Some (e,vals2);
  
    core_after_external :
      forall cd j j' st1 st2 m1 m2 e vals1 vals2 ret1 ret2 m1' m2',
        match_state cd j st1 m1 st2 m2 ->
        Mem.inject j m1 m2 ->
        at_external Sem1 st1 = Some (e,vals1) ->
        at_external Sem2 st2 = Some (e,vals2) ->
        Forall2 (val_inject j) vals1 vals2 ->
      
        inject_incr j j' ->
        inject_separated j j' m1 m2 ->
        Mem.inject j' m1' m2' ->
        val_inject j' ret1 ret2 ->

        mem_unchanged_on (loc_unmapped j) m1 m1' ->  (*together, these 2 conditions say roughly that*)
        mem_unchanged_on (loc_out_of_reach j m1) m2 m2' -> (* spill-locations didn't change*)

        mem_forward m1 m1' ->  
        mem_forward m2 m2' ->

        Forall2 (Val.has_type) vals2 (sig_args (ef_sig e)) ->
        Val.has_type ret2 (proj_sig_res (ef_sig e)) ->

        exists cd', exists st1', exists st2',
          after_external Sem1 ret1 st1 = Some st1' /\
          after_external Sem2 ret2 st2 = Some st2' /\
          match_state cd' j' st1' m1' st2' m2'
    }.

End Forward_simulation_inject.

Implicit Arguments Forward_simulation_inject[[G1] [C1] [G2] [C2]].
End Sim_inj.

(* Next, an axiom for passes that allow the memory to undergo extension. *)
Module Sim_ext.
Section Forward_simulation_extends. 
  Context {G1 C1 G2 C2:Type}
          {Sem1 : CompcertCoreSem G1 C1}
          {Sem2 : CompcertCoreSem G2 C2}

          {ge1:G1}
          {ge2:G2}
          {entry_points : list (val * val * signature)}.

  Record Forward_simulation_extends := {
    core_data : Type;

    match_state : core_data -> C1 -> mem -> C2 -> mem -> Prop;
    core_ord : core_data -> core_data -> Prop;
    core_ord_wf : well_founded core_ord;

    core_diagram : 
      forall st1 m1 st1' m1', corestep Sem1 ge1 st1 m1 st1' m1' ->
      forall cd st2 m2,
        match_state cd st1 m1 st2 m2 ->
        exists st2', exists m2', exists cd',
          match_state cd' st1' m1' st2' m2' /\
          ((corestep_plus Sem2 ge2 st2 m2 st2' m2') \/
            corestep_star Sem2 ge2 st2 m2 st2' m2' /\
            core_ord cd' cd);

    core_initial : forall v1 v2 sig,
      In (v1,v2,sig) entry_points ->
        forall vals vals' m1 m2,
          Forall2 Val.lessdef vals vals' ->
          Forall2 (Val.has_type) vals' (sig_args sig) ->
          Mem.extends m1 m2 ->
          exists cd, exists c1, exists c2,
            make_initial_core Sem1 ge1 v1 vals = Some c1 /\
            make_initial_core Sem2 ge2 v2 vals' = Some c2 /\
            match_state cd c1 m1 c2 m2;

    core_halted : 
      forall cd st1 m1 st2 m2 (v:int),
        match_state cd st1 m1 st2 m2 ->
        safely_halted Sem1 ge1 st1 = Some v ->
          safely_halted Sem2 ge2 st2 = Some v /\
          Mem.extends m1 m2;

    core_at_external : 
      forall cd st1 m1 st2 m2 e vals1,
        match_state cd st1 m1 st2 m2 ->
        at_external Sem1 st1 = Some (e,vals1) ->
        exists vals2,
          Mem.extends m1 m2 /\
          Forall2 Val.lessdef vals1 vals2 /\
          Forall2 (Val.has_type) vals2 (sig_args (ef_sig e)) /\
          at_external Sem2 st2 = Some (e,vals2);

    core_after_external :
      forall cd st1 st2 m1 m2 e vals1 vals2 ret1 ret2 m1' m2',
        match_state cd st1 m1 st2 m2 ->
        at_external Sem1 st1 = Some (e,vals1) ->
        at_external Sem2 st2 = Some (e,vals2) ->

        Forall2 Val.lessdef vals1 vals2 ->
        Forall2 (Val.has_type) vals2 (sig_args (ef_sig e)) ->
        mem_forward m1 m1' ->
        mem_forward m2 m2' ->

        mem_unchanged_on (loc_out_of_bounds m1) m2 m2' -> (*ie spill-locations didn't change*)
        Val.lessdef ret1 ret2 ->
        Mem.extends m1' m2' ->

        Val.has_type ret2 (proj_sig_res (ef_sig e)) ->

        exists st1', exists st2', exists cd',
          after_external Sem1 ret1 st1 = Some st1' /\
          after_external Sem2 ret2 st2 = Some st2' /\
          match_state cd' st1' m1' st2' m2'
   }.
End Forward_simulation_extends.

Implicit Arguments Forward_simulation_extends [[G1] [C1] [G2] [C2]].
End Sim_ext.

  Definition inj_compose (j j' : meminj) : meminj :=
    fun b => match j b with None => None
                          | Some (b', delta') => match j' b' with None => None
                                                            | Some (b'', delta'') => Some(b'', delta' + delta'')
                                                end
             end.

  Lemma inject_incr_compose: forall {j1 j1' j2 j2'}
        (HJ1: inject_incr j1 j1') (HJ2: inject_incr j2 j2'),
        inject_incr (inj_compose j1 j2) (inj_compose j1' j2').
    Proof.
    intros.
    intros b b' delta Hdelta.
    unfold inj_compose. unfold inj_compose in Hdelta.
    remember (j1 b) as j1b.
    destruct j1b; try inversion Hdelta; apply eq_sym in Heqj1b.
    destruct p.
    rewrite (HJ1 _ _ _ Heqj1b).
    remember (j2 b0) as j2b0.
    destruct j2b0; try inversion Hdelta; apply eq_sym in Heqj2b0.
    destruct p.
    rewrite (HJ2 _ _ _ Heqj2b0).
    trivial.
  Qed.

  Lemma inj_compose_NoneD: forall j j' b
      (JJ': inj_compose j j' b = None),
      j b = None \/ (exists b', exists delta', j b = Some(b', delta') /\ j' b' = None).
   Proof. intros.
    unfold inj_compose in *.
    remember (j b) as jb.
    destruct jb. Focus 2. left; trivial.
    destruct p.
    remember (j' b0) as j'b0.
    destruct j'b0. destruct p. inversion JJ'.
    right. exists b0. exists z. auto.
   Qed.

  Lemma inj_compose_SomeD: forall j j' b b' delta
      (JJ': inj_compose j j' b = Some (b', delta)),
      exists b1, exists delta1, exists delta2,
         j b = Some(b1,delta1) /\
         j' b1 = Some(b', delta2) /\ delta1 + delta2 = delta.
   Proof. intros.
    unfold inj_compose in *.
    remember (j b) as jb.
    destruct jb. Focus 2. inversion JJ'.
    destruct p.
    remember (j' b0) as j'b0.
    destruct j'b0. Focus 2. inversion JJ'.
    destruct p. inversion JJ'; subst; clear JJ'.
    exists b0. exists z. exists z0. auto.
   Qed.

  Lemma inj_separated_compose: forall {j1 j1' j2 j2' m1 m2 m3}
        (HJ1: inject_incr j1 j1')
        (HJ2: inject_incr j2 j2')
        (ZZ1 : forall (b b' : block) (delta : Z),
                      j1 b = Some (b', delta) -> Mem.valid_block m2 b')
        (ZZ2 :  forall b : block, ~ Mem.valid_block m2 b -> j2 b = None)
        (Hsep1: inject_separated j1 j1' m1 m2)
        (Hsep2: inject_separated j2 j2' m2 m3),
    inject_separated (inj_compose j1 j2) (inj_compose j1' j2') m1 m3.
  Proof.
    intros. intros b1 b3 delta Hj1 Hj1'.
    apply inj_compose_SomeD in Hj1'. destruct Hj1' as [b2 [delta2 [delta3 [Hj1' [Hj2' HD]]]]].
    apply inj_compose_NoneD in Hj1.
    destruct Hj1.
    (*j1 b1 = None*)
       destruct (Hsep1 _ _ _ H Hj1'); clear Hsep1.
       split; try assumption.
       assert (Y2 := ZZ2 _ H1).
       apply (Hsep2 _ _ _ Y2 Hj2').
    (*j1 b1 = Some (b', delta')*)
       destruct H as [b' [delta' [H1b' H2b']]]. subst.
       assert (ZZ := HJ1 _ _ _ H1b'). rewrite Hj1' in ZZ. inversion ZZ; subst; clear ZZ.
       destruct (Hsep2 _ _ _ H2b' Hj2'); clear Hsep2.
       split; try assumption.
       intros ZZ.
       apply H.
       apply (ZZ1 _ _ _ H1b').
  Qed.
  
  Lemma inject_separated_compose: forall {j1 j1' j2 j2' m1 m2 m3}
        (HJ1: inject_incr j1 j1')
        (HJ2: inject_incr j2 j2')
        (ZZ1: siminj j1 m1 m2)
        (ZZ2: siminj j2 m2 m3)
        (Hsep1: inject_separated j1 j1' m1 m2)
        (Hsep2: inject_separated j2 j2' m2 m3),
    inject_separated (inj_compose j1 j2) (inj_compose j1' j2') m1 m3.
  Proof.
    intros. destruct ZZ1. destruct ZZ2.
    eapply inj_separated_compose; eauto. 
  Qed. 
(*
  Lemma m_inj_sep_compose: forall {j1 j1' j2 j2' m1 m2 m3}
        (HJ1: inject_incr j1 j1')
        (HJ2: inject_incr j2 j2')
        (ZZ1 : Mem.mem_inj j1 m1 m2)
        (ZZ2 : Mem.mem_inj j2 m2 m3)
        (Hsep1: inject_separated j1 j1' m1 m2)
        (Hsep2: inject_separated j2 j2' m2 m3),
    inject_separated (inj_compose j1 j2) (inj_compose j1' j2') m1 m3.
  Proof.
    intros. intros b1 b3 delta Hj1 Hj1'.
    apply inj_compose_SomeD in Hj1'. destruct Hj1' as [b2 [delta2 [delta3 [Hj1' [Hj2' HD]]]]].
    apply inj_compose_NoneD in Hj1.
    destruct Hj1.
    (*j1 b1 = None*)
       destruct (Hsep1 _ _ _ H Hj1'); clear Hsep1.
       split; try assumption.
       intros ZZ.
       remember (j2 b2) as zz.
       destruct zz; apply eq_sym in Heqzz.  
       Focus 2. (*j2 b2 = None*) eapply Hsep2. apply Heqzz. apply Hj2'. apply ZZ.
       (*j2 b2 = Some p*) destruct p.
         destruct ZZ2. specialize (HJ2 _ _ _ Heqzz).  rewrite HJ2 in Hj2'.  inv Hj2'.
         clear Hsep2.
       unfold inject_separated in Hsep2.
       assert (Y2 := ZZ2 _ H1).
       apply (Hsep2 _ _ _ Y2 Hj2').
    (*j1 b1 = Some (b', delta')*)
       destruct H as [b' [delta' [H1b' H2b']]]. subst.
       assert (ZZ := HJ1 _ _ _ H1b'). rewrite Hj1' in ZZ. inversion ZZ; subst; clear ZZ.
       destruct (Hsep2 _ _ _ H2b' Hj2'); clear Hsep2.
       split; try assumption.
       intros ZZ.
       apply H.
       apply (ZZ1 _ _ _ H1b').
  Qed.
*)  

(*
  Lemma injt_separated_compose: forall {j1 j1' j2 j2' m1 m2 m3}
        (HJ1: inject_incr j1 j1')
        (HJ2: inject_incr j2 j2')
        (ZZ1 :  forall b : block, ~ Mem.valid_block m1 b -> j1 b = None)
        (Z21 :  forall b : block, ~ Mem.valid_block m2 b -> j2 b = None)
        (Hsep1: inject_separated j1 j1' m1 m2)
        (Hsep2: inject_separated j2 j2' m2 m3),
    inject_separated (inj_compose j1 j2) (inj_compose j1' j2') m1 m3.
  Proof.
    intros. intros b1 b3 delta Hj1 Hj1'.
    apply inj_compose_SomeD in Hj1'. destruct Hj1' as [b2 [delta2 [delta3 [Hj1' [Hj2' HD]]]]].
    apply inj_compose_NoneD in Hj1.
    destruct Hj1.
    (*j1 b1 = None*)
       destruct (Hsep1 _ _ _ H Hj1'); clear Hsep1.
       split; try assumption.
       remember (j2 b2) as jb.
       destruct jb; apply eq_sym in Heqjb.
       (*j2 b2 = Some p*) destruct p as [bb ddelta]. clear Hsep2.
          intros CONTRA.
          apply H1.
          apply (Mem.valid_block_inject_1 _ _ _ _ _ _ Heqjb ZZ2).
       (*j2 b2 = None*)
          apply (Hsep2 _ _ _ Heqjb Hj2').
    (*j1 b1 = Some (b', delta')*)
       destruct H as [b' [delta' [H1b' H2b']]]. subst.
       assert (ZZ := HJ1 _ _ _ H1b'). rewrite Hj1' in ZZ. inversion ZZ; subst; clear ZZ.
       destruct (Hsep2 _ _ _ H2b' Hj2'); clear Hsep2.
       split; try assumption.
       intros CON.
       apply H.
       apply (Mem.valid_block_inject_2 _ _ _ _ _ _ H1b' ZZ1). 
  Qed.  

  Lemma inject_separated_compose: forall {j1 j1' j2 j2' m1 m2 m3}
        (HJ1: inject_incr j1 j1')
        (HJ2: inject_incr j2 j2')
        (ZZ1 : Mem.inject j1 m1 m2)
        (ZZ2 : Mem.inject j2 m2 m3)
        (Hsep1: inject_separated j1 j1' m1 m2)
        (Hsep2: inject_separated j2 j2' m2 m3),
    inject_separated (inj_compose j1 j2) (inj_compose j1' j2') m1 m3.
  Proof.
    intros. intros b1 b3 delta Hj1 Hj1'.
    apply inj_compose_SomeD in Hj1'. destruct Hj1' as [b2 [delta2 [delta3 [Hj1' [Hj2' HD]]]]].
    apply inj_compose_NoneD in Hj1.
    destruct Hj1.
    (*j1 b1 = None*)
       destruct (Hsep1 _ _ _ H Hj1'); clear Hsep1.
       split; try assumption.
       remember (j2 b2) as jb.
       destruct jb; apply eq_sym in Heqjb.
       (*j2 b2 = Some p*) destruct p as [bb ddelta]. clear Hsep2.
          intros CONTRA.
          apply H1.
          apply (Mem.valid_block_inject_1 _ _ _ _ _ _ Heqjb ZZ2).
       (*j2 b2 = None*)
          apply (Hsep2 _ _ _ Heqjb Hj2').
    (*j1 b1 = Some (b', delta')*)
       destruct H as [b' [delta' [H1b' H2b']]]. subst.
       assert (ZZ := HJ1 _ _ _ H1b'). rewrite Hj1' in ZZ. inversion ZZ; subst; clear ZZ.
       destruct (Hsep2 _ _ _ H2b' Hj2'); clear Hsep2.
       split; try assumption.
       intros CON.
       apply H.
       apply (Mem.valid_block_inject_2 _ _ _ _ _ _ H1b' ZZ1). 
  Qed.  
*)
  Lemma memval_inject_compose: forall j1 ofs b1 m1 delta' b' m2 b2 m3 delta'' j2
     (Hj1 : memval_inject j1 (ZMap.get ofs (ZMap.get b1 (Mem.mem_contents m1)))
          (ZMap.get (ofs + delta') (ZMap.get b' (Mem.mem_contents m2))))
     (Hj2 : memval_inject j2
         (ZMap.get (ofs + delta') (ZMap.get b' (Mem.mem_contents m2)))
         (ZMap.get (ofs + delta' + delta'')
            (ZMap.get b2 (Mem.mem_contents m3))))
     (Rd: Mem.perm m3 b2 (ofs + delta' + delta'') Cur Readable),
     memval_inject (inj_compose j1 j2)
      (ZMap.get ofs (ZMap.get b1 (Mem.mem_contents m1)))
      (ZMap.get (ofs + delta' + delta'') (ZMap.get b2 (Mem.mem_contents m3))).
   Proof. intros.
     remember ((ZMap.get (ofs + delta') (ZMap.get b' (Mem.mem_contents m2)))) as v2.
     destruct v2.
     (*undef*)
        inversion Hj1; clear Hj1. inversion Hj2; clear Hj2.
        econstructor.
     (*Byte i*)
        inversion Hj1; clear Hj1.
          subst. inversion Hj2; clear Hj2. subst. econstructor.
          subst. inversion Hj2; clear Hj2. subst. econstructor.
     (*Pointer*)
        inversion Hj1; clear Hj1.
          (*Ptr*)
          subst. inversion Hj2; clear Hj2. subst.
          econstructor.
             unfold inj_compose. rewrite H2. rewrite H3. reflexivity.
          remember (ofs + delta' + delta'') as myofs.
          admit. (*again need properties of maxint I think*)
          (*Undef*)
          subst. inversion Hj2; clear Hj2. subst. econstructor. 
   Qed.


Lemma siminj_compose j j' m1 m2 m3 :
  siminj j m1 m2 -> siminj j' m2 m3 -> 
  siminj (inj_compose j j') m1 m3.
Proof.
unfold inj_compose, siminj. intros [H1 H2][H3 H4].
split. intros.
case_eq (j b). intros [b' z] eq.
case_eq (j' b'). intros [b2 z2] eq2.
specialize (H1 _ H). congruence. auto. auto.
intros until delta.
case_eq (j b). intros [b2 z2] eq2.
case_eq (j' b2). intros [b3 z3] eq3.
inversion 1; subst.
eapply H4; eauto.
intros ?; inversion 1.
congruence.
Qed.

Section ForwardSimInjectInjectCompose.
  Context {G1 C1 G2 C2 G3 C3:Type}.
  Variable Sem1 : CompcertCoreSem G1 C1.
  Variable Sem2 : CompcertCoreSem G2 C2.
  Variable Sem3 : CompcertCoreSem G3 C3.
  Variable ge1 :G1.
  Variable ge2: G2.
  Variable ge3:G3.

  Variable entry_points12 : list (val*val*signature).
  Variable entry_points23 : list (val*val*signature).
  Variable FSim12 : Sim_inj.Forward_simulation_inject Sem1 Sem2 ge1 ge2 entry_points12.
  Variable FSim23 : Sim_inj.Forward_simulation_inject Sem2 Sem3 ge2 ge3 entry_points23.

  Variable entry_points13: list (val*val*signature).
  Variable EPC: entry_points_compose entry_points12 entry_points23 entry_points13.

  Let data13 := (Sim_inj.core_data FSim23 * (*(option C2) **) Sim_inj.core_data FSim12)%type. 

  Let sem_compose_ord := (lex_ord (Sim_inj.core_ord FSim23) (Sim_inj.core_ord FSim12)).
  Definition well_founded_sem_compose_ord := wf_lex_ord (Sim_inj.core_ord_wf FSim23) (Sim_inj.core_ord_wf FSim12).

  Inductive compose_match_state : data13 -> meminj -> C1 -> mem -> C3 -> mem -> Prop :=
    intro_compose_match_state : forall d12 j1 j2 c2 m2 d23 c1 m1 c3 m3,
      Sim_inj.match_state FSim12 d12 j1 c1 m1 c2 m2 ->
      Sim_inj.match_state FSim23 d23 j2 c2 m2 c3 m3 ->
      compose_match_state (d23,(*(Some c2,m2),*)d12) (inj_compose j1 j2) c1 m1 c3 m3.
(*
  Lemma compase_match_inj: forall (d : data13) (j : meminj) (st1 : C1) (m1 : mem) (st2 : C3) (m2 : mem),
          compose_match_state d j st1 m1 st2 m2 -> Mem.mem_inj j m1 m2.
     Proof. intros. inversion H; subst; clear H.
       assert (Z1 := Sim_inj.match_inj FSim12 d12 _ _ _ _ _ H0).
       assert (Z2 := Sim_inj.match_inj FSim23 d23 _ _ _ _ _ H1).
       eapply mem_inj_compose. apply Z1. apply Z2.       
     Qed.
*)

  (* An axiom stating that inject forward simulations compose *)
  Lemma forward_simulation_inject_inject_compose :
    Sim_inj.Forward_simulation_inject Sem1 Sem3 ge1 ge3 entry_points13.
  Proof.
    intros.
    eapply (@Sim_inj.Build_Forward_simulation_inject G1 C1 G3 C3 Sem1 Sem3 ge1 ge3 entry_points13 _ compose_match_state).
      apply well_founded_sem_compose_ord.
      (*apply compose_match_inj.*)

      intros until m2. intros [H1 H2]. intros.
      apply Sim_inj.match_state_siminj in H.
      apply Sim_inj.match_state_siminj in H0.
      
      
  Lemma fsim_compose_diagram: forall (st1 : C1) (m1 : mem) (st1' : C1) (m1' : mem),
          corestep Sem1 ge1 st1 m1 st1' m1' ->
          forall (cd : data13) (st3 : C3) (j : meminj) (m3 : mem),
           compose_match_state cd j st1 m1 st3 m3 ->
           exists st3' : C3,
           exists m3' : mem,
           exists cd' : data13,
           exists j' : meminj,
            inject_incr j j' /\
            inject_separated j j' m1 m3 /\
            compose_match_state cd' j' st1' m1' st3' m3' /\
            (corestep_plus Sem3 ge3 st3 m3 st3' m3' \/
              corestep_star Sem3 ge3 st3 m3 st3' m3' /\
              lex_ord (Sim_inj.core_ord FSim23) (Sim_inj.core_ord FSim12) cd' cd).
    Proof.
    intros. inv H0. rename c2 into st2.
    destruct (Sim_inj.core_diagram FSim12 st1 m1 st1' m1'  H d12 st2 j1 m2 H1) as
      [st2' [m2' [d' [j1' [Hj1' [? [? ?]]]]]]].
    assert (H5: corestep_plus Sem2 ge2 st2 m2 st2' m2' \/
               ((st2,m2) = (st2',m2') /\ Sim_inj.core_ord FSim12 d' d12) ).
      destruct H4. auto.
      destruct H4.
        destruct H4.
        destruct x. right. split; auto.
                    left. exists x; auto.
    clear H4.
    destruct H5.
    Focus 2.
    (*case (st2, m2) = (st2', m2') /\ Sim_inj.core_ord FSim12 d' d12*)
      destruct H4.
      exists st3. exists m3. exists (d23, d'). (*was : exists (d',(Some c2,m2),d23).*)
      split. constructor; auto.
      apply extends_refl.
      inv H4.
      split. constructor; auto.
      right. split. exists O. simpl; auto.
      apply t_step. constructor 1; auto.

    (*case corestep_plus Sem2 ge2 st2 m2 st2' m2'*)
      destruct H4.
      assert (Inj1 := Sim_inj.match_inj FSim12 _ _ _ _ _ _ H1).
      assert (Inj2 := Sim_inj.match_inj FSim23 _ _ _ _ _ _ H2).
      generalize dependent m3. generalize dependent st3. generalize dependent d23. 
      generalize dependent m2'. generalize dependent st2'.
      generalize dependent m2. generalize dependent st2.
(*    revert d23 c2 m2 c2' m2' st3 m3 H2 H3 H4.*)
    induction x; intros. 
    (*Base*)
      simpl in H4.
      destruct H4 as [st3' [m3' [? ?]]].
      inv H5.
      destruct (Sim_inj.core_diagram FSim23 st2 m2 st2' m2' H4 d23 st3 j2 m3 H2) as 
        [st3' [m3' [d'' [j2' [Hj2' [? [? ?]]]]]]].
      exists st3'. exists m3'. exists (d'',d'). (*old proof had (d',(Some c2',m2'),d'').*)
      exists (inj_compose j1' j2').
      split. eapply (inject_incr_compose Hj1' Hj2').
      split. eapply inject_separated_compose. apply Hj1'. apply Hj2'. apply Inj1. apply Inj2. apply H0. apply H5.
      split. econstructor. apply H3. apply H6.
      destruct H7; auto. destruct H7.
      right. split; try assumption. apply lex_ord_left. apply H8.
    (*Step*)
      remember (S x) as x'. simpl in H4.
      destruct H4 as [st2'' [m2'' [? ?]]]. subst x'.
      destruct (Sim_inj.core_diagram FSim23
        st2 m2 st2'' m2'' H4 d23 st3 _ m3 H2) as [st3' [m3' [d'' [? [? [? [? ?]]]]]]].
      specialize (IHx _ _ H1 H0 Inj1 _ _ H3). xx d'' st2'' m2'' st2' m2').
    specialize (IHx c3' m3'). specialize (IHx H6 H3 H4).
    destruct IHx as [c3'' [m3'' [d''' [? [? ?]]]]].
    exists c3''. exists m3''. exists d'''.
    split; auto.
    inv H8. constructor. auto.
    eapply extends_trans; eauto.
    split. auto.



      destruct H4.
    destruct x. right.
    split; auto. exists O; auto.
    apply t_step. constructor 2. auto.
    left. exists x; auto.

    split. constructor; auto.

    split; auto. split; auto.
    destruct H6; auto. destruct H6.
    destruct H6.
    destruct x. right.
    split; auto. exists O; auto.
    apply t_step. constructor 2. auto.
    left. exists x; auto.
    remember (S x) as x'. simpl in H4.
    destruct H4 as [c2'' [m2'' [? ?]]]. subst x'.
    destruct (fsim_diagram FSim23
      c2 m2 c2'' m2'' H1
      d23 st3 m3 H2) as [c3' [m3' [d'' [? [? ?]]]]].
    specialize (IHx d'' c2'' m2'' c2' m2').
    specialize (IHx c3' m3'). specialize (IHx H6 H3 H4).
    destruct IHx as [c3'' [m3'' [d''' [? [? ?]]]]].
    exists c3''. exists m3''. exists d'''.
    split; auto.
    inv H8. constructor. auto.
    eapply extends_trans; eauto.
    split. auto.

    destruct H7; destruct H10.
    left. destruct H7 as [n1 ?]. destruct H10 as [n2 ?].
    exists (n1 + S n2)%nat.
    change (S (n1 + S n2)) with (S n1 + S n2)%nat.
    rewrite corestepN_add. eauto.
    destruct H10.
    left. destruct H7 as [n1 ?]. destruct H10 as [n2 ?].
    exists (n1 + n2)%nat.
    change (S (n1 + n2)) with (S n1 + n2)%nat.
    rewrite corestepN_add. eauto.
    left. destruct H7.
    destruct H7 as [n1 ?]. destruct H10 as [n2 ?].
    exists (n1 + n2)%nat.
    replace (S (n1 + n2)) with (n1 + S n2)%nat by omega.
    rewrite corestepN_add. eauto.
    right.
    destruct H7. destruct H10. split.
    destruct H7 as [n1 ?]. destruct H10 as [n2 ?].
    exists (n1 + n2)%nat.
    rewrite corestepN_add. eauto.
    eapply t_trans; eauto.
    apply t_step.
    constructor 2. auto.
    destruct H4.
    exists st3. exists m3. exists (d',(Some c2,m2),d23).
    split. constructor; auto.
    apply extends_refl.
    inv H4.
    split. constructor; auto.
    right. split. exists O. simpl; auto.
    apply t_step. constructor 1; auto.
  Qed.

      
    Qed.

  (* An axiom stating that inject forward simulations compose *)
  Lemma forward_simulation_inject_inject_compose :
    Sim_inj.Forward_simulation_inject Sem1 Sem3 ge1 ge3 entry_points13.
  Proof.
    intros.
    eapply (@Sim_inj.Build_Forward_simulation_inject G1 C1 G3 C3 Sem1 Sem3 ge1 ge3 entry_points13 _ compose_match_state).
      apply well_founded_sem_compose_ord.


  (* An axiom stating that inject forward simulations compose *)
  Lemma forward_simulation_inject_inject_compose :
    Sim_inj.Forward_simulation_inject Sem1 Sem3 ge1 ge3 entry_points13.
  Proof.
    intros.
    destruct FSim12. simpl in *. 
    destruct FSim23. simpl in *. 
  Qed.

  Lemma fsim_compose_diagram :
      forall st1 m1 st1' m1', corestep Sem1 ge1 st1 m1 st1' m1' ->
      forall d st3 m3, compose_match_state d st1 m1 st3 m3 ->
        exists st3', exists m3', exists d',
          compose_extends_data _ _ _
             (fsim_struct FSim12) (fsim_struct FSim23) d d' /\
          compose_match_state d' st1' m1' st3' m3' /\
          ((corestep_plus Sem3 ge3 st3 m3 st3' m3') \/
            corestep_star Sem3 ge3 st3 m3 st3' m3' /\
            clos_trans _ sem_compose_ord (d',st1') (d,st1)).
  Proof.
    intros. inv H0.
    destruct (fsim_diagram  FSim12
      st1 m1 st1' m1' H d12 c2 m2 H1) as
    [c2' [m2' [d' [? [? ?]]]]].
    assert (
      corestep_plus Sem2 ge2 c2 m2 c2' m2' \/
      (c2,m2) = (c2',m2') /\
      fsim_order FSim12 (d', st1') (d12, st1)).
    destruct H4. auto. destruct H4.
    destruct H4. destruct x.
    right. split; auto.
    left. exists x; auto.
    clear H4. destruct H5.
    destruct H4.
    clear H1.
    revert d23 c2 m2 c2' m2' st3 m3 H2 H3 H4.
    induction x; intros. simpl in H4.
    destruct H4 as [c3' [m3' [? ?]]].
    inv H4.
    destruct (fsim_diagram FSim23
      c2 m2 c2' m2' H1 d23 st3 m3 H2) as [c3' [m3' [d'' [? [? ?]]]]].
    exists c3'. exists m3'. exists (d',(Some c2',m2'),d'').
    split. constructor; auto.

    split; auto. split; auto.
    destruct H6; auto. destruct H6.
    destruct H6.
    destruct x. right.
    split; auto. exists O; auto.
    apply t_step. constructor 2. auto.
    left. exists x; auto.
    remember (S x) as x'. simpl in H4.
    destruct H4 as [c2'' [m2'' [? ?]]]. subst x'.
    destruct (fsim_diagram FSim23
      c2 m2 c2'' m2'' H1
      d23 st3 m3 H2) as [c3' [m3' [d'' [? [? ?]]]]].
    specialize (IHx d'' c2'' m2'' c2' m2').
    specialize (IHx c3' m3'). specialize (IHx H6 H3 H4).
    destruct IHx as [c3'' [m3'' [d''' [? [? ?]]]]].
    exists c3''. exists m3''. exists d'''.
    split; auto.
    inv H8. constructor. auto.
    eapply extends_trans; eauto.
    split. auto.

    destruct H7; destruct H10.
    left. destruct H7 as [n1 ?]. destruct H10 as [n2 ?].
    exists (n1 + S n2)%nat.
    change (S (n1 + S n2)) with (S n1 + S n2)%nat.
    rewrite corestepN_add. eauto.
    destruct H10.
    left. destruct H7 as [n1 ?]. destruct H10 as [n2 ?].
    exists (n1 + n2)%nat.
    change (S (n1 + n2)) with (S n1 + n2)%nat.
    rewrite corestepN_add. eauto.
    left. destruct H7.
    destruct H7 as [n1 ?]. destruct H10 as [n2 ?].
    exists (n1 + n2)%nat.
    replace (S (n1 + n2)) with (n1 + S n2)%nat by omega.
    rewrite corestepN_add. eauto.
    right.
    destruct H7. destruct H10. split.
    destruct H7 as [n1 ?]. destruct H10 as [n2 ?].
    exists (n1 + n2)%nat.
    rewrite corestepN_add. eauto.
    eapply t_trans; eauto.
    apply t_step.
    constructor 2. auto.
    destruct H4.
    exists st3. exists m3. exists (d',(Some c2,m2),d23).
    split. constructor; auto.
    apply extends_refl.
    inv H4.
    split. constructor; auto.
    right. split. exists O. simpl; auto.
    apply t_step. constructor 1; auto.
  Qed.

Obligation Tactic := intuition.

  Program Definition forward_simulation_compose : ForwardSimulation Sem1 Sem3 ge1 ge3 entry_points13 match_ext13:=
    @Build_ForwardSimulation _ _ _ _ _ _ _ _  ge1 ge3 entry_points13 match_ext13
      data13
      (FSimStruct_compose _ _ _
         (fsim_struct FSim12) (fsim_struct FSim23))
      compose_match_state
      (clos_trans _ sem_compose_ord)
      (wf_clos_trans _ _ well_founded_sem_compose_ord)
      fsim_compose_diagram
      _ _ _ _.
  Next Obligation.
    rename v2 into v3.
    assert (J1: exists v2, In (v1,v2,sig) entry_points12 /\ In (v2,v3,sig) entry_points23).
    pose proof EPC.
    clear - H H2.
    induction H2.
    simpl in H. destruct H. inv H.
    exists v2; split; simpl; auto.
    destruct (IHentry_points_compose H) as [v2' [? ?]].
    exists v2'; simpl; split; auto.
   inv H.
   destruct J1 as [v2 [J12 J23]].
    rename H0 into H5. rename H1 into H6.
    generalize (fsim_initial FSim12 _ _ _ J12); intro H2.
    generalize (fsim_initial FSim23 _ _ _ J23); intro H4.
    clear H; do 4 pose proof I.
    inv H6.
    assert (exists vals_,
      match_vals (fsim_struct FSim12) d12' (sig_args sig) vals vals_ /\
      match_vals (fsim_struct FSim23) d23' (sig_args sig) vals_ vals').
    clear -H5.
    revert vals' H5. generalize (sig_args sig). induction vals; simpl; intros.
    inv H5. exists nil; split; constructor.
    inv H5. eapply IHvals in H4. destruct H4 as [? [? ?]].
    destruct H2 as [? [? ?]].
    exists (x0::x). 
    split; constructor; auto.
    destruct H6 as [vals_ [? ?]].
    eapply H2 in H7; eauto.
    eapply H4 in H8; eauto.
    destruct H7 as [d12'' [c1 [c2_ [? [? [? ?]]]]]].
    destruct H8 as [d23'' [c2_' [c3 [? [? [? ?]]]]]].
    assert (c2_ = c2_') by congruence. subst c2_'.
    exists (d12'',(Some c2_,m2'),d23'').
    exists c1. exists c3.
    intuition.
    constructor; auto.
    constructor; auto.
  Qed.
  Next Obligation.
    inv H.
    eapply (fsim_halted FSim12) in H0; eauto.
    destruct H0 as [v2 [? [? ?]]].
    eapply (fsim_halted FSim23) in H; eauto.
    destruct H as [v3 [? [? ?]]].
    exists v3; intuition.
    simpl. exists v2; simpl; split; auto.
    constructor; auto.
  Qed.
  Next Obligation.
    inv H.
    eapply fsim_at_external in H0; eauto.
    destruct H0 as [e2 [vals' [? [? [??]]]]].
    eapply fsim_at_external in H0; eauto.
    destruct H0 as [e3 [vals'' [? [? [??]]]]].
    exists e3. exists vals''. intuition.
    exists e2; split; auto.

    clear -H3 H6.
    revert vals' vals'' H3 H6.
    generalize (sig_args sig).
    induction vals; intros. inv H3. inv H6.
    constructor.
    inv H3. inv H6.
    constructor.
    econstructor; simpl; split; eauto.
    eapply IHvals; eauto.
    constructor; auto.
  Qed.
  Next Obligation.
    inv H.
    inv H4. destruct H5 as [ret' [? ?]].
    generalize H0; intros.
    eapply fsim_at_external in H0; eauto.
    destruct H0 as [e2' [vals'' [? [? [??]]]]].
    generalize H8; intros.
    eapply fsim_at_external in H8; eauto.
    destruct H8 as [e3' [vals''' [? [? [??]]]]].
    rewrite H12 in H1. inv H1.
    eapply fsim_after_external with (d':=d12') in H16; eauto.
    destruct H16 as [st1' [st2' [d'' [? [? [? ?]]]]]].
    eapply fsim_after_external with (d':=d23') in H17; eauto.
    destruct H17 as [st2'' [st3' [d''' [? [? [? ?]]]]]].
    exists st1'. exists st3'. exists (d'',(Some st2'',m2'0),d''').
    intuition.
    constructor; auto.
    constructor; auto.
    replace st2'' with st2'; auto. congruence.
  Qed.

End ForwardSimCompose.

QedEnd