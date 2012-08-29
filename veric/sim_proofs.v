Require Import Wellfounded.
Require Import veric.base.
Require Import veric.sim.
Require Import compcert.Events.
(*Require Import compcert.Mem_inject.*)

Lemma app_last: forall {A} l (a:A) m, last (l ++ a :: nil) m = a.
  Proof.
    intros A l.
    induction l; trivial.
    intros.  simpl.  remember (l ++ a0 :: nil ) as zz.
      destruct zz. apply eq_sym in Heqzz. apply app_eq_nil in Heqzz.  destruct Heqzz; subst. congruence.
        rewrite Heqzz.  apply IHl.
  Qed.

Lemma app_last1: forall {A} (a:A) l m f g, last (f ++ a :: l) m = last (g ++ a :: l) m.
  Proof. intros until f.
     induction f; simpl; intros.
        induction g; simpl; intros. trivial.
          rewrite IHg. clear IHg. remember ((g ++ a :: l)) as z. destruct z. apply eq_sym in Heqz. apply app_eq_nil in Heqz. destruct Heqz; congruence. trivial.
        remember (f ++ a :: l) as z.
          destruct z. apply eq_sym in Heqz. apply app_eq_nil in Heqz. destruct Heqz; congruence.
          apply IHf.
  Qed.

Lemma app_last2: forall {A} l (b:list A) m a, last l a = last (b ++ a :: l) m.
  Proof. intros A l.
     induction l; simpl. intros. rewrite app_last. trivial.
     destruct l. intros.
           assert (ZZ:= @app_last A (b++a0::nil) a m).
             assert (Qq:(b ++ a0 :: a :: nil) = (b ++ a0 :: nil) ++ a :: nil). 
               rewrite <- app_assoc. simpl. trivial.
             rewrite Qq. rewrite ZZ. trivial.
     intros. specialize (IHl (b++(a::nil)) m a1).
          rewrite IHl; clear IHl.
          remember (b ++ a :: nil) as z. clear Heqz.
          assert (Eq1: z ++ a1 :: a0 :: l = (z ++ a1::nil) ++ a0 :: l).
            rewrite <- app_assoc. f_equal. 
          rewrite Eq1. clear Eq1. 
          assert (Eq2: b ++ a1 :: a :: a0 :: l = (b ++ a1 :: a::nil) ++ a0 :: l).
            rewrite <- app_assoc. f_equal. 
          rewrite Eq2. clear Eq2.
          eapply app_last1.
Qed. 

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

Fixpoint injlist_compose (j : list meminj) : meminj :=
  match j with 
     nil => fun b => Some (b,0)
  | cons h t => Mem.meminj_compose h (injlist_compose t)
  end.

Module Sim_inj.
(* An axiom for passes that use memory injections. *)
Section Forward_simulation_inject. 
  Context {G1 C1 G2 C2:Type}
          {Sem1 : CompcertCoreSem G1 C1}
          {Sem2 : CompcertCoreSem G2 C2}

          {ge1:G1}
          {ge2:G2}
          {entry_points : list (val * val * signature)}.

Fixpoint check_injectlist (js : list meminj) m1 ms lst : Prop :=
   match js,ms with
     nil, nil => m1 = lst
   | cons j J, cons m M => Mem.inject j m1 m /\ check_injectlist J m M lst
   | _ , _ => False
   end.

Fixpoint check_returns (js : list meminj) ret1 (rets : list val) r : Prop :=
  match js, rets with 
     nil, nil => r=ret1
  | (j::J), (ret2::R) => val_inject j ret1 ret2 /\ check_returns J ret2 R r
  | _ , _ => False
  end.

Fixpoint check_valslist (js : list meminj) (vals1 : list val) (vals:list (list val)) (w: list val): Prop :=
   match js,vals with
     nil, nil => vals1 = w 
   | cons j J, cons vals2 V => 
          Forall2 (val_inject j) vals1 vals2 /\ check_valslist J vals2 V w
   | _ , _ => False
   end.


Lemma check_injectlist_D: 
      forall J r1 R r2, check_injectlist  J r1 R r2 -> 
      length R = length J /\ last R r1 = r2.
  Proof.
    intros J.
    induction J.
       intros.
       destruct R; try contradiction. simpl in *. auto.
    intros. 
      destruct R; try contradiction. simpl in *.
       destruct H.
       destruct (IHJ _ _ _ H0). subst. clear IHJ.
       rewrite H1.  split; trivial.
       rewrite (app_last2 _ nil r1 m). simpl. trivial.
  Qed.    

Lemma check_returns_D: 
      forall J r1 R r2, check_returns J r1 R r2 -> 
      length R = length J /\ last R r1 = r2.
  Proof.
    intros J.
    induction J.
       intros.
       destruct R; try contradiction. simpl in *. auto.
    intros. 
      destruct R; try contradiction. simpl in *.
       destruct H.
       destruct (IHJ _ _ _ H0). subst. clear IHJ.
       rewrite H1.  split; trivial.
       rewrite (app_last2 _ nil r1 v). simpl. trivial.
  Qed.    

  Lemma check_valslist_D: 
      forall J vals1 V vals2, check_valslist J vals1 V vals2 -> 
      length J = length V /\ last V vals1 = vals2.
  Proof.
    intros J.
    induction J.
       intros.
       destruct V; try contradiction. simpl in *. auto.
    intros. 
      destruct V; try contradiction. simpl in *.
       destruct H.
       destruct (IHJ _ _ _ H0). subst. clear IHJ.
       rewrite H1.  split; trivial.
       rewrite (app_last2 _ nil vals1 l). simpl. trivial.
  Qed.    

Fixpoint mem_square js m1 ms m1' ms' : Prop :=
  match js, ms, ms' with
    nil, nil , nil => mem_forward m1 m1' 
 |  j::jss, m2::mss, m2'::mss' => mem_unchanged_on (loc_unmapped j) m1 m1' /\
                                 mem_unchanged_on (loc_out_of_reach j m1) m2 m2' /\
                                 mem_forward m1 m1' /\ mem_square jss m2 mss m2' mss'
 | _ , _ , _ => False
  end.

Lemma mem_square_mem_forward: 
      forall js m1 ms m1' ms', mem_square js m1 ms m1' ms' -> mem_forward m1 m1'.
  Proof.
    intro js.
    induction js; simpl; intros.
      destruct ms; try contradiction.
      destruct ms'; try contradiction. trivial. 
    destruct ms; try contradiction.
      destruct ms'; try contradiction.
      destruct H as [_ [_ [X _]]]. trivial.
  Qed. 
  Lemma mem_square_l: forall J M M' m m' JJ MM MM', 
        mem_square (J++JJ) m (M++MM) m' (M'++MM') ->
        length J = length M -> length J = length M' ->
        mem_square J m M m' M'.
    Proof.
       intros J.
       induction J; simpl; intros.
          destruct M; simpl in *; try congruence. 
          destruct M'; simpl in *; try congruence.
          eapply mem_square_mem_forward; apply H.
        destruct M; simpl in *; try congruence. 
          destruct M'; simpl in *; try congruence.
          inv H0. inv H1.
          destruct H as [UC1 [UC2 [MF MS]]].
          specialize (IHJ _ _ _ _ _ _ _ MS H3 H2); eauto.
    Qed.

  Lemma mem_square_r: forall J M M' m m' JJ MM MM' j mm mm',
        mem_square (J++(j::JJ)) m (M++(mm::MM)) m' (M'++(mm'::MM')) ->
        length J = length M -> length J = length M' ->
        mem_square JJ mm MM mm' MM'.
    Proof.
       intros J.
       induction J; simpl; intros.
          destruct M; simpl in *; try congruence. 
          destruct M'; simpl in *; try congruence.
          destruct H as [UC1 [UC2 [MF MS]]]. trivial.
        destruct M; simpl in *; try congruence. 
          destruct M'; simpl in *; try congruence.
          inv H0. inv H1.
          destruct H as [UC1 [UC2 [MF MS]]].
          apply (IHJ _ _ _ _ _ _ _ _ _ _ MS H3 H2). 
  Qed.
(*
Fixpoint mem_squareUni js m1 m2 m1' m2' : Prop :=
   mem_unchanged_on (loc_unmapped (injlist_compose js)) m1 m1' /\
   mem_unchanged_on (loc_out_of_reach (injlist_compose js) m1) m2 m2' /\
   mem_forward m1 m1'.
*)

  Lemma mem_square_D: forall J m M m' M', 
          mem_square J m M m' M' ->  
          length M = length J /\ length M' = length J.
   Proof.
     intros J.
     induction J; intros.
       destruct M; destruct M'; simpl in *; try contradiction.
       split; trivial.
     destruct M; destruct M'; simpl in *; try contradiction.
       destruct H as [? [? [? ?]]]. 
       destruct (IHJ _ _ _ _ H2). 
       rewrite H3.  rewrite H4. split; trivial.
  Qed.
  (*
Fixpoint mem_square2 js m1 ms lst m1' ms' lst': Prop :=
  match js, ms, ms' with
    nil, (m::m2::nil), (m'::m2'::nil) => mem_forward m1 m1' /\ 
          m1=lst /\ m1'=lst' /\ m=m1 /\ m'=m1' /\ m2=m /\ m2'=m'
 |  j::jss, m::m2::mss, m'::m2'::mss' => mem_unchanged_on (loc_unmapped j) m1 m1' /\
                                 mem_unchanged_on (loc_out_of_reach j m1) m2 m2' /\
                                 mem_forward m1 m1' /\ 
                                 mem_square2 jss m2 (m2::mss) lst m2' (m2'::mss') lst' /\ 
                                 m=m1 /\ m'=m1'
 | _ , _ , _ => False
  end.
       
Lemma mem_square2_mem_forward: 
      forall js m1 ms lst m1' ms' lst', 
      mem_square2 js m1 ms lst m1' ms' lst' -> mem_forward m1 m1'.
  Proof.
    intro js.
    induction js; simpl; intros.
      destruct ms; try contradiction.
      destruct ms; try contradiction. 
      destruct ms; try contradiction. 
      destruct ms'; try contradiction.
      destruct ms'; try contradiction.
      destruct ms'; try contradiction.
      destruct H as [? [? [? [? [? [? ?]]]]]]. subst.  trivial. 
    destruct ms; try contradiction.
      destruct ms; try contradiction.
      destruct ms'; try contradiction.
      destruct ms'; try contradiction.
      destruct H as [_ [_ [X _]]]. trivial.
  Qed. 

  Lemma mem_square2_D: forall J m M lst m' M' lst', 
          mem_square2 J m M lst m' M' lst' ->  
          length M = S(S(length J)) /\ length M' = S(S(length J)) 
          /\ exists t, M=m::t++(lst::nil)
          /\ exists t', M'=m'::t'++(lst'::nil).
   Proof.
     intros J.
     induction J; simpl; intros.
       destruct M; try contradiction.
         destruct M; try contradiction.
         destruct M; try contradiction.
         destruct M'; try contradiction; simpl in *.
         destruct M'; try contradiction.
         destruct M'; try contradiction.
         destruct H as [? [? [? [? [? [? ?]]]]]]. subst.
         split; trivial. split; trivial.
         exists nil; split; trivial.
         exists nil; simpl. trivial.
     destruct M; try contradiction.
       destruct M; try contradiction.
       destruct M'; try contradiction.
       destruct M'; try contradiction.
       destruct H as [? [? [? [? [? ?]]]]]. subst. 
       destruct (IHJ _ _ _ _ _ _ H2) as [? [? [? [? [? ?]]]]].
       simpl in *. inv H5. inv H6. 
       rewrite H3. rewrite H4.
       split; trivial. split; trivial.
       exists (m1::x). split; trivial.
       exists (m3::x0). trivial.
  Qed.


  Lemma mem_square2_l: forall JJ M M' m m' J MM MM' mm mm' lst lst', 
        mem_square2 (J++JJ) m (M++(mm::MM)) lst m' (M'++(mm'::MM')) lst' ->
        S(length J) = length M -> S(length J) = length M' ->
        length JJ = length MM -> length JJ = length MM' ->
        mem_square2 J m (M++(mm::nil)) mm m' (M'++(mm'::nil)) mm'.
    Proof. 
       intros JJ.
       induction JJ; simpl; intros.
          rewrite app_nil_r in H.
          destruct MM; simpl in *; inv H2.  
          destruct MM'; simpl in *; inv H3.
          assert (X:= mem_square2_D _ _ _ _ _ _ _ H). destruct X as [_ [_ [? [? [? ?]]]]].
            assert (X:= app_inj_tail M (m::x) mm lst). simpl in X.  apply X in H2. destruct H2; subst.  clear X.
            assert (X:= app_inj_tail M' (m'::x0) mm' lst'). simpl in X.  apply X in H3. destruct H3; subst.  clear X. 
          simpl in *. apply H.
       destruct M; simpl in *; try congruence. 
          destruct M'; simpl in *; try congruence.
          destruct MM; simpl in *; try congruence. 
          destruct MM'; simpl in *; try congruence.
          destruct J; simpl in *.
             destruct M; simpl in *; try congruence. 
             destruct M'; simpl in *; try congruence.
             destruct H as [? [? [? [? [? ?]]]]]. subst.
             repeat (split; trivial). 
       

   in H2. app_eq_unit in H2.
 exact H. try congruence.
          destruct M; simpl in *; try congruence. 
          destruct M'; simpl in *; try congruence.
          destruct M; simpl in *; try congruence. 
          destruct M'; simpl in *; try congruence.
          destruct JJ; simpl in *.
            destruct MM; simpl in *; try contradiction. 
            destruct MM'; simpl in *; try contradiction.
            destruct H as [? [? [? [? [? [? ?]]]]]]. subst.
            repeat (split; trivial). 
            destruct H as [? [? [? [? [? ?]]]]]. subst.
            destruct JJ; simpl in *. 
            destruct MM; simpl in *; try contradiction.
            destruct MM; simpl in *; try contradiction.  
            destruct MM'; simpl in *; try contradiction.
            destruct MM'; simpl in *; try contradiction. 
            destruct H4 as [? [? [? [? [? [? ?]]]]]]. subst.
            repeat (split; trivial). 
            destruct H as [? [? [? [? [? ?]]]]]. subst.
            destruct JJ; simpl in *. 
            repeat (split; trivial). 
          simpl in *. 
          eapply mem_square_mem_forward; apply H.
        destruct M; simpl in *; try congruence. 
          destruct M'; simpl in *; try congruence.
          inv H0. inv H1.
          destruct H as [UC1 [UC2 [MF MS]]].
          specialize (IHJ _ _ _ _ _ _ _ MS H3 H2); eauto.
    Qed.

  Lemma mem_square2_r: forall J M M' m m' JJ MM MM' j mm mm' lst lst',
        mem_square2 (J++(j::JJ)) m (M++(mm::MM)) lst m' (M'++(mm'::MM')) lst' ->
        length J = length M -> length J = length M' ->
        mem_square2 (j::JJ) mm (mm::MM) lst mm' (mm'::MM') lst'.
    Proof.
       intros J.
       induction J; simpl; intros.
          destruct M; simpl in *; try congruence. 
          destruct MM; simpl in *; try congruence. 
          destruct M'; simpl in *; try congruence.
          destruct MM'; simpl in *; try contradiction.
          destruct H as [UC1 [UC2 [MF [MS [? ?]]]]]. subst.
          split; trivial.
          split; trivial.
          split; trivial.
          split; trivial.
          split; trivial.
        destruct M; simpl in *; try congruence. 
          destruct M'; simpl in *; try congruence.
          remember (M ++ mm :: MM ) as zz. 
          destruct zz; simpl in *. apply eq_sym in Heqzz. apply app_eq_nil in Heqzz.  destruct Heqzz. inv H3.
          remember (M' ++ mm' :: MM') as yy. 
          destruct yy; simpl in *. apply eq_sym in Heqyy. apply app_eq_nil in Heqyy.  destruct Heqyy. inv H3.
          destruct H as [UC1 [UC2 [MF [MS [? ?]]]]]. subst.
          destruct MM; simpl in *. 
          destruct J; simpl in *. simpl in *.
          inv H0. inv H1.
          destruct H as [UC1 [UC2 [MF MS]]].
          apply (IHJ _ _ _ _ _ _ _ _ _ _ _ _ MS H3 H2). 
  Qed.

  Lemma mem_square2_l: forall J M M' m m' JJ MM MM' j mm mm' lst lst', 
        mem_square2 (J++(j::JJ)) m (M++(mm::MM)) lst m' (M'++(mm'::MM')) lst' ->
        S(length J) = length M -> S(length J) = length M' ->
        mem_square2 J m M mm m' M' mm'.
    Proof.
       intros J.
       induction J; simpl; intros.
          destruct M; simpl in *; try congruence. 
          destruct M'; simpl in *; try congruence.
          destruct M; simpl in *; try congruence. 
          destruct M'; simpl in *; try congruence. 
          eapply mem_square_mem_forward; apply H.
        destruct M; simpl in *; try congruence. 
          destruct M'; simpl in *; try congruence.
          inv H0. inv H1.
          destruct H as [UC1 [UC2 [MF MS]]].
          specialize (IHJ _ _ _ _ _ _ _ MS H3 H2); eauto.
    Qed.
*)
  Lemma mem_square_snoc: forall J m1 M m m1' M' m',
          mem_square J m1 (M++(m::nil)) m1' (M'++(m'::nil)) -> forall j lst lst', (*
          mem_unchanged_on (loc_unmapped j) m m' ->
          mem_unchanged_on (loc_out_of_reach j m) m m' -> mem_forward lst lst' ->*)
          mem_square (J ++ (j::nil)) m1 (M ++ (m::lst::nil)) m1' (M' ++ (m'::lst'::nil)).
   Proof. Admitted. (*
     intros J.
     induction J; simpl; intros.
       destruct M; try contradiction.
       destruct M; try contradiction. simpl in *.
       destruct M'; try contradiction; simpl in *.
          destruct H as [? [? [? ?]]].
          split; trivial. split; trivial. simpl. destruct J; simpl in *. split; trivial.
       split; trivial. split; trivial. split; trivial.
     destruct M; try contradiction.
       destruct M'; try contradiction.
       simpl in *. destruct H as [? [? [? ?]]]. 
       destruct M; try contradiction. Focus 2. 
       destruct M'; try contradiction. simpl in *.
       split; trivial. split; trivial. split; trivial.
       
  Lemma mem_square2_snoc: forall J m1 M m m1' M' m',
          mem_square2 J m1 M m m1' M' m' -> forall j lst lst', (*
          mem_unchanged_on (loc_unmapped j) m m' ->
          mem_unchanged_on (loc_out_of_reach j m) m m' -> mem_forward lst lst' ->*)
          mem_square2 (J ++ (j::nil)) m1 (M ++ (m::nil)) lst m1' (M' ++ (m'::nil)) lst'.
   Proof. Admitted. (*
     intros J.
     induction J; simpl; intros.
       destruct M; try contradiction.
       destruct M'; try contradiction.
       simpl in *. destruct H as [? [? ?]]. subst.
       split; trivial. split; trivial. split; trivial.
       split; trivial. split; trivial. split; trivial.
     destruct M; try contradiction.
       destruct M'; try contradiction.
       simpl in *. destruct H as [? [? [? ?]]]. 
       destruct M; try contradiction. Focus 2. 
       destruct M'; try contradiction. simpl in *.
       split; trivial. split; trivial. split; trivial.*)
       *)
       
Fixpoint mkInjections m (n:nat) : list meminj :=
  match n with O => nil
            | S n' => (Mem.flat_inj (Mem.nextblock m))::mkInjections m n'
  end.

Fixpoint lift_join (join:mem -> mem -> mem -> Prop) ms1 ms2 ms :=
  match ms1,ms2,ms with 
     nil, nil, nil => True
   | h1::t1,h2::t2,h::t => join h1 h2 h /\ lift_join join t1 t2 t
   | _ , _ , _ => False
  end.

Inductive Forall3 {A B C : Type} (R : A -> B -> C -> Prop)
            : list A -> list B -> list C -> Prop :=
    Forall3_nil : Forall3 R nil nil nil
  | Forall3_cons : forall (x : A) (y : B) (z:C) (l : list A) (l' : list B) (l'' : list C),
                   R x y z -> Forall3 R l l' l'' -> Forall3 R (x :: l) (y :: l') (z::l'').

  Record Forward_simulation_inject := {
    core_data : Type;
    num_passes : nat; (*gives length of js ms,...*)

    match_state : core_data -> list meminj -> C1 -> mem -> C2 -> mem -> Prop;
   
    match_state_num_passes: forall cd js st1 m1 st2 m2,
        match_state cd js st1 m1 st2 m2 -> length js = num_passes;

    core_ord : core_data -> core_data -> Prop;
    core_ord_wf : well_founded core_ord;

(*Maybe we need an axiom like this?
    thread_axiom: forall cd j m1 c1 m2 c2, match_state cd j c1 m1 c2 m2 ->
             (*we want maybe same sequence of memops to be applied in both forward_modifications*)
               allowed_forward_modifications m1 m1' ->
               allowed_forward_modifications m2 m2' ->
           exists j', incject_incr j j' /\ inject_separated j j' m1 m2
               match_state cd j' c1 m1' c2 m2';
*)

    match_state_siminj :
      forall cd j st1 m1 st2 m2,
        match_state cd j st1 m1 st2 m2 -> siminj (injlist_compose j) m1 m2;

    core_diagram : 
      forall st1 m1 st1' m1', corestep Sem1 ge1 st1 m1 st1' m1' ->
      forall cd st2 j m2,
        match_state cd j st1 m1 st2 m2 ->
        exists st2', exists m2', exists cd', exists j',
          Forall2 inject_incr j j' /\
          inject_separated (injlist_compose j) (injlist_compose j') m1 m2 /\
          match_state cd' j' st1' m1' st2' m2' /\
          ((corestep_plus Sem2 ge2 st2 m2 st2' m2') \/
            corestep_star Sem2 ge2 st2 m2 st2' m2' /\
            core_ord cd' cd);


    core_initial : forall v1 v2 sig,
      In (v1,v2,sig) entry_points ->
        forall vals1 c1 m1,
          make_initial_core Sem1 ge1 v1 vals1 = Some c1 ->
          initial_mem Sem1 ge1 m1 ->
          let js := mkInjections m1 num_passes in
           (*was: let js  map (fun m => Mem.flat_inj (Mem.nextblock m1)) ms in*)
(*          let m2 := last ms m1 in
          let vals2 := last valss vals1 in*)
           (*Lenb: the following two conditions appear to be needed for composition inj_inj*)
           (*Mem.inject (Mem.flat_inj (Mem.nextblock m2)) m2 m2 ->
           F orall2 (val_inject (Mem.flat_inj (Mem.nextblock m2))) vals' vals' ->*)

          (*check_valslist js vals1 valss ->
          Forall2 (Val.has_type) vals2 (sig_args sig) ->*)
          (*check_injectlist js m1 ms ->*)
(*          Forall2 (Val.has_type) vals1 (sig_args sig) ->*)
          exists cd, exists c2, exists vals2, exists m2, 
            make_initial_core Sem2 ge2 v2 vals2 = Some c2 /\
            initial_mem Sem2 ge2 m2 /\
            match_state cd js c1 m1 c2 m2;


(* Attempt to specify forking, parametric in some join relation. It'll be up to the concurrency machine 
to decide hoe memory is split - here we just assume ther are splits for all num_passes memories.
Also, we probably want to allow forking only at (exactly at?) at_external points, and also
add fiuther hypotheses that allows us to carry on in both threads without waiting for after-external,
ie we probably want to add mem_square and some toher hypotheses from after_external somewhere here*)
 (*
    core_at_fork : forall (join:mem -> mem -> mem -> Prop) v1 v2 sig,
      In (v1,v2,sig) entry_points ->
        forall vals1 vals2 (m1:mem) js ms m1l m1r m2l m2r msl msr cd c1 c2 c1',
          let m2 := last ms m1 in
          let m2l := last msl m1l in
          let m2r := last msr m1r in

            match_state cd js c1 m1 c2 m2 ->
            join m1l m1r m1 ->
            Forall3 (lift_join join) msl msr ms ->
           (*Lenb: the following two conditions appear to be needed for composition inj_inj*)
           (*Mem.inject (Mem.flat_inj (Mem.nextblock m2)) m2 m2 ->
           Forall2 (val_inject (Mem.flat_inj (Mem.nextblock m2))) vals' vals' ->*)

          Forall2 (val_inject js) vals1 vals2 ->
          Forall2 (Val.has_type) vals2 (sig_args sig) ->
          make_initial_core Sem1 ge1 v1 vals1 = Some c1' ->
          exists cd', exists c2', 
            make_initial_core Sem2 ge2 v2 vals2 = Some c2' /\
            match_state cd js c1 m1l c2 m2l /\
            match_state cd' js c1' m1r c2' m2r;
*)
    core_halted : forall cd js c1 m1 c2 m2 (v1:int),
      match_state cd js c1 m1 c2 m2 ->
      safely_halted Sem1 ge1 c1 = Some v1 ->
        (safely_halted Sem2 ge2 c2 = Some v1 /\
         exists ms, check_injectlist js m1 ms m2);
(*
    core_at_externalLenbAteempt : 
      forall cd js st1 m1 st2 m2 e vals1,
        match_state cd js st1 m1 st2 m2 ->
        at_external Sem1 st1 = Some (e,vals1) ->
        (Mem.inject (injlist_compose js) m1 m2 /\
          exists vals2, Forall2 (val_inject (injlist_compose js)) vals1 vals2 /\
          Forall2 (Val.has_type) vals2 (sig_args (ef_sig e)) /\
          at_external Sem2 st2 = Some (e,vals2));
*)
    core_at_external : 
      forall cd js st1 m1 st2 m2 e vals1,
        match_state cd js st1 m1 st2 m2 ->
        at_external Sem1 st1 = Some (e,vals1) ->
        exists ms, check_injectlist js m1 ms m2 /\
          exists vals2, Forall2 (val_inject (injlist_compose js)) vals1 vals2 /\
          Forall2 (Val.has_type) vals2 (sig_args (ef_sig e)) /\
          at_external Sem2 st2 = Some (e,vals2);
  (*
    (core_after_externalForwardSimulation.v :
      forall cd j j' st1 st2 m1 m2 e1 e2 vals vals' ret ret' m1' m2' sig,
        match_state cd j st1 m1 st2 m2 ->
        Mem.inject j m1 m2 ->
        at_external Sem1 st1 = Some (e1,sig,vals) ->
        at_external Sem2 st2 = Some (e2,sig,vals') ->
        match_ext sig e1 e2 ->
        Forall2 (val_inject j) vals vals' ->
      
        inject_incr j j' ->
        inject_separated j j' m1 m2 ->
        Mem.inject j' m1' m2' ->
        val_inject j' ret ret' ->

        mem_unchanged_on (loc_unmapped j) m1 m1' ->
        mem_unchanged_on (loc_out_of_reach j m1) m2 m2' ->
        mem_forward m1 m1' ->
        mem_forward m2 m2' ->

        Forall2 (Val.has_type) vals' (sig_args sig) ->
        Val.has_type ret' (proj_sig_res sig) ->

        exists cd', exists st1', exists st2',
          after_external Sem1 (ret::nil) st1 = Some st1' /\
          after_external Sem2 (ret'::nil) st2 = Some st2' /\
          match_state cd' j' st1' m1' st2' m2'),*)

    core_after_external :
      forall cd js js' st1 st2 m1 ms e vals1 (*vals2*) ret1 rets m1' ms' m2 m2' ret2,
        check_injectlist js m1 ms m2->
        match_state cd js st1 m1 st2 m2 ->
        at_external Sem1 st1 = Some (e,vals1) ->
(*        Mem.inject j m1 m2 ->
        at_external Sem2 st2 = Some (e,vals2) ->
        Forall2 (val_inject j) vals1 vals2 ->*)
      
        Forall2 inject_incr js js' ->
        inject_separated (injlist_compose js) (injlist_compose js') m1 m2 ->
        check_injectlist js' m1' ms' m2' ->
        check_returns js' ret1 rets ret2 ->

         mem_square js m1 ms m1' ms' ->
        (*mem_square2 js m1 ms m2 m1' ms' m2' ->*)

        Val.has_type ret2 (proj_sig_res (ef_sig e)) ->

        exists cd', exists st1', exists st2',
          after_external Sem1 ret1 st1 = Some st1' /\
          after_external Sem2 ret2 st2 = Some st2' /\
          match_state cd' js' st1' m1' st2' m2'

    }.

  Record Forward_simulation_inject_onepass := {
    core_dataOP : Type;

    match_stateOP : core_dataOP -> meminj -> C1 -> mem -> C2 -> mem -> Prop;
    core_ordOP : core_dataOP -> core_dataOP -> Prop;
    core_ord_wfOP : well_founded core_ordOP;

(*Maybe we need an axiom like this?
    thread_axiom: forall cd j m1 c1 m2 c2, match_state cd j c1 m1 c2 m2 ->
             (*we want maybe same sequence of memops to be applied in both forward_modifications*)
               allowed_forward_modifications m1 m1' ->
               allowed_forward_modifications m2 m2' ->
           exists j', incject_incr j j' /\ inject_separated j j' m1 m2
               match_state cd j' c1 m1' c2 m2';
*)

    match_state_siminjOP :
      forall cd j st1 m1 st2 m2,
        match_stateOP cd j st1 m1 st2 m2 -> siminj j m1 m2;

    core_diagramOP : 
      forall st1 m1 st1' m1', corestep Sem1 ge1 st1 m1 st1' m1' ->
      forall cd st2 j m2,
        match_stateOP cd j st1 m1 st2 m2 ->
        exists st2', exists m2', exists cd', exists j',
          inject_incr j j' /\
          inject_separated j j' m1 m2 /\
          match_stateOP cd' j' st1' m1' st2' m2' /\
          ((corestep_plus Sem2 ge2 st2 m2 st2' m2') \/
            corestep_star Sem2 ge2 st2 m2 st2' m2' /\
            core_ordOP cd' cd);

    core_initialOP : forall v1 v2 sig,
      In (v1,v2,sig) entry_points ->
        forall vals vals' m1 m2,
          let j := (Mem.flat_inj (Mem.nextblock m1)) in

           (*Lenb: the following two conditions appear to be needed for composition inj_inj*)
           Mem.inject (Mem.flat_inj (Mem.nextblock m2)) m2 m2 ->
           Forall2 (val_inject (Mem.flat_inj (Mem.nextblock m2))) vals' vals' ->

          Forall2 (val_inject j) vals vals' ->
          Forall2 (Val.has_type) vals' (sig_args sig) ->
          Mem.inject j m1 m2 ->
          exists cd, exists c1, exists c2,
            make_initial_core Sem1 ge1 v1 vals = Some c1 /\
            make_initial_core Sem2 ge2 v2 vals' = Some c2 /\
            match_stateOP cd j c1 m1 c2 m2;

(* Attempt to specify forking, but we're giving away the entire memory here which can't be right.
  We may later want to reintroduce this lemma, but somehow allow one to specify which part of
the memory is retained, and which one is given to the thread.
    core_at_fork : forall v1 v2 sig,
      In (v1,v2,sig) entry_points ->
        forall vals vals' m1 m2 j
          (HM: match_state cd j c1 m1 c2 m2),

           (*Lenb: the following two conditions appear to be needed for composition inj_inj*)
           (*Mem.inject (Mem.flat_inj (Mem.nextblock m2)) m2 m2 ->
           Forall2 (val_inject (Mem.flat_inj (Mem.nextblock m2))) vals' vals' ->*)

          Forall2 (val_inject j) vals vals' ->
          Forall2 (Val.has_type) vals' (sig_args sig) ->
          Mem.inject j m1 m2 ->
          exists cd', exists c1', exists c2',
            make_initial_core Sem1 ge1 v1 vals = Some c1' /\
            make_initial_core Sem2 ge2 v2 vals' = Some c2' /\
            match_state cd' j c1' m1 c2' m2;*)

    core_haltedOP : forall cd j c1 m1 c2 m2 (v1:int),
      match_stateOP cd j c1 m1 c2 m2 ->
      safely_halted Sem1 ge1 c1 = Some v1 ->
        (safely_halted Sem2 ge2 c2 = Some v1 /\
         Mem.inject j m1 m2); (*conjunct Mem.inject j m1 m2 could maybe deleted here?*)

    core_at_externalOP: 
      forall cd j st1 m1 st2 m2 e vals1,
        match_stateOP cd j st1 m1 st2 m2 ->
        at_external Sem1 st1 = Some (e,vals1) ->
        exists vals2,
          Mem.inject j m1 m2 /\
          Forall2 (val_inject j) vals1 vals2 /\
          Forall2 (Val.has_type) vals2 (sig_args (ef_sig e)) /\
          at_external Sem2 st2 = Some (e,vals2);
  
    core_after_externalOP :
      forall cd j j' st1 st2 m1 m2 e vals1 vals2 ret1 ret2 m1' m2',
        match_stateOP cd j st1 m1 st2 m2 ->
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
          match_stateOP cd' j' st1' m1' st2' m2'
    }.

  Axiom OnePassSpecialization: Forward_simulation_inject_onepass -> Forward_simulation_inject.

End Forward_simulation_inject.

Implicit Arguments Forward_simulation_inject[[G1] [C1] [G2] [C2]].
End Sim_inj.
Lemma corestepN_allowed_modifications:
  forall {G C : Type}{Sem : CompcertCoreSem G C} {ge n c m c' m'}
      (HC: corestepN Sem ge n c m c' m'),  allowed_core_modification m m'.
  Proof.
  intros until n.
  induction n; simpl; intros.
    inv HC. apply allowed_core_modification_refl.
  destruct HC as [c'' [m'' [Step StepN]]].
    eapply allowed_core_modification_trans.
      apply (csem_allowed_modifications _ _ _ _ _ _ Step).
      eauto.
  Qed.

Lemma corestep_plus_allowed_modifications:
  forall {G C : Type}{Sem : CompcertCoreSem G C} {ge c m c' m'} 
      (HC: corestep_plus Sem ge c m c' m'),  allowed_core_modification m m'.
  Proof.
  intros. destruct HC as [n Hn]. eapply corestepN_allowed_modifications. apply Hn.
  Qed.
  
Lemma corestep_star_allowed_modifications:
  forall {G C : Type}{Sem : CompcertCoreSem G C} {ge c m c' m'} 
      (HC: corestep_star Sem ge c m c' m'),  allowed_core_modification m m'.
  Proof.
  intros. destruct HC as [n Hn]. eapply corestepN_allowed_modifications. apply Hn.
  Qed.

Notation inj_compose := Mem.meminj_compose.

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

Lemma siminj_compose j j' m1 m2 m3:
    siminj j m1 m2 -> siminj j' m2 m3 -> siminj (inj_compose j j') m1 m3.
  Proof.
    unfold inj_compose, siminj. intros [H1 H2][H3 H4].
    split. 
    (*Claim1*)
      intros.
      case_eq (j b).
      (*j b = Some p*)
         intros [b' z] eq.
         case_eq (j' b').
         (*j' b' = Some p'*)
            intros [b2 z2] eq2.
            specialize (H1 _ H). congruence.
         (*j' b' = None*) auto.
      (*j b = None*) auto.
    (*Claim2*)
      intros until delta.
      case_eq (j b). 
      (*j b = Some p*)
         intros [b2 z2] eq2.
         case_eq (j' b2).
         (*j' b2 = Some p'*)
            intros [b3 z3] eq3.
            inversion 1; subst. eapply H4; eauto.
         (*j' b2 = None*)
            intros ?; inversion 1.
      (*j b = None*)
         congruence.
  Qed.

  Lemma inj_compose_neutral: forall j, inj_compose (fun b : block => Some (b, 0)) j = j.
    Proof.
      intros.
      extensionality b. unfold inj_compose; simpl. case (j b); eauto. destruct p; eauto.
    Qed.      
 
  Lemma inj_compose_assoc: 
        forall j1 j2 j3, inj_compose j1 (inj_compose j2 j3) = inj_compose (inj_compose j1 j2) j3.
    Proof.
      unfold inj_compose; simpl; intros.
      extensionality b.
      case (j1 b); trivial. destruct p. 
      case (j2 b0); trivial. destruct p. 
      case (j3 b1); trivial. destruct p. rewrite Zplus_assoc. trivial.
    Qed. 
  
  Lemma injlist_compose_app: forall js1 js2,
        injlist_compose (js1 ++ js2) = inj_compose (injlist_compose js1) (injlist_compose js2).
    Proof.
      intros js1.
      induction js1; simpl; intros.
        rewrite inj_compose_neutral. trivial.
      rewrite IHjs1. clear IHjs1. apply inj_compose_assoc.
    Qed.
  
  Lemma siminj_list_compose: 
        forall js1 m1 m2 (Sim1: siminj (injlist_compose js1) m1 m2)
               js2 m3 (Sim2 : siminj (injlist_compose js2) m2 m3),
        siminj (injlist_compose (js1 ++ js2)) m1 m3.
  Proof.
    intros. assert (Sim := siminj_compose _ _ _ _ _ Sim1 Sim2). clear Sim1 Sim2.
    rewrite injlist_compose_app. apply Sim.
  Qed.

  Lemma inject_incr_compose: forall {J1 J1' J2 J2'}
        (HJ1: Forall2 inject_incr J1 J1') (HJ2: Forall2 inject_incr J2 J2'),
        Forall2 inject_incr (J1 ++ J2) (J1' ++ J2').
  Proof.
    intros.
    induction HJ1; simpl. apply HJ2.
    eapply Forall2_cons; assumption. 
  Qed.

  Lemma inject_incr_list_refl: forall J, Forall2 inject_incr J J.
  Proof.
    intros.
    induction J; intros. constructor. constructor; trivial.
  Qed.

  Lemma injlist_compose_inj_incr: forall J J',
       Forall2 inject_incr J J' -> 
       inject_incr (injlist_compose J) (injlist_compose J').
  Proof.
    intros.
    induction H; intros; simpl in *.
      apply inject_incr_refl.
    rename x into j. rename y into j'. 
      intros b; intros.
      apply inj_compose_SomeD in H1.
      destruct H1 as [b1 [delta1 [delta2 [Jb [Hb1 HD]]]]]; subst.
      apply H in Jb. apply IHForall2 in Hb1.
      unfold inj_compose. rewrite Jb. rewrite Hb1. trivial.
  Qed.

  Lemma injlist_incr_trans: 
      forall J1 J2 (H12: Forall2 inject_incr J1 J2)
             J3 (H23: Forall2 inject_incr J2 J3),
      Forall2 inject_incr J1 J3.
  Proof.
    intros J1 J2 H12. 
    induction H12; intros; inv H23; try econstructor; trivial.
      eapply inject_incr_trans; eauto. eauto.
  Qed.

  Lemma inject_separated_injlist_compose: forall {J1 J1' J2 J2' m1 m2 m3}
        (HII1: Forall2 inject_incr J1 J1')
        (HII2: Forall2 inject_incr J2 J2')
        (Inj1B : forall (b b' : block) (delta : Z),
                 injlist_compose J1 b = Some (b', delta) -> Mem.valid_block m2 b')
        (Inj2A : forall b : block,
                 ~ Mem.valid_block m2 b -> injlist_compose J2 b = None)
        (Hsep1: inject_separated (injlist_compose J1) (injlist_compose J1') m1 m2)
        (Hsep2: inject_separated (injlist_compose J2) (injlist_compose J2') m2 m3),
    inject_separated (injlist_compose (J1 ++ J2)) (injlist_compose  (J1' ++ J2')) m1 m3.
  Proof.
    intros. intros b1 b3 delta HJ1 HJ1'.
    rewrite injlist_compose_app in HJ1'.
    apply inj_compose_SomeD in HJ1'. destruct HJ1' as [b2 [delta2 [delta3 [HJ1' [HJ2' HD]]]]].
    rewrite injlist_compose_app in HJ1.
    apply inj_compose_NoneD in HJ1.
    destruct HJ1.
    (*J1 b1 = None*)
       destruct (Hsep1 _ _ _ H HJ1'); clear Hsep1.
       split; try assumption.
       assert (Y2 := Inj2A _ H1).
       apply (Hsep2 _ _ _ Y2 HJ2').
    (*j1 b1 = Some (b', delta')*)
       destruct H as [b' [delta' [H1b' H2b']]]. subst.
       apply injlist_compose_inj_incr in HII1.
       assert (ZZ := HII1 _ _ _ H1b'). rewrite HJ1' in ZZ. inversion ZZ; subst; clear ZZ.
       destruct (Hsep2 _ _ _ H2b' HJ2'); clear Hsep2.
       split; try assumption.
       intros ZZ.
       apply H.
       apply (Inj1B _ _ _ H1b').
  Qed.

  Lemma lex_ord_clos_trans_left: forall {A B:Type} R d d' 
          (Ord : clos_trans A R d d') T e e',
          clos_trans (A * B) (lex_ord R T) (d, e) (d', e').
  Proof.
    intros A B R d d' Ord.
    induction Ord; intros.
      apply t_step. apply lex_ord_left. apply H.
    apply t_trans with (y:=(y,e')). apply IHOrd1. apply IHOrd2.
  Qed. 

  Lemma inject_separated_incrs: forall j j' jj m1 m1' m2 m2'
       (Sep: inject_separated j j' m1 m2)
       (Sep': inject_separated j' jj m1' m2')
       (Incr: inject_incr j' jj)
       (AM1: allowed_core_modification m1 m1')
       (AM2: allowed_core_modification m2 m2'),
       inject_separated j jj m1 m2.
  Proof.
    unfold inject_separated; intros.
    remember (j' b1) as jb.
    destruct jb; apply eq_sym in Heqjb.
    (*Some p*)
        destruct p as [bb ddelta].
        rewrite (Incr _ _ _ Heqjb) in H0. inv H0.
        apply (Sep _ _ _ H Heqjb).
    (*None*)
        destruct (Sep' _ _ _ Heqjb H0) as [K1 K2].
        split; intros QQ.
          apply K1. apply AM1. apply QQ.
          apply K2. apply AM2. apply QQ.
  Qed.

  Lemma InjInj_core_diagram_AUX: forall {G2 C2 G3 C3} {Sem2 : CompcertCoreSem G2 C2} {Sem3 : CompcertCoreSem G3 C3} 
                     {ge2: G2} {ge3 : G3} {entry_points23 : list (val*val*signature)}
                     {FSim23 : Sim_inj.Forward_simulation_inject Sem2 Sem3 ge2 ge3 entry_points23}
       N st2 m2 st2' m2'
       (Hyp: corestepN Sem2 ge2 (S N) st2 m2 st2' m2')
       d23 J st3 m3
       (MS23:Sim_inj.match_state FSim23 d23 J st2 m2 st3 m3),
       exists st3', exists m3', exists d', exists J', 
            allowed_core_modification m3 m3' /\
            Forall2 inject_incr J J' /\ inject_separated (injlist_compose J) (injlist_compose J') m2 m3 /\ 
            Sim_inj.match_state FSim23 d' J' st2' m2' st3' m3' /\
            (corestep_plus Sem3 ge3 st3 m3 st3' m3' \/
               corestep_star Sem3 ge3 st3 m3 st3' m3' /\
               clos_trans _ (Sim_inj.core_ord FSim23) d' d23).
  Proof. 
    intros until N.
    induction N; intros.
    (*Base*)
      simpl in Hyp.
      destruct Hyp as [st3' [m3' [Step StatesEQ]]].
      inv StatesEQ.
      (*      assert (ACM:= csem_allowed_modifications _ _ _ _ _ _ Step).*)
      assert (CD:= Sim_inj.core_diagram FSim23 st2 m2 st2' m2' Step d23 st3 J m3 MS23).
      destruct CD as [st3' [m3' [d' [J' [Inc3 [Sep3 [MS3 EX3]]]]]]].
      exists st3'. exists m3'. exists d'. exists J'.
      split. destruct EX3 as [Hplus | [Hstar _]].
        eapply (corestep_plus_allowed_modifications Hplus).
        eapply (corestep_star_allowed_modifications Hstar).
      split; trivial.
      split; trivial.
      split; trivial.
      destruct EX3 as [Hplus | [Hstar Hord]].
        left; trivial.
        right; split; trivial. apply (t_step _ _ _ _ Hord).  
    (*Step*)
      remember (S N) as x. simpl in Hyp.
      destruct Hyp as [st2'' [m2'' [Step StepN]]]. subst x.
      destruct (Sim_inj.core_diagram FSim23
        st2 m2 st2'' m2'' Step _ _ _ _ MS23) as [st3'' [m3'' [d'' [J2'' [Incr2 [Sep23 [MS23'' ?]]]]]]].
      specialize (IHN st2'' m2'' st2' m2' StepN _ _ _ _ MS23'').
      destruct IHN as [st3' [m3' [dd [JJ [AM' [INCR [SEP [MS HH]]]]]]]].
      exists st3'. exists m3'. exists dd. exists JJ.
         assert (AM'': allowed_core_modification m3 m3'').
                destruct H as [Hplus | [Hstar _]].
                eapply (corestep_plus_allowed_modifications Hplus).
                eapply (corestep_star_allowed_modifications Hstar).
         assert (AM: allowed_core_modification m3 m3').
                apply allowed_core_modification_trans with (m2:=m3''); trivial.
         split; trivial. 
         split. eapply injlist_incr_trans. apply Incr2. apply INCR.
         split. eapply inject_separated_incrs. apply Sep23. apply SEP. eapply injlist_compose_inj_incr. apply INCR. 
                   apply (csem_allowed_modifications _ _ _ _ _ _ Step).
                   apply AM''.
         split. apply MS.
         destruct H as [HPlus | [HStar Hord]]; destruct HH as [HHPlus | [HHStar HHord]].
         (*Plus Plus*)
            left. destruct HPlus as [n1 ?]. destruct HHPlus as [n2 ?].
            exists (n1 + S n2)%nat.
            change (S (n1 + S n2)) with (S n1 + S n2)%nat.
            rewrite corestepN_add. eauto.
         (*Plus Star*)
            left. destruct HPlus as [n1 ?]. destruct HHStar as [n2 ?].
            exists (n1 + n2)%nat.
            change (S (n1 + n2)) with (S n1 + n2)%nat.
            rewrite corestepN_add. eauto.
         (*Star Plus*)
            left. destruct HStar as [n1 ?]. destruct HHPlus as [n2 ?].
             exists (n1 + n2)%nat.
             replace (S (n1 + n2)) with (n1 + S n2)%nat by omega.
             rewrite corestepN_add. eauto.
         (*Star Star*)
             right. split.
                destruct HStar as [n1 ?]. destruct HHStar as [n2 ?].
                exists (n1 + n2)%nat.
                rewrite corestepN_add. eauto.
             eapply t_trans. apply HHord. apply (t_step _ _ _ _ Hord).
  Qed.

Lemma check_injectlist_DTail: forall J M m m2 (Inj : Sim_inj.check_injectlist J m M m2),
      (J = nil /\ M = nil /\ m = m2) \/
      (exists JJ, exists j, exists MM, 
            J = JJ ++ (j:: nil) /\ M = MM ++ (m2::nil)).
  Proof.
    intros J.
    induction J; intro M.
      destruct M; simpl; intros; try contradiction.
        left; auto.
    destruct M; simpl; intros; try contradiction.
      right.
      destruct Inj.
      destruct (IHJ _ _ _ H0); clear IHJ.
         destruct H1 as [? [? ?]]. subst. simpl in *.
         exists nil. exists a. exists nil. simpl. auto. 
      destruct H1 as [? [? [? [? ?]]]]. subst.
         exists (a::x). exists x0. exists (m::x1). simpl.
         split; trivial. (*split; trivial. 
         remember (x1 ++ x2 :: nil) as zz. destruct zz; apply eq_sym in Heqzz. apply app_eq_nil in Heqzz. destruct Heqzz; subst.  congruence. 
           rewrite <- Heqzz. apply app_last.                   *)
  Qed.      

Lemma check_injectlist_app: 
      forall ms1 js1 m1 m2 (Inj1 : Sim_inj.check_injectlist js1 m1 ms1 m2)
             ms2 js2 m3 (Inj2 : Sim_inj.check_injectlist js2 m2 ms2 m3),
                 Sim_inj.check_injectlist (js1 ++ js2) m1 (ms1++ms2) m3.
  Proof.
    intros ms1.
    induction ms1; intros.
       destruct js1; simpl in *. subst. trivial.
       contradiction.
    destruct js1; simpl in *. contradiction.
       destruct Inj1. split; trivial.
       eapply IHms1. apply H0. apply Inj2.
  Qed.
(*
Lemma check_injectlist_app1: 
      forall m1 js1 ms1 m2 (Inj1 : Sim_inj.check_injectlist js1 m1 ms1 m2)
             js2 ms2 m3 (Inj2 : Sim_inj.check_injectlist js2 m2 ms2 m3),
      exists ms,
         last ms2 (last ms1 m1) = last ms m1 /\
         Sim_inj.check_injectlist (js1 ++ js2) m1 ms.
  Proof. 
    intros.
    assert (YY:= check_injectlist_DTail _ _ _ Inj1).
              destruct YY as [[? [? ?]] | [? [? [? [? [? [? ?]]]]]]].
                 rewrite H in *. rewrite H0 in *. simpl in *.  subst. 
                 exists ms2. auto.
              rewrite H in *. rewrite H0 in *. clear H1. subst.
              assert (Eq : (x ++ x0 :: nil) ++ js2 = x ++ x0 :: js2).
                 assert (x0 :: nil = (x0 :: nil) ++ nil). trivial. rewrite H.
                 rewrite <- app_assoc. f_equal.
              rewrite Eq. clear Eq.
              rewrite app_last in Inj2. 
              assert (ZZ:= check_injectlist_app _ _ _ _ Inj1 _ _ Inj2).
              exists (x1 ++ x2 :: ms2 ). split; try assumption. rewrite app_last.
                 apply app_last2.
              assert (Qq: x ++ x0 :: js2 = (x ++ x0 :: nil) ++ js2).
                rewrite <- app_assoc. f_equal.
              rewrite Qq. apply ZZ.
     Qed.
*)
Lemma check_injectlist_split: 
      forall js1 js2 ms m m2 (HCI: Sim_inj.check_injectlist (js1 ++ js2) m ms m2),
      exists ms1, exists ms2, exists mm, ms = ms1 ++ ms2 /\
        Sim_inj.check_injectlist js1 m ms1 mm /\
        Sim_inj.check_injectlist js2 mm ms2 m2.
  Proof.
    intros js1.
    induction js1; simpl; intros. exists nil. exists ms. exists m; auto.
    destruct ms; try contradiction. destruct HCI.
      destruct (IHjs1 _ _ _ _ H0) as [ms1 [ms2 [mm [M [M1 M2]]]]]; clear IHjs1; subst; simpl in *.
        exists (m0::ms1); simpl. exists ms2; simpl. exists mm. auto.
  Qed.

  Lemma check_returns_split: 
      forall js1 js2 ms m m2 (HCI: Sim_inj.check_returns (js1 ++ js2) m ms m2),
      exists ms1, exists ms2, exists mm, ms = ms1 ++ ms2 /\
        Sim_inj.check_returns js1 m ms1 mm /\
        Sim_inj.check_returns js2 mm ms2 m2.
  Proof.
    intros js1.
    induction js1; simpl; intros. exists nil. exists ms. exists m; auto.
    destruct ms; try contradiction. destruct HCI.
      destruct (IHjs1 _ _ _ _ H0) as [ms1 [ms2 [mm [M [M1 M2]]]]]; clear IHjs1; subst; simpl in *.
        exists (v::ms1); simpl. exists ms2; simpl. exists mm. auto.
  Qed.

  Lemma vals_inject_compose: 
        forall vals1 j1 vals2 (ValsInj1 : Forall2 (val_inject j1) vals1 vals2)
               vals3 j2 (ValsInj2 : Forall2 (val_inject j2) vals2 vals3),
        Forall2 (val_inject (inj_compose j1 j2)) vals1 vals3.
    Proof.
      intros vals1.
      induction vals1; intros; subst.
      (*nil*)
         inv ValsInj1.
         inv ValsInj2.
         constructor.
      (*cons*)
         inv ValsInj1.
         inv ValsInj2.
         constructor; eauto. 
           apply (Mem.val_inject_compose _ _ _ _ _ H1 H2).
    Qed.

  Lemma injlist_incr_split: 
      forall js' js1 js2 (Incr : Forall2 inject_incr (js1 ++ js2) js'),
      exists js1', exists js2', js' = js1' ++ js2' /\ 
                   Forall2 inject_incr js1 js1' /\ Forall2 inject_incr js2 js2'.
  Proof.
    intros js'.
    induction js'; simpl; intros.
      inv Incr. apply eq_sym in H0. apply app_eq_nil in H0. destruct H0. subst.
        exists nil. exists nil. simpl. auto. 
    destruct js1; simpl in *.
      inv Incr. exists nil. exists (a::js'). simpl. auto. 
    inv Incr.
      destruct (IHjs' _ _ H4) as [js1' [js2' [XX [Inc Incs]]]]. subst. clear IHjs'.
      exists (a::js1'). exists js2'. auto.
  Qed.

  Lemma val_inject_has_type: 
      forall j w v (I : val_inject j w v) T (HT : Val.has_type v T), Val.has_type w T.
  Proof.
    intros j w v I.
    induction I; simpl in *; intros; trivial.
  Qed.

  Lemma check_returns_DTail: forall J M m m2 (Inj : Sim_inj.check_returns J m M m2),
      (J = nil /\ M = nil /\ m = m2) \/
      (exists JJ, exists j, exists MM, 
            J = JJ ++ (j:: nil) /\ M = MM ++ (m2::nil)).
  Proof.
    intros J.
    induction J; intro M.
      destruct M; simpl; intros; try contradiction.
        left; auto.
    destruct M; simpl; intros; try contradiction.
      right.
      destruct Inj.
      destruct (IHJ _ _ _ H0); clear IHJ.
         destruct H1 as [? [? ?]]. subst. simpl in *.
         exists nil. exists a. exists nil. simpl. auto. 
      destruct H1 as [? [? [? [? ?]]]]. subst.
         exists (a::x). exists x0. exists (v::x1). simpl.
         split; trivial. (*split; trivial. 
         remember (x1 ++ x2 :: nil) as zz. destruct zz; apply eq_sym in Heqzz. apply app_eq_nil in Heqzz. destruct Heqzz; subst.  congruence. 
           rewrite <- Heqzz. apply app_last.                   *)
  Qed.   
  
  Lemma check_returns_types:
      forall t R w r
       (T : Val.has_type r t) J (CR: Sim_inj.check_returns J w R r),
       Val.has_type w t.
  Proof. intros.
    assert (XX:= check_returns_DTail _ _ _ _ CR).
    destruct XX. destruct H as [? [? ?]]. subst. trivial.
    destruct H as [JJ [j [MM [? ?]]]]. subst.
    generalize dependent MM. generalize dependent w.
    induction JJ; simpl; intros.
       remember (MM ++ r :: nil) as z. destruct z. contradiction.
       destruct CR. destruct z; try contradiction.
       subst. destruct MM; simpl in *; inv Heqz. eapply val_inject_has_type; eauto.
           apply eq_sym in H2. apply app_eq_nil in H2. destruct H2. congruence.
     remember (MM ++ r :: nil) as z. destruct z; try contradiction.
       destruct CR.
       destruct z. 
          remember (JJ ++ j :: nil) as q. destruct q. apply eq_sym in Heqq. apply app_eq_nil in Heqq. destruct Heqq. congruence.
            simpl in H0. contradiction.
         destruct MM; simpl in *; inv Heqz. rewrite H3 in H0.
         specialize (IHJJ _ _ H0). eapply val_inject_has_type; eauto.
  Qed.

  Lemma inject_compose_app: 
      forall J1 m1 m2 (HJ1: Mem.inject (injlist_compose J1) m1 m2)
             J2 m3 (HJ2: Mem.inject (injlist_compose J2) m2 m3),
      Mem.inject (injlist_compose (J1 ++ J2)) m1 m3.
  Proof.
    intros. rewrite injlist_compose_app.
    eapply Mem.inject_compose; eauto. 
  Qed.

  Lemma Forall2_length: 
        forall {A B:Type} (R:A -> B -> Prop) J J', 
               Forall2 R J J' -> length J' = length J.
    Proof.
      intros.
       induction H; simpl; eauto.
    Qed.

  Lemma check_injectlist_inject: 
        forall J M m mm (CI: Sim_inj.check_injectlist J m M mm),
        (J=nil /\ M = nil /\ m=mm) \/
        (J <> nil /\ Mem.inject (injlist_compose J) m mm).
   Proof.
     intros J.
     induction J; intros; destruct M; simpl in *; try contradiction. subst. left; auto.
     destruct CI. right. split; try congruence.
       specialize (IHJ _ _ _ H0).
       destruct IHJ.
          destruct H1 as [? [? ?]]. subst; simpl in *.
          assert (inj_compose a (fun b : block => Some (b, 0)) = a).
            unfold inj_compose. extensionality b.
            remember (a b) as z; destruct z; auto. destruct p. rewrite Zplus_0_r. trivial.
          rewrite H1. trivial.
       destruct H1. eapply Mem.inject_compose; eauto.
  Qed.


  Lemma memval_dec: forall (x y:memval), (x=y) + {x <> y}.
    intros.
    destruct x; destruct y.
       left; trivial. right; discriminate. right; discriminate.
       right; discriminate. 
          remember (Byte.eq_dec i i0). destruct s. left; congruence. right. congruence.
          right; discriminate.
       right; discriminate. right; discriminate.
          remember (eq_block b b0) as z1. destruct z1; subst; try (right; congruence).
          remember (Int.eq_dec i i0) as z2. destruct z2; subst; try (right; congruence).
          remember (beq_nat n n0) as z. destruct z; subst.
                   apply beq_nat_eq in Heqz; subst. left; trivial.
                   apply eq_sym in Heqz. apply beq_nat_false in Heqz. right; congruence.
      Qed.

  Lemma inject_separated_refl: forall f m m',
       inject_separated f f m m'.
   Proof. intros f m m' b; intros. rewrite H in H0. inv H0. Qed.
(*
  Lemma inj_separated_tail: forall J j j' J' m1 m m3,
        inject_separated (inj_compose j (injlist_compose J)) 
                         (inj_compose j' (injlist_compose J')) m1 m3 -> 
        Mem.inject j m1 m -> Forall2 inject_incr J J' ->
        inject_separated (injlist_compose J) (injlist_compose J') m m3.
   Proof. intros J.
     induction J; simpl; intros.
       inv H1. simpl. apply inject_separated_refl.
     intros b; intros. unfold inject_separated, inj_compose in H.
     specialize (H 
     remember () as z.

  Lemma inject_separated_split:
        forall js1 ms1 m1 m2    (CIL1 : Sim_inj.check_injectlist js1 m1 ms1 m2)
               js2 ms2 m3 (CIL2 : Sim_inj.check_injectlist js2 m2 ms2 m3)
               js1' js2' 
               (Sep13 : inject_separated (injlist_compose (js1 ++ js2))
                                        (injlist_compose (js1' ++ js2')) m1 m3)
               (Incr1 : Forall2 inject_incr js1 js1')
               (Incr2: Forall2 inject_incr js2 js2'),
        inject_separated (injlist_compose js1) (injlist_compose js1') m1 m2.
  Proof. intros js1.
    induction js1; simpl; intros.
       destruct ms1; try contradiction. subst. inv Incr1. simpl in Sep13. simpl.
       apply inject_separated_refl.
    destruct ms1; try contradiction.
    inv Incr1. rename a into j. rename y into j'. rename l' into js1'.
    destruct CIL1 as [CIL1a CIL1b].
    specialize (IHjs1 _ _ _ CIL1b _ _ _ CIL2).
    simpl in Sep13.
          (injlist_compose (js1' ++ js2')) m m3

    apply check_injectlist_inject in CIL1.
    destruct CIL1 as [[? [? ?]] | ?]; subst; simpl in *.
      inv Incr1; simpl in *.
      intros b; intros. inv H. 
    apply check_injectlist_inject in CIL2.
    destruct CIL2 as [[? [? ?]] | ?]; subst; simpl in *.
      inv Incr2; simpl in *.
      do 2 rewrite app_nil_r in Sep13. assumption.
    intros b b1 delta1; intros.
      destruct H as [_ ? ? _ _].
      remember (injlist_compose js2' b1) as z1.
      destruct z1; apply eq_sym in Heqz1.
        destruct p as [b2 d2].
        specialize (Sep13 b b2 (delta1 + d2)).
        destruct Sep13; try rewrite injlist_compose_app; try unfold inj_compose.
           rewrite H1. trivial.
           rewrite H2. rewrite Heqz1. trivial.
           split; try assumption.
*)
(*           destruct H0 as [_ ? ? _ _].
           
  Lemma inject_separated_split:
        forall js2 ms2 m2 m3 (CIL2 : Sim_inj.check_injectlist js2 m2 ms2 m3)
               js1 ms1 m1    (CIL1 : Sim_inj.check_injectlist js1 m1 ms1 m2)
               js1' js2' 
               (Sep13 : inject_separated (injlist_compose (js1 ++ js2))
                                        (injlist_compose (js1' ++ js2')) m1 m3)
               (Incr1 : Forall2 inject_incr js1 js1')
               (Incr2: Forall2 inject_incr js2 js2'),
        inject_separated (injlist_compose js1) (injlist_compose js1') m1 m2.
  Proof. intros.
    apply check_injectlist_inject in CIL1.
    destruct CIL1 as [[? [? ?]] | ?]; subst; simpl in *.
      inv Incr1; simpl in *.
      intros b; intros. inv H. 
    apply check_injectlist_inject in CIL2.
    destruct CIL2 as [[? [? ?]] | ?]; subst; simpl in *.
      inv Incr2; simpl in *.
      do 2 rewrite app_nil_r in Sep13. assumption.
    intros b b1 delta1; intros.
      destruct H as [_ ? ? _ _].
      remember (injlist_compose js2' b1) as z1.
      destruct z1; apply eq_sym in Heqz1.
        destruct p as [b2 d2].
        specialize (Sep13 b b2 (delta1 + d2)).
        destruct Sep13; try rewrite injlist_compose_app; try unfold inj_compose.
           rewrite H1. trivial.
           rewrite H2. rewrite Heqz1. trivial.
           split; try assumption.
(*           destruct H0 as [_ ? ? _ _].
           
 destruct mi_inj.
      destruct H0 as [? ? ? _ _].
      intros b; intros. inv H. 
    
 rewrite
      destruct js1'; simpl in *.

    intros js2.
    induction js2; intros; simpl in *; subst. 
       destruct ms2; try contradiction.
       destruct ms0; simpl in *; try contradiction.
       subst.
       destruct js2'; simpl in *; try contradiction.
         do 2 rewrite app_nil_r in Sep13. assumption.
       inv INC.

     destruct ms2; try contradiction.
     destruct ms0; simpl in *; try contradiction.
     destruct js2'; simpl in *; try contradiction.
       inv INC. simpl in *. rename a into j. rename  m4 into j'.
     destruct CIL2. destruct CIL0.
     specialize (IHjs2 _ _ _ H0).
     intros b; intros.
       destruct SI1 as [A B].
       remember (j b2) as jb2.  
       destruct jb2; apply eq_sym in Heqjb2.
         destruct p. inv INC. assert (ZZ:= H8 _ _ _ Heqjb2).
         remember (injlist_compose js2 b0) as j2b0.
         destruct j2b0; apply eq_sym in Heqj2b0. destruct p.
           apply injlist_compose_inj_incr in H10.
           assert (QQ:= H10 _ _ _  Heqj2b0).
           specialize (Sep13 b b1 (delta + (z + z0))).
           destruct Sep13. rewrite injlist_compose_app. unfold inj_compose. rewrite H3. trivial.
                rewrite injlist_compose_app. simpl. unfold inj_compose.  rewrite H4. rewrite ZZ. rewrite QQ. trivial.
           split; trivial.
           destruct SI2 as [AA BB]. exfalso. apply H6. eapply (BB b2). unfold inj_compose. rewrite Heqjb2. rewrite Heqj2b0. reflexivity.
         destruct SI2 as [AA BB].
         apply BB in Heqj2b0.

  simpl.
    
       unfold inject_separated in *. intros b1 b2; intros. congruence.
     destruct ms1; try contradiction. simpl in *. destruct CIL1.
       inv Incr1. rename l' into js1'.
       specialize (IHjs1 _ _ _ H0 js2 m3 js1' js2' H5).
       intros b. intros. simpl in *. apply inj_compose_NoneD in H1.
         apply inj_compose_SomeD in H2. destruct H2 as [bb1 [d1 [d2 [X [Y ZZ]]]]]. subst.
         rename y into a'.
         destruct H1.
           remember (injlist_compose js2' b2) as z.          
           destruct z; apply eq_sym in Heqz. destruct p.
           destruct (Sep13 b b0 ((d1 + (d2 + z)))); unfold inj_compose.
               rewrite H1. trivial.
               rewrite X. rewrite injlist_compose_app. unfold inj_compose. rewrite Y. rewrite Heqz. trivial.
               split; trivial. 
(*xx               destruct FSI as [_ SI]. apply inj_
         
    remember (injlist_compose js2' b2) as z.
    destruct z; apply eq_sym in Heqz.
      destruct p. 
         destruct (Sep13 b1 b (delta + z)); try trivial.
         rewrite injlist_compose_app.
            unfold inj_compose. rewrite H. trivial.
         rewrite injlist_compose_app.
            unfold inj_compose. rewrite H0. rewrite Heqz. trivial.
         split; trivial. *)

   Admitted. (*   need maybe meminj assumptions, and inj_incr.*)

      *)
*)

 
  Lemma flat_inj_None_injlist:
        forall m b N (Hmb: None = (Mem.flat_inj (Mem.nextblock m) b)),
         (injlist_compose (Sim_inj.mkInjections m (S N)) b) = None.
   Proof.
     intros.
     induction N; simpl.
     unfold Mem.meminj_compose. rewrite <- Hmb. trivial.
     unfold Mem.meminj_compose. rewrite <- Hmb. trivial.
   Qed.

  Lemma mkInjections_app: forall m A B,
    Sim_inj.mkInjections m (A + B) =
    Sim_inj.mkInjections m A ++ Sim_inj.mkInjections m B.
    Proof.
      intros m A.
      induction A; simpl; intros. trivial.
      rewrite IHA. trivial.
    Qed.
(*
  Lemma mkInjections_app1: forall B m1 m2 A
         (SI: siminj (injlist_compose (Sim_inj.mkInjections m1 A)) m1 m2),
       Sim_inj.mkInjections m1 A ++ Sim_inj.mkInjections m2 B
      = Sim_inj.mkInjections m1 (A + B).
   Proof.
     intros. rewrite mkInjections_app. destruct SI.
     induction B.
     (*nil*)
       simpl; intros. rewrite app_nil_r. reflexivity.
     assert ((S B = B + 1)%nat). rewrite plus_comm. reflexivity.
       rewrite H1; clear H1.
       do 2 rewrite mkInjections_app.
       do 2 rewrite app_assoc.
       rewrite IHB. clear IHB. f_equal.
       simpl. f_equal. extensionality b.
           unfold Mem.flat_inj. 
simpl.
       assert (Sim_inj.mkInjections m1 (N1 + S N2) = injlist_compose  (Sim_inj.mkInjections m1 (N1 + N2)) (Sim_inj.mkInjections m1 1)).
       induction N2; simpl; intros; trivial.
       rewrite IHN2; clear IHN2.
       destruct SI.
       f_equal. extensionality b. unfold Mem.flat_inj; simpl.
          remember (zlt b (Mem.nextblock m1)) as z1.
          destruct z1. 
            remember (zlt b (Mem.nextblock m2)) as z2.
            destruct z2; trivial;
              unfold Mem.valid_block in *.
              specialize (H0 b _ _ (eq_refl _)). clear Heqz2. unfold Zge in z0. unfold Zlt in H0. rewrite H0 in z0. congruence.

          unfold Mem.valid_block in H. 
            unfold Zge in z. unfold Zlt in H. specialize (H b z). inv H.
     (*cons*) 
        intros. simpl.
        rewrite IHN1. trivial. clear IHN1.
        destruct SI.
        split; intros. clear H0. do 1 unfold inj_compose in H.
               specialize (H _ H1). (* unfold Mem.flat_inj in H.  
                unfold Mem.valid_block in H1. unfold zlt in H.*)  
               remember ( Mem.flat_inj (Mem.nextblock m1) b) as z.
               destruct z. destruct p. 
                unfold Mem.flat_inj in Heqz.
                unfold Mem.valid_block in H1.
                apply Znot_lt_ge in H1. rewrite zlt_false in Heqz; trivial. inv Heqz.
               destruct N1; simpl. unfold Mem.flat_inj in Heqz. simpl in H. unfold Mem.valid_block in H1. unfold inj_compose in H. rewrite H1 in Heqz.
             ~ Mem.valid_block m1 b ->   Mem.flat_inj (Mem.nextblock m1) b = None 
                unfold Mem.flat_inj in Heqz.
                unfold Mem.valid_block in H1.
                apply Znot_lt_ge in H1. rewrite zlt_false in Heqz; trivial. inv Heqz.
                
                unfold Mem.valid_block in H1.
                 remember ().
unfold Mem.flat_inj in H.  
                unfold Mem.valid_block in H1. unfold zlt in H.
          
            
 destruct z0. apply Zge_le in z0. rewrite z0 in H0.
                
            remember 


(SI12: siminj
         (injlist_compose
            (Sim_inj.mkInjections m1 (Sim_inj.num_passes FSim12))) m1 m2)
Sim_inj.mkInjections m1 (Sim_inj.num_passes FSim12) ++
        Sim_inj.mkInjections m2 (Sim_inj.num_passes FSim23)
 = Sim_inj.mkInjections m1
     (Sim_inj.num_passes FSim12 + Sim_inj.num_passes FSim23

  Lemma mkInjections_app: forall N2 m1 m2 N1
         (SI: siminj (injlist_compose (Sim_inj.mkInjections m1 N1)) m1 m2),
       Sim_inj.mkInjections m1 N1 ++ Sim_inj.mkInjections m2 N2
      = Sim_inj.mkInjections m1 (N1 + N2).
   Proof.
     intros N2.
     induction N1.
     (*nil*)
       simpl; intros.
       induction N2; simpl; intros; trivial.
       rewrite IHN2; clear IHN2.
       destruct SI.
       f_equal. extensionality b. unfold Mem.flat_inj; simpl.
          remember (zlt b (Mem.nextblock m1)) as z1.
          destruct z1. 
            remember (zlt b (Mem.nextblock m2)) as z2.
            destruct z2; trivial;
              unfold Mem.valid_block in *.
              specialize (H0 b _ _ (eq_refl _)). clear Heqz2. unfold Zge in z0. unfold Zlt in H0. rewrite H0 in z0. congruence.

          unfold Mem.valid_block in H. 
            unfold Zge in z. unfold Zlt in H. specialize (H b z). inv H.
     (*cons*) 
        intros. simpl.
        rewrite IHN1. trivial. clear IHN1.
        destruct SI.
        split; intros. clear H0. do 1 unfold inj_compose in H.
               specialize (H _ H1). (* unfold Mem.flat_inj in H.  
                unfold Mem.valid_block in H1. unfold zlt in H.*)  
               remember ( Mem.flat_inj (Mem.nextblock m1) b) as z.
               destruct z. destruct p. 
                unfold Mem.flat_inj in Heqz.
                unfold Mem.valid_block in H1.
                apply Znot_lt_ge in H1. rewrite zlt_false in Heqz; trivial. inv Heqz.
               destruct N1; simpl. unfold Mem.flat_inj in Heqz. simpl in H. unfold Mem.valid_block in H1. unfold inj_compose in H. rewrite H1 in Heqz.
             ~ Mem.valid_block m1 b ->   Mem.flat_inj (Mem.nextblock m1) b = None 
                unfold Mem.flat_inj in Heqz.
                unfold Mem.valid_block in H1.
                apply Znot_lt_ge in H1. rewrite zlt_false in Heqz; trivial. inv Heqz.
                
                unfold Mem.valid_block in H1.
                 remember ().
unfold Mem.flat_inj in H.  
                unfold Mem.valid_block in H1. unfold zlt in H.
          
            
 destruct z0. apply Zge_le in z0. rewrite z0 in H0.
                
            remember 


(SI12: siminj
         (injlist_compose
            (Sim_inj.mkInjections m1 (Sim_inj.num_passes FSim12))) m1 m2)
Sim_inj.mkInjections m1 (Sim_inj.num_passes FSim12) ++
        Sim_inj.mkInjections m2 (Sim_inj.num_passes FSim23)
 = Sim_inj.mkInjections m1
     (Sim_inj.num_passes FSim12 + Sim_inj.num_passes FSim23
*)

Fixpoint check_injectlist1 (js : list meminj) m1 ms last : Prop :=
   match js,ms with
     nil, (first::nil) => first=m1 /\ m1 = last 
   | j::J, first::m::M => first=m1 /\ Mem.inject j m1 m /\ check_injectlist1 J m (m::M) last
   | _ , _ => False
   end.

  Lemma check_injectlist1_elim: forall J first M last, check_injectlist1 J first M last ->
      S(length J) = length M /\ exists t, M=first::t. 
   Proof.
     intros J.
     induction J; simpl; intros.
        destruct M; try contradiction.
        destruct M; try contradiction. 
        destruct H; subst. simpl. split; trivial. exists nil; trivial.
      destruct M; try contradiction.
        destruct M; try contradiction. 
        destruct H as [? [? ?]]; subst. simpl.
        destruct (IHJ _ _ _ H1) as [? [? ?]]. inv H2; subst; simpl in *. 
        rewrite H. split; trivial. exists (m0::x); trivial. 
    Qed.

  Lemma check_injectlist1_check_injectlist: 
     forall J first m M last, check_injectlist1 J first (m::M) last ->
          Sim_inj.check_injectlist J first M last.
   Proof.
    intros J. 
     induction J; simpl; intros.
        destruct M; try contradiction. destruct H; trivial.
      destruct M; try contradiction. 
        destruct H as [? [? ?]]; subst.
        specialize (IHJ _ _ _ _ H1). split; trivial.  
    Qed.


  Lemma check_injectlist_check_injectlist1: 
     forall J first M last, Sim_inj.check_injectlist J first M last ->
          check_injectlist1 J first (first::M) last.
   Proof.
    intros J. 
     induction J; simpl; intros.
        destruct M; try contradiction. subst; split; trivial.
      destruct M; try contradiction. 
        destruct H as [? ?]; subst.
        specialize (IHJ _ _ _ H0). split; trivial.  split; trivial.  
    Qed.

  Lemma mem_square_memExtAux: forall js1 m3 m1 ms 
          (CIL : Sim_inj.check_injectlist js1 m1 ms m3) ms1 m33
          (CIL1 : Sim_inj.check_injectlist js1 m1 ms1 m33) ms'  m1'
          (MSQ : Sim_inj.mem_square js1 m1 ms m1' ms') ,
  Sim_inj.mem_square js1 m1 ms1 m1' ms'.
  Proof.
    intros js1.
    remember (rev js1) as J. generalize dependent js1.
    induction J; simpl; intros.
    (*nil*)
       assert (js1 = nil). destruct js1. trivial. simpl in HeqJ. apply eq_sym in HeqJ.  
           apply app_eq_nil in HeqJ. destruct HeqJ. inv H0.
       clear HeqJ. subst. simpl in *.
       destruct ms; try contradiction. subst.
       destruct ms1; try contradiction. subst. 
       destruct ms'; try contradiction. assumption.
    (*cons*)
       assert (exists j, exists JJ, js1 = JJ ++ (j::nil)). admit.
       destruct H as [j [JJ HJJ]]. subst. rewrite rev_app_distr in HeqJ. simpl in HeqJ.
       inv HeqJ.
       specialize (IHJ _ (eq_refl _)).
       simpl in *. 
       apply check_injectlist_split in CIL. destruct CIL as [M1 [M2 [mm [X [CILa HH2]]]]]. subst.
       apply check_injectlist_split in CIL1. destruct CIL1 as [N1 [N2 [nn [X [CIL1a KK2]]]]]. subst.
       simpl in *.
       destruct M2; try contradiction.
       destruct N2; try contradiction.
       destruct HH2 as [CILb X]. destruct M2; try contradiction. subst.
       destruct KK2 as [CIL1b X]. destruct N2; try contradiction. subst.
       specialize (IHJ _ _ _ CILa). clear CILa.
       specialize (IHJ _ _ CIL1a). clear CIL1a.
       assert (D:= Sim_inj.mem_square_D _ _ _ _ _ MSQ). repeat rewrite app_length in D. simpl in D.
                 repeat rewrite (plus_comm _ 1) in D. simpl in D.
                 destruct D as [D1 D2]. inv D1.               
       assert (exists M', exists mm', ms' = M' ++ (mm'::nil)). admit.                             
       destruct H as [M' [mm' X]]; subst. 
       repeat rewrite app_length in D2. simpl in D2.
                 repeat rewrite (plus_comm _ 1) in D2. simpl in D2. inv D2.
       apply eq_sym in H0. apply eq_sym in H1.
       assert (X:= Sim_inj.mem_square_l _ _ _ _ _ _ _ _ MSQ H0 H1).
       apply IHJ in X. clear IHJ MSQ.
(*
       destruct X.
       destruct ms'; try contradiction.
       destruct CIL as [CILa CILb]; subst.
       destruct CIL1 as [CIL1a CIL1b]; subst.
       destruct MSQ as [MSQa [MSQb [MSQc MSQd]]].
       rename a into j. rename js1 into J.
       split; trivial.
       split. Focus 2. (* split; intros.
                destruct MSQb. eapply H1. apply H. 
                 unfold loc_out_of_reach in H.
                destruct CIL1a. destruct mi_inj. 
                destruct CILa. destruct mi_inj.
           clear mi_representable mi_memval mi_representable0 mi_memval0 H2 H1.
              unfold  Mem.meminj_no_overlap in mi_no_overlap.
           admit. 
           admit. *)
       split; trivial. eapply (IHjs1 _ m0). apply CIL1b. Focus 2. apply MSQd.
       specialize (IHjs1 m3 m _ _ CILb _ _ MSQd). apply IHjs1. Focus 3. apply CIL1b.  apply CIL1b. 
       eapply (IHjs1 _ m0). Focus 2.  apply CIL1b.  apply CIL1b.*) admit.
   Qed.

(*
  Lemma mem_square_memEXtAux1: forall js1 m3 m1 ms a
          (CIL : check_injectlist1 js1 m1 (a::ms) m3) ms'  m1'
          (MSQ : Sim_inj.mem_square js1 m1 ms m1' ms') ms1 b
          (CIL1 : check_injectlist1 js1 m1 (b::ms1) m3),
  Sim_inj.mem_square js1 b ms1 m1' ms'.
  Proof.
    intros js1.
    induction js1; simpl; intros.
    (*nil*)
       destruct ms; try contradiction.
       destruct ms1; try contradiction. 
       destruct ms'; try contradiction. destruct CIL1. subst. assumption.
    (*cons*)
       destruct ms; try contradiction.
       destruct ms1; try contradiction.
       destruct ms'; try contradiction.
       destruct CIL as [X [CILa CILb]]; subst.
       destruct CIL1 as [X [CIL1a CIL1b]]; subst.
       destruct MSQ as [MSQa [MSQb [MSQc MSQd]]].
       rename a into j. rename js1 into J.
       split; trivial.
       split. Focus 2. (* split; intros.
                destruct MSQb. eapply H1. apply H. 
                 unfold loc_out_of_reach in H.
                destruct CIL1a. destruct mi_inj. 
                destruct CILa. destruct mi_inj.
           clear mi_representable mi_memval mi_representable0 mi_memval0 H2 H1.
              unfold  Mem.meminj_no_overlap in mi_no_overlap.
           admit. 
           admit. *)
       split; trivial. (*eapply (IHjs1 _ m). Focus 2. apply MSQd.
       specialize (IHjs1 m3 m _ _ CILb _ _ MSQd). apply IHjs1. Focus 3. apply CIL1b.  apply CIL1b. 
       eapply (IHjs1 _ m0). Focus 2.  apply CIL1b.  apply CIL1b.*) admit.
   admit.
   Qed.
*)

  Lemma mem_square_memExt: forall
       js2 m2 ms2 m3 (CIL2: Sim_inj.check_injectlist js2 m2 ms2 m3)
       js1 m1 ms1 (CIL1: Sim_inj.check_injectlist js1 m1 ms1 m2)
       ms (CIL: Sim_inj.check_injectlist (js1 ++ js2) m1 ms m3)
       ms' m1' (MSQ: Sim_inj.mem_square (js1 ++ js2) m1 ms m1' ms'),
  Sim_inj.mem_square (js1 ++ js2) m1 (ms1 ++ ms2) m1' ms'.
  Proof.
    intros js2.
    induction js2; intros; simpl in *.
    (*nil*)
       destruct ms2; try contradiction. repeat rewrite app_nil_r in *.  subst; simpl.
       eapply mem_square_memExtAux. apply CIL. apply CIL1. apply MSQ.
    (*cons*)
      rename a into j.
      destruct ms2; try contradiction.
      destruct CIL2 as [CIL2a CIL2b].
      assert (ZZ: Mem.inject j m2 m /\ m = m). split; trivial.
      assert (XX:= check_injectlist_app _ _ _ _ CIL1 (m::nil) (j::nil) m ZZ).
      specialize (IHjs2 _ _ _ CIL2b _ _ _ XX). clear XX.
       rewrite <- app_assoc in IHjs2. simpl in IHjs2.
      specialize (IHjs2 _ CIL _ _ MSQ); clear CIL MSQ. 
       rewrite <- app_assoc in IHjs2. simpl in IHjs2. assumption.
  Qed.
(*
Fixpoint mem_square1 js m1 ms m1' ms' : Prop :=
  match js, ms, ms' with
    nil, (m::nil) , (m'::nil) => mem_forward m1 m1' /\ m=m1 /\ m'=m1'
 |  j::jss, m::m2::mss, m'::m2'::mss' => mem_unchanged_on (loc_unmapped j) m1 m1' /\
                                 mem_unchanged_on (loc_out_of_reach j m1) m2 m2' /\
                                 mem_forward m1 m1' /\ mem_square1 jss m2 (m2::mss) m2' (m2'::mss') /\ m=m1 /\ m'=m1'
 | _ , _ , _ => False
  end.
  Lemma mem_square1_elim: forall J m M m' M',
        mem_square1 J m M m' M' -> length M = length M' /\ length M' = S(length J) /\ (m = hd m M).
   Proof.
     intros J.
     induction J; simpl; intros.
       destruct M; try contradiction.
       destruct M; try contradiction.
       destruct M'; try contradiction.
       destruct M'; try contradiction. simpl.
       destruct H as [? [? ?]]. subst. split; trivial. split; trivial.
     destruct M; try contradiction.
       destruct M; try contradiction.
       destruct M'; try contradiction.
       destruct M'; try contradiction. simpl in *.
       destruct H as [? [? [? [? [? ?]]]]]. subst.
       destruct (IHJ _ _ _ _ H2) as [? [? ?]].
           simpl in *. rewrite H3. rewrite <- H4. split; trivial. split; trivial.
   Qed.*)
(*
  Lemma mem_square1_memEXt: forall J m M m' M',
       S(length J) = length M ->
       forall MM (MSQ: mem_square1 J m MM m' M'),
  mem_square1 J m M m' M'.
  Proof.
    intros J.
    induction J; intros; simpl in *.
    (*nil*)
       destruct MM; try contradiction.
       destruct MM; try contradiction.
       destruct M'; try contradiction.
       destruct M'; try contradiction.
       destruct M; simpl in *; try contradiction. inv H. 
       destruct M; simpl in *; try contradiction. destruct MSQ as [? [? ?]].  subst. assumption. inv H.  
    (*cons*)
      rename a into j.
      destruct M'; try contradiction.
      destruct M; simpl in *; inv H. (* try contradiction.*)
      destruct ms; try contradiction.
(*      destruct CIL as [CILa CILb].*)
      destruct MSQ as [MSQa [MSQb [MSQc MSQd]]].
      split; trivial.
      specialize (IHJ m2 M m3 H1 M' ms).
      assert (X: Sim_inj.mem_square J m2 M' m3 ms). admit. admit. Qed.
     *)
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

  Let data13 := ((Sim_inj.core_data FSim23 * Sim_inj.core_data FSim12) * mem )%type. 

  Let numpasses13 := ((Sim_inj.num_passes FSim12) + (Sim_inj.num_passes FSim23))%nat. 

  Definition sem_compose_ord (x y: data13) := (lex_ord (Sim_inj.core_ord FSim23) (Sim_inj.core_ord FSim12)) (fst x) (fst y).
(*  Definition well_founded_sem_compose_ord := wf_lex_ord (Sim_inj.core_ord_wf FSim23) (Sim_inj.core_ord_wf FSim12).*)
  Definition wf1:=  wf_lex_ord (Sim_inj.core_ord_wf FSim23) (Sim_inj.core_ord_wf FSim12).

  Definition well_founded_sem_compose_ord: well_founded sem_compose_ord.
       unfold sem_compose_ord.
       assert (ZZ:= @wf_inverse_rel data13 _ _ (fun a b => fst a = b) wf1).
       simpl in ZZ.
       assert (HH: (fun x y : data13 =>
        exists2 b : Sim_inj.core_data FSim23 * Sim_inj.core_data FSim12,
          fst x = b &
          forall c : Sim_inj.core_data FSim23 * Sim_inj.core_data FSim12,
          fst y = c ->
          lex_ord (Sim_inj.core_ord FSim23) (Sim_inj.core_ord FSim12) b c)
        = (fun x y : data13 =>
   lex_ord (Sim_inj.core_ord FSim23) (Sim_inj.core_ord FSim12) (fst x)
     (fst y))).
         extensionality x. extensionality y. apply prop_ext.
         split; intros. destruct x; destruct y; simpl in *. destruct H. subst. apply H0. trivial.
             destruct x; destruct y; simpl. exists p. trivial. intros. subst. simpl in *. trivial.
     rewrite HH in ZZ. apply ZZ.
   Qed.
(*
  Definition well_founded_sem_compose_ord := wf_lex_ord (Sim_inj.core_ord_wf FSim23) (Sim_inj.core_ord_wf FSim12).*)

  Inductive compose_match_state : data13 -> list meminj -> C1 -> mem -> C3 -> mem -> Prop :=
    intro_compose_match_state : 
      forall d12 js1 js2 c2 m2 d23 c1 m1 c3 m3,
      Sim_inj.match_state FSim12 d12 js1 c1 m1 c2 m2 -> 
      Sim_inj.match_state FSim23 d23 js2 c2 m2 c3 m3 -> 
      compose_match_state ((d23,(*(Some c2,(js1,ms1++ms2,js2),*)d12),m2) (js1 ++ js2) c1 m1 c3 m3.
      (*compose_match_state (d23,(*(Some c2,m2),*)d12) (js1 ++ js2) c1 m1 c3 m3.*)

  Lemma compose_match_state_numpasses: 
        forall (cd : data13) (js : list meminj) (c1 : C1) (m1 : mem) (c3 : C3) (m3 : mem),
        compose_match_state cd js c1 m1 c3 m3 -> length js = numpasses13.
    Proof.
      intros.
      inv H. unfold numpasses13. 
      rewrite <- (Sim_inj.match_state_num_passes _ _ _ _ _ _ _ H0).
      rewrite <- (Sim_inj.match_state_num_passes _ _ _ _ _ _ _ H1).
      rewrite app_length. reflexivity.
    Qed.

  Lemma compose_match_state_siminj: forall d j st1 m1 st2 m2,
        compose_match_state d j st1 m1 st2 m2 -> siminj (injlist_compose j) m1 m2.
    Proof. 
      intros until m2. intros [H1 H2]. intros.
      apply Sim_inj.match_state_siminj in H.
      apply Sim_inj.match_state_siminj in H0.
      eapply siminj_list_compose; eauto.
    Qed.

  Lemma compose_core_diagram: 
        forall (st1 : C1) (m1 : mem) (st1' : C1) (m1' : mem),
                corestep Sem1 ge1 st1 m1 st1' m1' ->
        forall (cd : data13) (st3 : C3) (J : list meminj) (m3 : mem),
               compose_match_state cd J st1 m1 st3 m3 ->
        exists st3' : C3, exists m3' : mem, exists cd' : data13, exists J' : list meminj,
               Forall2 inject_incr J J' /\
               inject_separated (injlist_compose J) (injlist_compose J') m1 m3 /\
               compose_match_state cd' J' st1' m1' st3' m3' /\
               (corestep_plus Sem3 ge3 st3 m3 st3' m3' \/
                corestep_star Sem3 ge3 st3 m3 st3' m3' /\
                clos_trans data13 sem_compose_ord cd' cd). (* clos_trans data13
                (lex_ord (Sim_inj.core_ord FSim23) (Sim_inj.core_ord FSim12)) cd' cd).*)
   Proof. 
    intros. inv H0. rename c2 into st2. rename js1 into J1. rename js2 into J2. 
    destruct (Sim_inj.core_diagram FSim12 st1 m1 st1' m1' H _ _ _ _ H1) as
      [st2' [m2' [d12' [J1' [HJ1' [Sep12 [MS12 Step2]]]]]]].
    assert (H6: corestep_plus Sem2 ge2 st2 m2 st2' m2' \/
               ((st2,m2) = (st2',m2') /\ Sim_inj.core_ord FSim12 d12' d12) ).
      destruct Step2. auto.
      destruct H0.
        destruct H0.
        destruct x. right. split; auto.
                    left. exists x; auto.
    clear Step2.
    assert (Inj1 := Sim_inj.match_state_siminj _ _ _ _ _ _ _ H1). 
    assert (Inj2 := Sim_inj.match_state_siminj _ _ _ _ _ _ _ H2).
    destruct H6 as [Step2 | [SEQ Ord]].
    (*case corestep_plus Sem2 ge2 st2 m2 st2' m2'*)
      destruct Step2.
      destruct Inj1 as [Inj1A Inj1B]. clear Inj1A.
      destruct Inj2 as [Inj2A Inj2B]. clear Inj2B. 
      apply csem_allowed_modifications in H. rename H into AM1.
      assert (AM2:= corestepN_allowed_modifications H0).
      clear H1. clear st1 st1.
      assert (AUX := @InjInj_core_diagram_AUX _ _ _ _ _ _ _ _ _ FSim23 _ _ _ _ _ H0 _ _ _ _ H2).
      destruct AUX as [st3' [m3' [d' [J2' [AM3 [Incr2 [Sep2 [MS EXEC]]]]]]]].
      exists st3'. exists m3'.
      exists ((d',d12'),m2'). (*unfold data13.  exists (d12',(J1',m2',J2'),d').*)
      exists (J1' ++ J2'). 
      split. eapply inject_incr_compose. apply HJ1'. apply Incr2.
      split. (* (Incr1 : inject_incr j1 j1')
                (Incr2 : inject_incr j2 j2')
                (Sep12 : inject_separated j1 j1' m1 m2)
                (Sep23: inject_separated j2 j2' m2 m3),
                inject_separated (inj_compose j1 j2) (inj_compose j1' j2') m1 m3*)
              eapply inject_separated_injlist_compose. apply HJ1'. apply Incr2. apply Inj1B. apply Inj2A. apply Sep12. apply Sep2.
      split. econstructor. apply MS12. apply MS.
      
      destruct EXEC as [ExecPlus | [ExecStar Ord]].
        left; assumption.
        right. split; try assumption.
(*               assert (ORD:= @lex_ord_clos_trans_left _ (Sim_inj.core_data FSim12) _ _ _ Ord (Sim_inj.core_ord FSim12) d12' d12).
               assert (ORD1:= @lex_ord_clos_trans_left _ mem _ _ _ ORD (fun m mm => True) m2' m2). simpl in ORD1.
               unfold sem_compose_ord. fold data13 in ORD1. apply ORD1. (Sim_inj.core_ord FSim12) d12' d12).
               apply lex_ord_clos_trans_left.
               eapply lex_ord_clos_trans_left. apply Ord.*) admit. (*order stuff*)
    (*case (st2, m2) = (st2', m2') /\ Sim_inj.core_ord FSim12 d' d12*)
      inv SEQ. 
      exists st3. exists m3. 
      exists ((d23,(*(J1',m2',J2),*)d12'),m2'). (*exists (d23, d12'). *)(*was : exists (d',(Some c2,m2),d23).*)
      exists (J1' ++ J2).
      split. eapply inject_incr_compose. apply HJ1'. apply inject_incr_list_refl. 
      split. eapply inject_separated_injlist_compose. (*alternative : eapply inject_separated_siminj_compose.*)
               apply HJ1'. 
               apply inject_incr_list_refl.
               apply Inj1.
               apply Inj2. 
               apply Sep12.
               intros b; intros. rewrite H0 in H3. inv H3. (*congruence.*)
      split. econstructor. apply MS12. apply H2. 
      right. split. exists O. simpl; auto.
        eapply t_step. apply lex_ord_right. apply Ord.
        (*eapply t_step. econstructor. apply lex_ord_right. apply Ord. admit.*) (*seem to require changing the order of components!*) (*apply lex_ord_right. apply Ord.*)
  Qed.

  Lemma compose_core_initial:
        forall v1 v3 sig (HEntry : In (v1, v3, sig) entry_points13) vals1
               c1 m1 (MIC1 : make_initial_core Sem1 ge1 v1 vals1 = Some c1) 
              (IM1: initial_mem Sem1 ge1 m1),
        let js := Sim_inj.mkInjections m1 numpasses13 in
        exists cd, exists c3, exists vals3, exists m3,
          make_initial_core Sem3 ge3 v3 vals3 = Some c3 /\
          initial_mem Sem3 ge3 m3 /\ compose_match_state cd js c1 m1 c3 m3.
  Proof.
    intros.
    assert (J1: exists v2, In (v1,v2,sig) entry_points12 /\ In (v2,v3,sig) entry_points23).
      pose proof EPC as myEPC.
      clear - HEntry myEPC.
      induction myEPC.
      simpl in HEntry. destruct HEntry. inv H.
      exists v2; split; simpl; auto.
      destruct (IHmyEPC H) as [v2' [? ?]].
      exists v2'; simpl; split; auto.
      inv HEntry.
   destruct J1 as [v2 [J12 J23]].
    generalize (Sim_inj.core_initial FSim12 _ _ _ J12); intro CI12.

    specialize (CI12 _ _ _ MIC1 IM1).
    destruct CI12 as [d12 [c2 [vals2 [m2 [MIC2 [IM2 MS12]]]]]].
    generalize (Sim_inj.core_initial FSim23 _ _ _ J23); intro CI23.
    specialize (CI23 _ _ _ MIC2 IM2).
    destruct CI23 as [d23 [c3 [vals3 [m3 [MIC3 [IM3 MS23]]]]]].
    (*exists ((d12,
       (Sim_inj.mkInjections m1 (Sim_inj.num_passes FSim12), m2,
       Sim_inj.mkInjections m2 (Sim_inj.num_passes FSim23)), d23)). *)
    exists ((d23,d12),m2). 
    exists c3. exists vals3. exists m3.
    split; trivial.
    split; trivial.
    assert (ZZ:= intro_compose_match_state _ _ _ _ _ _ _ _ _ _ MS12 MS23).
    unfold js. unfold numpasses13. 
       apply Sim_inj.match_state_siminj in MS12.
       apply Sim_inj.match_state_siminj in MS23.
       rewrite mkInjections_app. (*apply ZZ.*) 
      admit. (*rewrite (flatinj_compose _ _ H1).*)
  Qed. (*rewrite (flatinj_compose _ _ H1).*)
(*
  Lemma compose_safely_halted1:
     forall (cd : data13) (js : list meminj) c1 m1 c3 m3 v1 
            (CMS: compose_match_state cd js c1 m1 c3 m3)
            (SH1: safely_halted Sem1 ge1 c1 = Some v1),
     safely_halted Sem3 ge3 c3 = Some v1 
     /\ exists ms, check_injectlist1 js m1 ms m3.
     Proof. 
       intros.
       inv CMS. rename H into CMS12. rename H0 into CMS23.
       destruct (Sim_inj.core_halted FSim12 _ _ _ _ _ _ _ CMS12 SH1) as [SH2 [ms1 Inj1]].
       destruct (Sim_inj.core_halted FSim23 _ _ _ _ _ _ _ CMS23 SH2) as [SH3 [ms2 Inj2]].
       split; trivial.
       clear - Inj1 Inj2.
       exists (ms1 ++ ms2). eapply check_injectlist_app; eauto. 
     Qed.*)
  Lemma compose_safely_halted:
     forall (cd : data13) (js : list meminj) c1 m1 c3 m3 v1 
            (CMS: compose_match_state cd js c1 m1 c3 m3)
            (SH1: safely_halted Sem1 ge1 c1 = Some v1),
     safely_halted Sem3 ge3 c3 = Some v1 
     /\ exists ms, Sim_inj.check_injectlist js m1 ms m3.
     Proof. 
       intros.
       inv CMS. rename H into CMS12. rename H0 into CMS23.
       destruct (Sim_inj.core_halted FSim12 _ _ _ _ _ _ _ CMS12 SH1) as [SH2 [ms1 Inj1]].
       destruct (Sim_inj.core_halted FSim23 _ _ _ _ _ _ _ CMS23 SH2) as [SH3 [ms2 Inj2]].
       split; trivial.
       clear - Inj1 Inj2.
       exists (ms1 ++ ms2). eapply check_injectlist_app; eauto. 
     Qed.

  Lemma compose_at_external: forall cd J st1 m1 st3 m3 e vals1
           (CMS: compose_match_state cd J st1 m1 st3 m3)
           (AtExt1: at_external Sem1 st1 = Some (e, vals1)),
       exists ms,
           Sim_inj.check_injectlist J m1 ms m3 /\
           exists vals3,
              Forall2 (val_inject (injlist_compose J)) vals1 vals3 /\
              Forall2 Val.has_type vals3 (sig_args (ef_sig e)) /\
              at_external Sem3 st3 = Some (e, vals3).
  Proof. 
    intros.
    inv CMS. rename c2 into st2. rename H into CMS12. rename H0 into CMS23.
    destruct (Sim_inj.core_at_external FSim12 _ _ _ _ _ _ _ _ CMS12 AtExt1) as [ms2 [CIL2 [vals2 [ValsInj1 [HasType2 AtExt2]]]]].
    destruct (Sim_inj.core_at_external FSim23 _ _ _ _ _ _ _ _ CMS23 AtExt2) as [ms3 [CIL3 [vals3 [ValsInj2 [HasType3 AtExt4]]]]].
    subst.
    assert (ZZ:= check_injectlist_app _ _ _ _ CIL2 _ _ _ CIL3).
    exists (ms2 ++ ms3).
    split; trivial.
    exists vals3.
    split. rewrite injlist_compose_app. 
           eapply (vals_inject_compose _ _ _ ValsInj1 _ _ ValsInj2).
    split; trivial.  
  Qed.

  Lemma compose_after_external: 
        forall (cd : data13) (js js' : list meminj) st1 st3 m1 ms e vals1 ret1 rets 
                m1' ms' m3 m3' ret3
               (CIL: Sim_inj.check_injectlist js m1 ms m3)
               (CMS: compose_match_state cd js st1 m1 st3 m3)
               (AtExt1: at_external Sem1 st1 = Some (e, vals1))
               (Incr: Forall2 inject_incr js js')
               (Sep13: inject_separated (injlist_compose js) (injlist_compose js') m1 m3)
               (CIL': Sim_inj.check_injectlist js' m1' ms' m3')
               (RET': Sim_inj.check_returns js' ret1 rets ret3)
               (MSQ: Sim_inj.mem_square js m1 ms m1' ms')
               (Tp3: Val.has_type ret3 (proj_sig_res (ef_sig e))),
        exists cd', exists st1', exists st3',
          after_external Sem1 ret1 st1 = Some st1' /\
          after_external Sem3 ret3 st3 = Some st3' /\
          compose_match_state cd' js' st1' m1' st3' m3'.
  Proof.
    intros.
    inv CMS. rename c2 into st2. rename H into CMS12. rename H0 into CMS23. 
    destruct (Sim_inj.core_at_external _ _ _ _ _ _ _ _ _ CMS12 AtExt1) 
          as [ms1 [CIL1 [vals2 [VI2 [ArgTp2 AtExt2]]]]].
    destruct (Sim_inj.core_at_external _ _ _ _ _ _ _ _ _ CMS23 AtExt2) 
          as [ms2 [CIL2 [vals3 [VI3 [ArgTp3 AtExt3]]]]].
    apply injlist_incr_split in Incr. destruct Incr as [js1' [js2' [XX [Incr1 Incr2]]]]. subst.
    assert (MSQ' := mem_square_memExt _ _ _ _ CIL2 _ _ _ CIL1 _ CIL _ _ MSQ).
    clear CIL MSQ ms. (*apply check_injectlist_split in CIL.
    destruct CIL as (*[[NIL CIL2] |*) [M1 [M2 [m [M [CCIL1 CCIL2]]]]]. subst.*)

      assert (X:= check_injectlist_split _ _ _ _ _ CIL'). destruct X as [M1' [M2' [m2' [X [CIL1' CIL2']]]]]. subst. 
      apply check_returns_split in RET'. destruct RET' as [rets12' [rets23' [ret2 [XX [RET12' RET23']]]]]. subst.

      assert (X1 :=  Sim_inj.core_after_external FSim12 d12 js1 js1' st1 st2 m1 ms1 e vals1 ret1 rets12' m1' M1' m2 m2' ret2
                      CIL1 CMS12 AtExt1 Incr1). 
      destruct X1 as [d12' [st1' [st2' [AftExt1 [AftExt2 CMS12']]]]]; simpl; try trivial.
          (*injlist_separated*) 
              clear AtExt1 AtExt2 AtExt3 VI2 VI3 ArgTp2 ArgTp3 Tp3 CMS12 CMS23. 
              intros b1 b2 delta. intros. unfold inject_separated in Sep13.
              unfold Sim_inj.check_injectlist in CIL1. admit.
              
         (*memsquare_splits*) apply Sim_inj.mem_square_l in MSQ'. trivial.
                               apply eq_sym. eapply (Sim_inj.check_injectlist_D _ _ _ _ CIL1).
                               apply eq_sym. rewrite <- (Forall2_length _ _ _ Incr1). apply (Sim_inj.check_injectlist_D _ _ _ _ CIL1').
         (*hastype*) eapply check_returns_types. apply Tp3. apply RET23'.

      assert (Z1:= check_injectlist_DTail _ _ _ _ CIL1).
      destruct Z1.
      (*case js1 = nil*) destruct H as [? [? ?]]; subst. simpl in *.
            inv Incr1. simpl in *.
          destruct M1'; try contradiction.
          destruct rets12'; try contradiction. subst. clear CIL1. simpl in *.
(*          assert (X1 :=  Sim_inj.core_after_external FSim12 d12 nil nil st1 st2 
                m2 nil e vals1 ret1 nil m2' nil m2 m2'  ret1 (eq_refl _) CMS12).
          destruct X1 as [d12' [st1' [st2' [AftEXt1 [AftEXt2 CMS12']]]]]; simpl; try trivial.
            intros b; intros. inv H.
            apply Sim_inj.mem_square_mem_forward in MSQ. apply MSQ.
            eapply check_returns_types; eauto.*)
          assert (X2 := Sim_inj.core_after_external FSim23 d23 js2 js2' st2 st3 m2 ms2 e
                       vals2 ret1 rets23' m2' M2' m3 m3' ret3).
          destruct X2 as [d23' [stss' [st3' [AftExt22 [AftExt3 CMS23']]]]]; simpl; try trivial.
          rewrite AftExt2 in AftExt22. apply eq_sym in AftExt22. inv AftExt22.
          eexists. (*exists ((d23',d12'), m2').*)
          exists st1'. exists st3'.
          split. apply AftExt1. 
          split. apply AftExt3. 
          assert (ZZ:= intro_compose_match_state _ _ _ _ _ _ _ _ _ _ CMS12' CMS23'). 
          simpl in ZZ. apply ZZ. 
      (*cons*)
      destruct H as [J1 [j1 [M1 [Z1 Z2]]]]. subst.
        assert (Z1':= check_injectlist_DTail _ _ _ _ CIL1').
        destruct Z1'.
        (*case js1' = nil*) destruct H as [H _]; subst. apply Forall2_length in Incr1. rewrite app_length in Incr1.  simpl in Incr1. rewrite plus_comm in Incr1.  rewrite plus_Sn_m in Incr1. inv Incr1.
        (*cons*)
        destruct H as [J1' [j1' [MM1' [Z1' Z2']]]]. subst.
       
        repeat rewrite <- app_assoc  in MSQ'. simpl in MSQ'. 
               assert (Z1 : length J1 = length M1). apply Sim_inj.check_injectlist_D in CIL1. destruct CIL1 as [Z _]. 
                      do 2 rewrite app_length in Z.  rewrite (plus_comm (length M1)) in Z.  rewrite (plus_comm (length J1)) in Z. simpl in Z. inv Z. trivial.
               assert (Z2 : length J1 = length MM1').  apply Forall2_length in Incr1. 
                     apply Sim_inj.check_injectlist_D in CIL1'. destruct CIL1' as [Z _].
                      rewrite  Incr1 in Z. 
                      do 2 rewrite app_length in Z.  rewrite (plus_comm (length MM1')) in Z.  rewrite (plus_comm (length J1)) in Z. simpl in Z. inv Z. trivial.
        assert (Z:= Sim_inj.mem_square_r J1 M1 MM1' m1 m1' js2 ms2 M2' j1 m2 m2' MSQ' Z1 Z2).
      assert (X2 :=  Sim_inj.core_after_external FSim23 d23 js2 js2' 
                    st2 st3 m2 ms2 e vals2 
                  ret2 rets23' m2' M2' _ m3' ret3 
                     CIL2 CMS23 AtExt2 Incr2). 
      destruct X2 as [d23' [st22' [st3' [AftExt22 [AftExt3 CMS23']]]]]; try trivial.
         constructor. admit. admit.
      rewrite AftExt2 in AftExt22. apply eq_sym in AftExt22. inv AftExt22.
         exists ((d23',d12'), m2').
         exists st1'. exists st3'.
         split. apply AftExt1. 
         split. apply AftExt3. 
         assert (ZZ:= intro_compose_match_state _ _ _ _ _ _ _ _ _ _ CMS12' CMS23'). 
            simpl in ZZ. apply ZZ.
 Qed. 

  (* The proof that inject forward simulations compose *)
  Lemma forward_simulation_inject_inject_compose :
    Sim_inj.Forward_simulation_inject Sem1 Sem3 ge1 ge3 entry_points13.
  Proof.
    intros. 
    eapply (@Sim_inj.Build_Forward_simulation_inject G1 C1 G3 C3 Sem1 Sem3 ge1 ge3
              entry_points13 data13 numpasses13 compose_match_state). (* with (core_ord:=sem_compose_ord).*)
      eapply compose_match_state_numpasses; eauto.
(*      apply well_founded_sem_compose_ord.*)
      eapply wf_clos_trans. apply well_founded_sem_compose_ord.
      apply compose_match_state_siminj.
      eapply compose_core_diagram; eauto.
      eapply compose_core_initial; eauto.
      eapply compose_safely_halted; eauto.
      eapply compose_at_external; eauto.
      eapply compose_after_external; eauto.
  Qed.

End ForwardSimInjectInjectCompose.


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

Section ForwardSimExtendInjectCompose.
  Context {G1 C1 G2 C2 G3 C3:Type}.
  Variable Sem1 : CompcertCoreSem G1 C1.
  Variable Sem2 : CompcertCoreSem G2 C2.
  Variable Sem3 : CompcertCoreSem G3 C3.
  Variable ge1 : G1.
  Variable ge2 : G2.
  Variable ge3 : G3.

  Variable entry_points12 : list (val*val*signature).
  Variable entry_points23 : list (val*val*signature).
  Variable FSim12 : Sim_ext.Forward_simulation_extends Sem1 Sem2 ge1 ge2 entry_points12.
  Variable FSim23 : Sim_inj.Forward_simulation_inject Sem2 Sem3 ge2 ge3 entry_points23.

  Variable entry_points13: list (val*val*signature).
  Variable EPC: entry_points_compose entry_points12 entry_points23 entry_points13.

  Let data13 := ((Sim_inj.core_data FSim23 * Sim_ext.core_data FSim12) * mem )%type.

  Let numpasses13 := ((Sim_inj.num_passes FSim12) + (Sim_ext.num_passes FSim23))%nat. 

  Definition sem_compose_ord (x y: data13) := (lex_ord (Sim_inj.core_ord FSim23) (Sim_inj.core_ord FSim12)) (fst x) (fst y).
(*  Definition well_founded_sem_compose_ord := wf_lex_ord (Sim_inj.core_ord_wf FSim23) (Sim_inj.core_ord_wf FSim12).*)
  Definition wf1:=  wf_lex_ord (Sim_inj.core_ord_wf FSim23) (Sim_inj.core_ord_wf FSim12).

  Definition well_founded_sem_compose_ord: well_founded sem_compose_ord.
       unfold sem_compose_ord.
       assert (ZZ:= @wf_inverse_rel data13 _ _ (fun a b => fst a = b) wf1).
       simpl in ZZ.
       assert (HH: (fun x y : data13 =>
        exists2 b : Sim_inj.core_data FSim23 * Sim_inj.core_data FSim12,
          fst x = b &
          forall c : Sim_inj.core_data FSim23 * Sim_inj.core_data FSim12,
          fst y = c ->
          lex_ord (Sim_inj.core_ord FSim23) (Sim_inj.core_ord FSim12) b c)
        = (fun x y : data13 =>
   lex_ord (Sim_inj.core_ord FSim23) (Sim_inj.core_ord FSim12) (fst x)
     (fst y))).
         extensionality x. extensionality y. apply prop_ext.
         split; intros. destruct x; destruct y; simpl in *. destruct H. subst. apply H0. trivial.
             destruct x; destruct y; simpl. exists p. trivial. intros. subst. simpl in *. trivial.
     rewrite HH in ZZ. apply ZZ.
   Qed.
(*
  Definition well_founded_sem_compose_ord := wf_lex_ord (Sim_inj.core_ord_wf FSim23) (Sim_inj.core_ord_wf FSim12).*)

  Inductive compose_match_state : data13 -> list meminj -> C1 -> mem -> C3 -> mem -> Prop :=
    intro_compose_match_state : 
      forall d12 js1 js2 c2 m2 d23 c1 m1 c3 m3,
      Sim_inj.match_state FSim12 d12 js1 c1 m1 c2 m2 -> 
      Sim_inj.match_state FSim23 d23 js2 c2 m2 c3 m3 -> 
      compose_match_state ((d23,(*(Some c2,(js1,ms1++ms2,js2),*)d12),m2) (js1 ++ js2) c1 m1 c3 m3.
      (*compose_match_state (d23,(*(Some c2,m2),*)d12) (js1 ++ js2) c1 m1 c3 m3.*)

  Lemma compose_match_state_numpasses: 
        forall (cd : data13) (js : list meminj) (c1 : C1) (m1 : mem) (c3 : C3) (m3 : mem),
        compose_match_state cd js c1 m1 c3 m3 -> length js = numpasses13.
    Proof.
      intros.
      inv H. unfold numpasses13. 
      rewrite <- (Sim_inj.match_state_num_passes _ _ _ _ _ _ _ H0).
      rewrite <- (Sim_inj.match_state_num_passes _ _ _ _ _ _ _ H1).
      rewrite app_length. reflexivity.
    Qed.
  Theorem forward_simulation_extend_inject_compose :
          Sim_inj.Forward_simulation_inject Sem1 Sem3 ge1 ge3 entry_points13.
    intros. 
    eapply (@Sim_inj.Build_Forward_simulation_inject G1 C1 G3 C3 Sem1 Sem3 ge1 ge3
              entry_points13).
    eapply (@Sim_inj.Build_Forward_simulation_inject G1 C1 G3 C3 Sem1 Sem3 ge1 ge3
              entry_points13 data13 numpasses13 compose_match_state). (* with (core_ord:=sem_compose_ord).*)
      eapply compose_match_state_numpasses; eauto.
(*      apply well_founded_sem_compose_ord.*)
      eapply wf_clos_trans. apply well_founded_sem_compose_ord.
      apply compose_match_state_siminj.
      eapply compose_core_diagram; eauto.
      eapply compose_core_initial; eauto.
      eapply compose_safely_halted; eauto.
      eapply compose_at_external; eauto.
      eapply compose_after_external; eauto.
  Qed.


  Admitted.

  (* The proof that equal inject forward simulations compose *)
  Theorem forward_simulation_equal_inject_compose : forall
    (G1 C1 G2 C2 G3 C3:Type)
    (Sem1 : CompcertCoreSem G1 C1)
    (Sem2 : CompcertCoreSem G2 C2)
    (Sem3 : CompcertCoreSem G3 C3)

    (ge1 : G1)
    (ge2 : G2)
    (ge3 : G3)

    (entry_points12 : list (val*val*signature))
    (entry_points23 : list (val*val*signature))

    (FSim12 : Sim_eq.Forward_simulation_equals Sem1 Sem2 ge1 ge2 entry_points12)
    (FSim23 : Sim_inj.Forward_simulation_inject Sem2 Sem3 ge2 ge3 entry_points23)

    (entry_points13: list (val*val*signature))
    (EPC: entry_points_compose entry_points12 entry_points23 entry_points13),

    Sim_inj.Forward_simulation_inject Sem1 Sem3 ge1 ge3 entry_points13.
  Admitted.
End Sim_proof.


  Lemma compose_after_external: 
        forall (cd : data13) (js js' : list meminj) st1 st3 m1 ms e vals1 ret1 rets 
                m1' ms' m3 m3' ret3
               (CIL: Sim_inj.check_injectlist js m1 ms m3)
               (CMS: compose_match_state cd js st1 m1 st3 m3)
               (AtExt1: at_external Sem1 st1 = Some (e, vals1))
               (Incr: Forall2 inject_incr js js')
               (Sep13: inject_separated (injlist_compose js) (injlist_compose js') m1 m3)
               (CIL': Sim_inj.check_injectlist js' m1' ms' m3')
               (RET': Sim_inj.check_returns js' ret1 rets ret3)
               (MSQ: Sim_inj.mem_square js m1 ms m1' ms')
               (Tp3: Val.has_type ret3 (proj_sig_res (ef_sig e))),
        exists cd', exists st1', exists st3',
          after_external Sem1 ret1 st1 = Some st1' /\
          after_external Sem3 ret3 st3 = Some st3' /\
          compose_match_state cd' js' st1' m1' st3' m3'.
  Proof.
    intros.
    inv CMS. rename c2 into st2. rename H into CMS12. rename H0 into CMS23. 
    destruct (Sim_inj.core_at_external _ _ _ _ _ _ _ _ _ CMS12 AtExt1) 
          as [ms1 [CIL1 [vals2 [VI2 [ArgTp2 AtExt2]]]]].
    destruct (Sim_inj.core_at_external _ _ _ _ _ _ _ _ _ CMS23 AtExt2) 
          as [ms2 [CIL2 [vals3 [VI3 [ArgTp3 AtExt3]]]]].
    apply injlist_incr_split in Incr. destruct Incr as [js1' [js2' [XX [Incr1 Incr2]]]]. subst.
    apply check_injectlist_split in CIL.
    destruct CIL as (*[[NIL CIL2] |*) [M1 [M2 [m [M [CCIL1 CCIL2]]]]]. subst.
    assert (X1 := check_injectlist_inject _ _ _ _ CCIL1).
    destruct X1 as [[? [? ?]] | [? ?]].
     (*js1 = nil*) subst. inv Incr1. simpl in *.
       destruct (Sim_inj.core_at_external FSim12 _ _ _ _ _ _ _ _ CMS12 AtExt1) 
          as [ms1 [CIL1 [vals2 [VI2 [Tp2 AtExt2]]]]].
       destruct ms1; try contradiction. simpl in *. subst.  
       assert (X1 :=  Sim_inj.core_after_external FSim12 d12 nil nil st1 st2 
               m2 nil e vals1 ret1 nil m1' nil _ m1' ret1 (eq_refl _) CMS12).
       destruct X1 as [d12' [st1' [st2' [AftExt1 [AftExt2 CMS12']]]]]; simpl; try trivial.
         intros b; intros. inv H.
         apply Sim_inj.mem_square_mem_forward in MSQ. apply MSQ.
         eapply check_returns_types; eauto.
       assert (X2 := Sim_inj.core_after_external FSim23 d23 js2 js2' st2 st3 m2 M2 e
                     vals2 ret1 rets m1' ms' m3 m3' ret3).
       destruct X2 as [d23' [stss' [st3' [AftExt22 [AftExt3 CMS23']]]]]; simpl; try trivial.
       rewrite AftExt2 in AftExt22. apply eq_sym in AftExt22. inv AftExt22.
       eexists. (*exists ((d23',d12'), m2').*)
       exists st1'. exists st3'.
       split. apply AftExt1. 
       split. apply AftExt3. 
       assert (ZZ:= intro_compose_match_state _ _ _ _ _ _ _ _ _ _ CMS12' CMS23'). 
          simpl in ZZ. apply ZZ. 
    (*Case js1 = cons *)
       destruct (Sim_inj.check_injectlist_D _ _ _ _ CCIL1) as [Length1 Lst1].
       assert (X:= check_injectlist_DTail _ _ _ _ CCIL1).
       destruct X as [[? [? ?]] | [JJ1 [j1 [MM1 [? ?]]]]]. subst. exfalso. apply H.  trivial. subst. clear H.
       destruct (Sim_inj.core_at_external FSim12 _ _ _ _ _ _ _ _ CMS12 AtExt1) as [ms1 [CIL1 [vals2 [VI1 [ValTp2 AtExt2]]]]].
       assert (X:= check_injectlist_split _ _ _ _ _ CIL'). destruct X as [M1' [M2' [m' [X [CIL1' CIL2']]]]]. subst.
       assert (X1:= check_injectlist_DTail _ _ _ _ CIL').
       destruct X1 as [[? _] | [JJ' [j' [MM' [X Y]]]]].
          apply app_eq_nil in H. destruct H; subst. inv Incr1. apply eq_sym in H1. apply app_eq_nil in H1. destruct H1. inv H1.
       apply check_returns_split in RET'. destruct RET' as [rets12' [rets23' [ret2 [XX [RET12' RET23']]]]]. subst.
       rewrite X in *. rewrite Y in *. 
       assert (X1 :=  Sim_inj.core_after_external FSim12 d12 (JJ1 ++ j1 :: nil) js1' st1 st2 m1 ms1
                e vals1 ret1 rets12' m1' M1' m2 m' ret2 CIL1 CMS12 AtExt1 Incr1).
       destruct X1 as [d12' [st1' [st2' [AftExt1 [AftExt2 CMS12']]]]]; simpl; try trivial.
          admit.
         (*memsquare_splits*) apply mem_square_l in MSQ. trivial.
                               apply eq_sym. eapply (Sim_inj.check_injectlist_D _ _ _ _ CCIL1).
                               apply eq_sym. rewrite <- (Forall2_length _ _ _ Incr1). apply (Sim_inj.check_injectlist_D _ _ _ _ CCIL1').
         (*hastype*) eapply check_returns_types. apply Tp3. apply CR23.
       assert (X2 := check_injectlist_inject _ _ _ _ CCIL2).
       destruct X2 as [[? [? ?]] | [? ?]].
       (*js2 = nil*) subst. inv Incr2. repeat rewrite app_nil_r in *. simpl in *.
         destruct (Sim_inj.core_at_external FSim23 _ _ _ _ _ _ _ _ CMS23 AtExt2) 
           as [ms2 [CIL2 [vals3 [VI3 [Tp33 AtExt3]]]]].
         destruct ms2; try contradiction. simpl in *. subst.  
       destruct X1 as [d12' [st1' [st2' [AftExt1 [AftExt2 CMS12']]]]]; simpl; try trivial.
         assert (X2 :=  Sim_inj.core_after_external FSim23 d23 nil nil st2 st3
                 m3 nil e vals2). ret1 nil _ nil _ m3 m3' (eq_refl _) CMS23).
         destruct X1 as [d12' [st1' [st2' [AftExt1 [AftExt2 CMS12']]]]]; simpl; try trivial.
           intros b; intros. inv H.
           apply Sim_inj.mem_square_mem_forward in MSQ. apply MSQ.
           eapply check_returns_types; eauto.
         assert (X2 := Sim_inj.core_after_external FSim23 d23 js2 js2' st2 st3 m2 M2 e
                       vals2 ret1 rets m1' ms' m3 m3' ret3).
         destruct X2 as [d23' [stss' [st3' [AftExt22 [AftExt3 CMS23']]]]]; simpl; try trivial.
         rewrite AftExt2 in AftExt22. apply eq_sym in AftExt22. inv AftExt22.
         eexists. (*exists ((d23',d12'), m2').*)
         exists st1'. exists st3'.
         split. apply AftExt1. 
         split. apply AftExt3. 
         assert (ZZ:= intro_compose_match_state _ _ _ _ _ _ _ _ _ _ CMS12' CMS23'). 
            simpl in ZZ. apply ZZ. 


       clear CIL1 ms1.
       
 (*       assert (exists N1, exists n, ms1 = N1 ++ n :: nil). admit. destruct H as [N1 [n HH]]. subst.
 *)
       destruct (Sim_inj.core_at_external FSim23 _ _ _ _ _ _ _ _ CMS23 AtExt2) as [ms2 [CIL2 [vals3 [VI2 [ValTp3 AtExt3]]]]]. 
       clear CIL2 ms2.
       (*  clear CIL1 Hm2 ms1. xx clear CIL1 ms1.*) (* destruct ms1; try contradiction. clear CIL1. inv Incr1. simpl in *.*)
       (*rewrite Hm3 in *. clear Hm3.*)
       apply check_returns_split in RET'. destruct RET' as [rets12 [rets23 [ret2 [R [CR12 CR23]]]]]. subst.
       apply check_injectlist_split in CIL'.
       destruct CIL' as (*[[NIL CIL2] |*) [M1' [M2' [m2' [M' [CCIL1' CCIL2']]]]]. subst.
       assert (X1 :=  Sim_inj.core_after_external FSim12 d12 js1 js1' st1 st2 m1 M1 (*(M1 ++ m :: nil)*)
                e vals1 ret1 rets12 m1' M1' m2 m2' ret2).
       destruct X1 as [d12' [st1' [st2' [AftExt1 [AftExt2 CMS12']]]]]; simpl; try trivial.
        (*inject_separared_splits*) admit.
        (*memsquare_splits*) apply mem_square_l in MSQ. trivial.
                               apply eq_sym. eapply (Sim_inj.check_injectlist_D _ _ _ _ CCIL1).
                               apply eq_sym. rewrite <- (Forall2_length _ _ _ Incr1). apply (Sim_inj.check_injectlist_D _ _ _ _ CCIL1').
         (*hastype*) eapply check_returns_types. apply Tp3. apply CR23.
       assert (X2 :=  Sim_inj.core_after_external FSim23 d23 js2 js2' st2 st3 m2 M2 e
                     vals2 ret2 rets23 m2' M2' m3 m3' ret3).

       destruct (Sim_inj.check_injectlist_D _ _ _ _ CCIL1) as [L1 _].
       destruct (Sim_inj.check_injectlist_D _ _ _ _ CCIL1') as [L1' _].
       assert (LL' := Forall2_length _ _ _ Incr1). 
       destruct X2 as [d23' [stss' [st3' [AftExt22 [AftExt3 CMS23']]]]]; simpl; try trivial.
           (*inject_separared_splits*) admit.
           (*memsquare_splits*) 
              destruct (check_injectlist_DTail _ _ _ _ CCIL1) as [[? [? ?]] | [J1 [j1 [MM1 [? ?]]]]]; subst; simpl in *.
                destruct (check_injectlist_DTail _ _ _ _ CCIL1') as [[? [? ?]] | [J1' [j1' [MM1' [? ?]]]]]; subst; simpl in *; try congruence.
                inv Incr1. apply eq_sym in H. apply app_eq_nil in H. destruct H; congruence.
              destruct (check_injectlist_DTail _ _ _ _ CCIL1') as [[? [? ?]] | [J1' [j1' [MM1' [? ?]]]]]; subst; simpl in *; try congruence.
                inv Incr1. apply eq_sym in H0. apply app_eq_nil in H0. destruct H0; congruence.              
              apply (mem_square_r J1 MM1 MM1' m1 m1' _ _ _ j1).
                 simpl in *. clear - MSQ. repeat rewrite <- app_assoc in MSQ. simpl in MSQ. apply MSQ.
                 repeat rewrite app_length in L1. simpl in L1. 
                     repeat  rewrite <- (plus_comm 1) in L1. simpl in L1. inv L1. trivial. 
                 repeat rewrite app_length in L1'. simpl in L1'. 
                     repeat  rewrite <- (plus_comm 1) in L1'. simpl in L1'. inv L1'. trivial. 
                 rewrite H0. repeat rewrite app_length in LL'. simpl in LL'. 
                     repeat  rewrite <- (plus_comm 1) in LL'. simpl in LL'. inv LL'. trivial. 
       
       exists (d23',d12'). exists st1'. exists st3'.
       split. apply AftExt1.
       rewrite AftExt2 in AftExt22. apply eq_sym in AftExt22. inv AftExt22. 
       split. apply AftExt3. 
       assert (ZZ:= intro_compose_match_state _ _ _ _ _ _ _ _ _ _ CMS12' CMS23'). 
           apply ZZ.
  Qed.

  Lemma compose_after_external: 
        forall (cd : data13) (js js' : list meminj) st1 st3 m1 ms e vals1 ret1 rets 
                m1' ms' m3 m3' ret3
               (CIL: Sim_inj.check_injectlist js m1 ms m3)
               (CMS: compose_match_state cd js st1 m1 st3 m3)
               (AtExt1: at_external Sem1 st1 = Some (e, vals1))
               (Incr: Forall2 inject_incr js js')
               (Sep13: inject_separated (injlist_compose js) (injlist_compose js') m1 m3)
               (CIL': Sim_inj.check_injectlist js' m1' ms' m3')
               (RET': Sim_inj.check_returns js' ret1 rets ret3)
               (MSQ: Sim_inj.mem_square js m1 ms m1' ms')
               (Tp3: Val.has_type ret3 (proj_sig_res (ef_sig e))),
        exists cd', exists st1', exists st3',
          after_external Sem1 ret1 st1 = Some st1' /\
          after_external Sem3 ret3 st3 = Some st3' /\
          compose_match_state cd' js' st1' m1' st3' m3'.
  Proof.
    intros.
    inv CMS. rename c2 into st2. rename H into CMS12. rename H0 into CMS23. 
    apply injlist_incr_split in Incr. destruct Incr as [js1' [js2' [XX [Incr1 Incr2]]]]. subst.
    apply check_injectlist_split in CIL.
    destruct CIL as (*[[NIL CIL2] |*) [M1 [M2 [m [M [CCIL1 CCIL2]]]]]. subst.
    assert (X1 := check_injectlist_inject _ _ _ _ CCIL1).
    destruct X1 as [[? [? ?]] | [? ?]].
     (*js1 = nil*) subst. inv Incr1. simpl in *.
assert (m=m2). admit.
    (*Case js1 = nil
       subst. simpl in *.
       destruct (Sim_inj.core_at_external FSim12 _ _ _ _ _ _ _ _ CMS12 AtEXt1) 
          as [ms1 [CIL1 [vals2 [VI2 [Tp2 AtEXt2]]]]].
       destruct ms1; try contradiction. simpl in *. subst.  inv Incr1. simpl in *.
       assert (X1 :=  Sim_inj.core_after_external FSim12 d12 nil nil st1 st2 
               m2 nil e vals1 ret1 nil m1' nil _ m1' ret1 (eq_refl _) CMS12).
       destruct X1 as [d12' [st1' [st2' [AftEXt1 [AftEXt2 CMS12']]]]]; simpl; try trivial.
         intros b; intros. inv H.
         apply Sim_inj.mem_square_mem_forward in MSQ. apply MSQ.
         eapply check_returns_types; eauto.
       assert (X2 := Sim_inj.core_after_external FSim23 d23 js2 js2' st2 st3 m2 ms e
                     vals2 ret1 rets m1' ms' m3 m3' ret3).
       destruct X2 as [d23' [stss' [st3' [AftEXt22 [AftEXt3 CMS23']]]]]; simpl; try trivial.
       rewrite AftEXt2 in AftEXt22. apply eq_sym in AftEXt22. inv AftEXt22.
       exists (d23',d12').
       exists st1'. exists st3'.
       split. apply AftEXt1. 
       split. apply AftEXt3. 
       assert (ZZ:= intro_compose_match_state _ _ _ _ _ _ _ _ _ _ CMS12' CMS23'). 
          simpl in ZZ. apply ZZ. 
    Case js1 = cons *)
       subst.
       destruct (Sim_inj.core_at_external FSim12 _ _ _ _ _ _ _ _ CMS12 AtExt1) as [ms1 [CIL1 [vals2 [VI1 [ValTp2 AtExt2]]]]]. 
       clear CIL1 ms1.
       
 (*       assert (exists N1, exists n, ms1 = N1 ++ n :: nil). admit. destruct H as [N1 [n HH]]. subst.
 *)
       destruct (Sim_inj.core_at_external FSim23 _ _ _ _ _ _ _ _ CMS23 AtExt2) as [ms2 [CIL2 [vals3 [VI2 [ValTp3 AtExt3]]]]]. 
       clear CIL2 ms2.
       (*  clear CIL1 Hm2 ms1. xx clear CIL1 ms1.*) (* destruct ms1; try contradiction. clear CIL1. inv Incr1. simpl in *.*)
       (*rewrite Hm3 in *. clear Hm3.*)
       apply check_returns_split in RET'. destruct RET' as [rets12 [rets23 [ret2 [R [CR12 CR23]]]]]. subst.
       apply check_injectlist_split in CIL'.
       destruct CIL' as (*[[NIL CIL2] |*) [M1' [M2' [m2' [M' [CCIL1' CCIL2']]]]]. subst.
       assert (X1 :=  Sim_inj.core_after_external FSim12 d12 js1 js1' st1 st2 m1 M1 (*(M1 ++ m :: nil)*)
                e vals1 ret1 rets12 m1' M1' m2 m2' ret2).
       destruct X1 as [d12' [st1' [st2' [AftExt1 [AftExt2 CMS12']]]]]; simpl; try trivial.
        (*inject_separared_splits*) admit.
        (*memsquare_splits*) apply mem_square_l in MSQ. trivial.
                               apply eq_sym. eapply (Sim_inj.check_injectlist_D _ _ _ _ CCIL1).
                               apply eq_sym. rewrite <- (Forall2_length _ _ _ Incr1). apply (Sim_inj.check_injectlist_D _ _ _ _ CCIL1').
         (*hastype*) eapply check_returns_types. apply Tp3. apply CR23.
       assert (X2 :=  Sim_inj.core_after_external FSim23 d23 js2 js2' st2 st3 m2 M2 e
                     vals2 ret2 rets23 m2' M2' m3 m3' ret3).

       destruct (Sim_inj.check_injectlist_D _ _ _ _ CCIL1) as [L1 _].
       destruct (Sim_inj.check_injectlist_D _ _ _ _ CCIL1') as [L1' _].
       assert (LL' := Forall2_length _ _ _ Incr1). 
       destruct X2 as [d23' [stss' [st3' [AftExt22 [AftExt3 CMS23']]]]]; simpl; try trivial.
           (*inject_separared_splits*) admit.
           (*memsquare_splits*) 
              destruct (check_injectlist_DTail _ _ _ _ CCIL1) as [[? [? ?]] | [J1 [j1 [MM1 [? ?]]]]]; subst; simpl in *.
                destruct (check_injectlist_DTail _ _ _ _ CCIL1') as [[? [? ?]] | [J1' [j1' [MM1' [? ?]]]]]; subst; simpl in *; try congruence.
                inv Incr1. apply eq_sym in H. apply app_eq_nil in H. destruct H; congruence.
              destruct (check_injectlist_DTail _ _ _ _ CCIL1') as [[? [? ?]] | [J1' [j1' [MM1' [? ?]]]]]; subst; simpl in *; try congruence.
                inv Incr1. apply eq_sym in H0. apply app_eq_nil in H0. destruct H0; congruence.              
              apply (mem_square_r J1 MM1 MM1' m1 m1' _ _ _ j1).
                 simpl in *. clear - MSQ. repeat rewrite <- app_assoc in MSQ. simpl in MSQ. apply MSQ.
                 repeat rewrite app_length in L1. simpl in L1. 
                     repeat  rewrite <- (plus_comm 1) in L1. simpl in L1. inv L1. trivial. 
                 repeat rewrite app_length in L1'. simpl in L1'. 
                     repeat  rewrite <- (plus_comm 1) in L1'. simpl in L1'. inv L1'. trivial. 
                 rewrite H0. repeat rewrite app_length in LL'. simpl in LL'. 
                     repeat  rewrite <- (plus_comm 1) in LL'. simpl in LL'. inv LL'. trivial. 
       
       exists (d23',d12'). exists st1'. exists st3'.
       split. apply AftExt1.
       rewrite AftExt2 in AftExt22. apply eq_sym in AftExt22. inv AftExt22. 
       split. apply AftExt3. 
       assert (ZZ:= intro_compose_match_state _ _ _ _ _ _ _ _ _ _ CMS12' CMS23'). 
           apply ZZ.
  Qed.

 xx

       assert (inject_separated (injlist_compose js2) (injlist_compose js2') m2 m3).
          (*inject_separared_splits m2*)
          intros b; intros. clear CR12 CR23 ValTp2 ValTp3 VI2 VI1 Tp3.
          clear AtExt1 AtExt2 AtExt3.
             destruct (check_injectlist_inject _ _ _ _ CCIL2) as [[? [? ?]] | [nonNil2 Inj2]].
               subst; simpl in *. inv H.
             destruct (check_injectlist_inject _ _ _ _ CCIL2') as [[? [? ?]] | [nonNil2' Inj2']].
               subst; simpl in *. inv Incr2. congruence.
            destruct Inj2'. xxunfold Sim_inj.mem_square in MSQ. destruct mi_inj.
             apply Sim_inj.mem_square_mem_forward in MSQ. 
             specialize (Sep13 b). repeat rewrite injlist_compose_app in Sep13.
             remember (injlist_compose js2' b2) as z2'.
             destruct z2'; apply eq_sym in Heqz2'.
                destruct p as [b3 d3].
                specialize (Sep13 b3 (delta + d3)).  unfold inj_compose in Sep13.
                rewrite H in Sep13. rewrite H0 in Sep13. rewrite Heqz2' in Sep13.
                destruct Sep13; trivial.
                split; trivial.
                intros Hyp.
                remember (injlist_compose js2 b2) as z2.
                destruct z2; apply eq_sym in Heqz2. 
                   destruct p as [b33 d33]. apply injlist_compose_inj_incr in Incr2.
                   assert (QQ:= Incr2 _ _ _ Heqz2). rewrite Heqz2' in QQ. apply eq_sym in QQ. inv QQ.
                   destruct Inj2. apply mi_mappedblocks in Heqz2.  apply (H2 Heqz2).
                 
          destruct (check_injectlist_inject _ _ _ _ CCIL1') as [[? [? ?]] | [nonNil1' Inj1']].
             subst; simpl in *.
             inv Incr1. simpl in *. inv H.
          (*Cons case: have Inj1'*)
             destruct (check_injectlist_inject _ _ _ _ CCIL1) as [[? [? ?]] | [nonNil1 Inj1]].
             subst; simpl in *. inv Incr1. congruence.
          destruct (check_injectlist_inject _ _ _ _ CCIL2') as [[? [? ?]] | [nonNil2' Inj2']].
             subst; simpl in *.
             inv Incr2. simpl in *. destruct M2; try contradiction.  subst. 
             repeat rewrite app_nil_r in *.
             eapply Sep13. apply H. apply H0.
          (*Cons case: have Inj2'*)
             destruct (check_injectlist_inject _ _ _ _ CCIL2) as [[? [? ?]] | [nonNil2 Inj2]].
             subst; simpl in *. inv Incr2. congruence.
             apply Sim_inj.mem_square_mem_forward in MSQ. 
             specialize (Sep13 b). repeat rewrite injlist_compose_app in Sep13.
             remember (injlist_compose js2' b2) as z2'.
             destruct z2'; apply eq_sym in Heqz2'.
                destruct p as [b3 d3].
                specialize (Sep13 b3 (delta + d3)).  unfold inj_compose in Sep13.
                rewrite H in Sep13. rewrite H0 in Sep13. rewrite Heqz2' in Sep13.
                destruct Sep13; trivial.
                split; trivial.
                intros Hyp.
                remember (injlist_compose js2 b2) as z2.
                destruct z2; apply eq_sym in Heqz2. 
                   destruct p as [b33 d33]. apply injlist_compose_inj_incr in Incr2.
                   assert (QQ:= Incr2 _ _ _ Heqz2). rewrite Heqz2' in QQ. apply eq_sym in QQ. inv QQ.
                   destruct Inj2. apply mi_mappedblocks in Heqz2.  apply (H2 Heqz2).
                 
                
       assert (X1 :=  Sim_inj.core_after_external FSim12 d12 js1 js1' st1 st2 m1 M1 (*(M1 ++ m :: nil)*)
                e vals1 ret1 rets12 m1' M1' m2 m2' ret2).
       destruct X1 as [d12' [st1' [st2' [AftExt1 [AftExt2 CMS12']]]]]; simpl; try trivial.
      (*inject_separared_splits*)
          intros b; intros. clear CR12 CR23 ValTp2 ValTp3 VI2 VI1 Tp3.
          clear AtExt1 AtExt2 AtExt3.
          destruct (check_injectlist_inject _ _ _ _ CCIL1') as [[? [? ?]] | [nonNil1' Inj1']].
             subst; simpl in *.
             inv Incr1. simpl in *. inv H.
          (*Cons case: have Inj1'*)
             destruct (check_injectlist_inject _ _ _ _ CCIL1) as [[? [? ?]] | [nonNil1 Inj1]].
             subst; simpl in *. inv Incr1. congruence.
          destruct (check_injectlist_inject _ _ _ _ CCIL2') as [[? [? ?]] | [nonNil2' Inj2']].
             subst; simpl in *.
             inv Incr2. simpl in *. destruct M2; try contradiction.  subst. 
             repeat rewrite app_nil_r in *.
             eapply Sep13. apply H. apply H0.
          (*Cons case: have Inj2'*)
             destruct (check_injectlist_inject _ _ _ _ CCIL2) as [[? [? ?]] | [nonNil2 Inj2]].
             subst; simpl in *. inv Incr2. congruence.
             apply Sim_inj.mem_square_mem_forward in MSQ. 
             specialize (Sep13 b). repeat rewrite injlist_compose_app in Sep13.
             remember (injlist_compose js2' b2) as z2'.
             destruct z2'; apply eq_sym in Heqz2'.
                destruct p as [b3 d3].
                specialize (Sep13 b3 (delta + d3)).  unfold inj_compose in Sep13.
                rewrite H in Sep13. rewrite H0 in Sep13. rewrite Heqz2' in Sep13.
                destruct Sep13; trivial.
                split; trivial.
                intros Hyp.
                remember (injlist_compose js2 b2) as z2.
                destruct z2; apply eq_sym in Heqz2. 
                   destruct p as [b33 d33]. apply injlist_compose_inj_incr in Incr2.
                   assert (QQ:= Incr2 _ _ _ Heqz2). rewrite Heqz2' in QQ. apply eq_sym in QQ. inv QQ.
                   destruct Inj2. apply mi_mappedblocks in Heqz2.  apply (H2 Heqz2).
                 
                

destruct mi_inj.
                specialize (Sep13 b3 (delta + d3)).  unfold inj_compose in Sep13.
                rewrite H in Sep13. rewrite H0 in Sep13. rewrite Heqz2' in Sep13.
                destruct Sep13; trivial.
                split; trivial.
                intros Hyp. destruct Inj2.
                  
unfold Sim_inj.mem_square in MSQ.
             
             inv Incr1. simpl in *. inv H.
          (*Cons case: have Inj1'*)
             

            apply Sim_inj.match_state_siminj in CMS12. destruct CMS12 as [CC1 CC2].

            apply Sim_inj.match_state_siminj in CMS23. 
          clear VI2 AtExt2 AtExt3 ValTp2 ValTp3 Tp3 AtExt1 CMS12 CMS23 CR12 CR23.
             intros b; intros. unfold Sim_inj.check_injectlist in CIL1.*)
         admit.
Sim_inj.mem_square (js1 ++ js2) m1 (M1 ++ M2) m1' (M1' ++ M2')
Sim_inj.mem_square js1 m1 ms1 m1' M1'
         (*mem_square_splits*) unfold Sim_inj.mem_square. intros b.  admit.
         eapply check_returns_types. apply Tp3. apply CR23.
       assert (X2 :=  Sim_inj.core_after_external FSim23 d23 js2 js2' st2 st3 m2 ms2 e
                     vals2 ret2 rets23 m2' M2' m3 m3' ret3).
       destruct X2 as [d23' [stss' [st3' [AftExt22 [AftExt3 CMS23']]]]]; simpl; try trivial.
           admit. admit.
       exists (d23',d12'). exists st1'. exists st3'.
       split. apply AftExt1.
       rewrite AftExt2 in AftExt22. apply eq_sym in AftExt22. inv AftExt22. 
       split. apply AftExt3. 
       assert (ZZ:= intro_compose_match_state _ _ _ _ _ _ _ _ _ _ CMS12' CMS23'). 
           apply ZZ.
  Qed. xx
  inject_separated (injlist_compose js1) 

 constructor.
 simpl.
       assert (NIL12':= Sim_inj.match_state_nil FSim12 _ _ _ _ _ CMS12'). subst.
 
apply  inv MSQ. unfold constructor.

       exists (d23,d12). exists 
    apply check_injectlist_split in CIL.
    destruct CIL as [[NIL CIL2] | [ms1 [ms2 [mm [M [CIL1 CIL2]]]]]].

assert (X1 :=  Sim_inj.core_after_external FSim12 d12 js1 js1' st1 st2 m1). ms e vals1 ret1 rets m1' ms').ss
    destruct X1 xx
       unfold m3. unfold m2. 
    destruct (Sim_inj.core_at_external FSim12 _ _ _ _ _ _ _ _ CMS12 AtExt1) as [ms1 [Hm2 [CIL1 [vals2 [VI2 [Tp2 AtExt2]]]]]].
    destruct (Sim_inj.core_at_external FSim23 _ _ _ _ _ _ _ _ CMS23 AtExt2) as [ms2 [Hm3 [CIL2 [vals3 [VI3 [Tpp AtExt]]]]]].
    exists (
 vals3' [MemInj2 [ValsInj2 [HasType3 AtExt3']]]].
    rewrite AtExt3 in AtExt3'. apply eq_sym in AtExt3'. inv AtExt3'.
    assert (AftExt1 := Sim_inj.core_after_external_reorder FSim12
      _ _ _ _ _ _ _ _ _ CMS12 MemInj1 AtExt1 AtExt2 ValsInj1 HasType2).
 _ _ j1' _ _ _ _ _ vals1 vals2 ret1 ret3 m1'). m2 CMS12 MemInj1  Incr1').
(*    apply Sim_inj.match_state_siminj in CMS12.
    apply Sim_inj.match_state_siminj in CMS23.*)
(*    unfold inject_separated in InjSep.*)
    destruct (inj_split _ _ _ InjIncr _ _ _ MemInj InjSep MemInj1 MemInj2)
       as [j1' [j2' [Incr1' [Incr2' JJ']]]]; subst.
xx
    unfold at_external in AtExt2. remember (csem Sem2). destruct c; simpl in *. destruct Sem2.
    unfold at_external in AtExt2.
  Qed.

 Admitted. Admitted.

  (* An axiom stating that inject forward simulations compose *)
  Lemma forward_simulation_inject_inject_compose :
    Sim_inj.Forward_simulation_inject Sem1 Sem3 ge1 ge3 entry_points13.
  Proof.
    intros. 
    eapply (@Sim_inj.Build_Forward_simulation_inject G1 C1 G3 C3 Sem1 Sem3 ge1 ge3
              entry_points13 data13 numpasses13 compose_match_state). (* with (core_ord:=sem_compose_ord).*)
      eapply compose_match_state_numpasses; eauto.
(*      apply well_founded_sem_compose_ord.*)
      eapply wf_clos_trans. apply well_founded_sem_compose_ord.
      apply compose_match_state_siminj.
      eapply compose_core_diagram; eauto.
      eapply compose_core_initial; eauto.
      eapply compose_safely_halted; eauto.
      eapply compose_at_external; eauto.
      eapply compose_after_external; eauto.
  Proof.



  Lemma compose_after_external: 
        forall (cd : data13) (js js' : list meminj) st1 st3 m1 ms e vals1 ret1 rets m1' ms',
          let m3 := last ms m1 in
          let ret3 := last rets ret1 in
        forall (CIL: Sim_inj.check_injectlist js m1 ms)
               (CMS: compose_match_state cd js st1 m1 st3 m3)
               (AtExt1: at_external Sem1 st1 = Some (e, vals1))
               (Incr: Forall2 inject_incr js js')
               (Sep13: inject_separated (injlist_compose js) (injlist_compose js') m1 m3),
          let m3' := last ms' m1' in
        forall (CIL': Sim_inj.check_injectlist js' m1' ms')
               (RET': Sim_inj.check_returns js' ret1 rets)
               (MSQ: Sim_inj.mem_square js m1 ms m1' ms')
               (Tp3: Val.has_type ret3 (proj_sig_res (ef_sig e))),
        exists cd', exists st1', exists st3',
          after_external Sem1 ret1 st1 = Some st1' /\
          after_external Sem3 ret3 st3 = Some st3' /\
          compose_match_state cd' js' st1' m1' st3' m3'.
  Proof.
    intros.
    inv CMS. rename c2 into st2. rename H into CMS12. rename H0 into CMS23. 
    apply injlist_incr_split in Incr. destruct Incr as [js1' [js2' [XX [Incr1 Incr2]]]]. subst.
    unfold m3 in *.
    apply check_injectlist_split in CIL.
    destruct CIL as [[NIL CIL2] | [M1 [M2 [m [M [CCIL1 CCIL2]]]]]].
    (*Case js1 = nil*)
       subst. simpl in *.
       destruct (Sim_inj.core_at_externalRob FSim12 _ _ _ _ _ _ _ _ CMS12 AtExt1) 
          as [ms1 [Hm2 [CIL1 [vals2 [VI2 [Tp2 AtExt2]]]]]].
       destruct ms1; try contradiction. clear CIL1. inv Incr1. simpl in *.
       assert (X1 :=  Sim_inj.core_after_externalRob FSim12 d12 nil nil st1 st2 m1 nil e vals1 ret1 nil m1' nil).
       destruct X1 as [d12' [st1' [st2' [AftExt1 [AftExt2 CMS12']]]]].
         constructor.
         apply CMS12. 
         apply AtExt1.
         constructor.
         simpl. (*apply inject_separated_refl.*) intros b; intros. inv H.
         constructor.
         constructor.
         simpl. apply Sim_inj.mem_square_mem_forward in MSQ. apply MSQ.
         simpl. eapply check_returns_types; eauto.
       simpl in *.
       assert (X2 :=  Sim_inj.core_after_externalRob FSim23 d23 js2 js2' st2 st3 m1 ms e
                     vals2 ret1 rets m1' ms').
       destruct X2 as [d23' [stss' [st3' [AftExt22 [AftExt3 CMS23']]]]].
         apply CIL2.
         unfold m3 in *. apply CMS23.
         apply AtExt2. 
         apply Incr2.
         unfold m3 in *. apply Sep13.
         apply CIL'.
         apply RET'.
         apply MSQ.
         unfold ret3 in *. apply Tp3.
       rewrite AftExt2 in AftExt22. apply eq_sym in AftExt22. inv AftExt22.
       eexists. (*exists (d23',d12').*)
       exists st1'. exists st3'.
       split. apply AftExt1. 
       split. unfold ret3 in *. apply AftExt3. 
       assert (ZZ:= intro_compose_match_state _ _ _ _ _ _ _ _ _ _ CMS12' CMS23'). 
          simpl in ZZ. unfold m3' in *. apply ZZ. 
    (*Case js1 = cons*)
       unfold m3 in *. subst.
       destruct (Sim_inj.core_at_externalRob FSim12 _ _ _ _ _ _ _ _ CMS12 AtExt1) as [ms1 [Hm2 [CIL1 [vals2 [VI1 [ValTp2 AtExt2]]]]]]. 
          subst.
 (*       assert (exists N1, exists n, ms1 = N1 ++ n :: nil). admit. destruct H as [N1 [n HH]]. subst.
 *)
       destruct (Sim_inj.core_at_externalRob FSim23 _ _ _ _ _ _ _ _ CMS23 AtExt2) as [ms2 [Hm3 [CIL2 [vals3 [VI2 [ValTp3 AtExt3]]]]]]. 
       simpl in *. subst. (*  clear CIL1 Hm2 ms1. xx clear CIL1 ms1.*) (* destruct ms1; try contradiction. clear CIL1. inv Incr1. simpl in *.*)
       rewrite Hm3 in *. clear Hm3.
       
       assert (X1 :=  Sim_inj.core_after_externalRob FSim12 d12 js1 js1' st1 st2 m1 (M1 ++ m :: nil) e vals1 ret1).
       destruct X1 as [d12' [st1' [st2' [AftExt1 [AftExt2 CMS12']]]]].
         constructor.
       destruct (Sim_inj.core_at_external FSim12 _ _ _ _ _ _ _ _ CMS12 AtExt1) as [INJ1 [vals2 [VI1 [ArgTp2 AtExt2]]]].
          (*Rob .. as [ms1 [Hm2 [CIL1 [vals2 [VI2 [Tp2 AtEXt2]]]]]]. *)
       destruct (Sim_inj.core_at_external FSim23 _ _ _ _ _ _ _ _ CMS23 AtExt2) as [INJ2 [vals3 [VI2 [ArgTp3 AtExt3]]]].
          (*Rob .. as [ms1 [Hm2 [CIL1 [vals2 [VI2 [Tp2 AtEXt2]]]]]]. *)
       simpl in *. subst. (*  clear CIL1 Hm2 ms1. xx clear CIL1 ms1.*) (* destruct ms1; try contradiction. clear CIL1. inv Incr1. simpl in *.*)
       assert (X1 :=  Sim_inj.core_after_externalRob FSim12 d12 js1 js1' st1 st2 m1 (M1 ++ m :: nil) e vals1 ret1). nil m1' nil).xx
       destruct X1 as [d12' [st1' [st2' [AftExt1 [AftExt2 CMS12']]]]].
         constructor.
         apply CMS12. 
         apply AtExt1.
         constructor.
         simpl. (*apply inject_separated_refl.*) intros b; intros. inv H.
         constructor.
         constructor.
         simpl. apply Sim_inj.mem_square_mem_forward in MSQ. apply MSQ.
         simpl. admit. (*pull hastype back through rets*) 
       simpl in *.
       assert (X2 :=  Sim_inj.core_after_external FSim23 d23 js2 js2' st2 st3 m1 ms e
                     vals2 ret1 rets m1' ms').
       destruct X2 as [d23' [stss' [st3' [AftExt22 [AftExt3 CMS23']]]]].
         apply CIL2.
         unfold m3 in *. apply CMS23.
         apply AtExt2. 
         apply Incr2.
         unfold m3 in *. apply Sep13.
         apply CIL'.
         apply RET'.
         apply MSQ.
         unfold ret3 in *. apply Tp3.
       rewrite AftExt2 in AftExt22. apply eq_sym in AftExt22. inv AftExt22.
       exists (d23',d12'). exists st1'. exists st3'.
       split. apply AftExt1. 
       split. unfold ret3 in *. apply AftExt3. 
       assert (ZZ:= intro_compose_match_state _ _ _ _ _ _ _ _ _ _ CMS12' CMS23'). 
          simpl in ZZ. unfold m3' in *. apply ZZ. 
  
  
 constructor.
 simpl.
       assert (NIL12':= Sim_inj.match_state_nil FSim12 _ _ _ _ _ CMS12'). subst.
 
apply  inv MSQ. unfold constructor.

       exists (d23,d12). exists 
    apply check_injectlist_split in CIL.
    destruct CIL as [[NIL CIL2] | [ms1 [ms2 [mm [M [CIL1 CIL2]]]]]].

assert (X1 :=  Sim_inj.core_after_external FSim12 d12 js1 js1' st1 st2 m1). ms e vals1 ret1 rets m1' ms').ss
    destruct X1 xx
       unfold m3. unfold m2. 
    destruct (Sim_inj.core_at_external FSim12 _ _ _ _ _ _ _ _ CMS12 AtExt1) as [ms1 [Hm2 [CIL1 [vals2 [VI2 [Tp2 AtExt2]]]]]].
    destruct (Sim_inj.core_at_external FSim23 _ _ _ _ _ _ _ _ CMS23 AtExt2) as [ms2 [Hm3 [CIL2 [vals3 [VI3 [Tpp AtExt]]]]]].
    exists (
 vals3' [MemInj2 [ValsInj2 [HasType3 AtExt3']]]].
    rewrite AtExt3 in AtExt3'. apply eq_sym in AtExt3'. inv AtExt3'.
    assert (AftExt1 := Sim_inj.core_after_external_reorder FSim12
      _ _ _ _ _ _ _ _ _ CMS12 MemInj1 AtExt1 AtExt2 ValsInj1 HasType2).
 _ _ j1' _ _ _ _ _ vals1 vals2 ret1 ret3 m1'). m2 CMS12 MemInj1  Incr1').
(*    apply Sim_inj.match_state_siminj in CMS12.
    apply Sim_inj.match_state_siminj in CMS23.*)
(*    unfold inject_separated in InjSep.*)
    destruct (inj_split _ _ _ InjIncr _ _ _ MemInj InjSep MemInj1 MemInj2)
       as [j1' [j2' [Incr1' [Incr2' JJ']]]]; subst.
xx
    unfold at_external in AtExt2. remember (csem Sem2). destruct c; simpl in *. destruct Sem2.
    unfold at_external in AtExt2.
  Qed.

 Admitted.

  (* An axiom stating that inject forward simulations compose *)
  Lemma forward_simulation_inject_inject_compose :
    Sim_inj.Forward_simulation_inject Sem1 Sem3 ge1 ge3 entry_points13.
  Proof.
    intros. 
    eapply (@Sim_inj.Build_Forward_simulation_inject G1 C1 G3 C3 Sem1 Sem3 ge1 ge3
              entry_points13 data13 numpasses13 compose_match_state). (* with (core_ord:=sem_compose_ord).*)
      eapply compose_match_state_numpasses; eauto.
(*      apply well_founded_sem_compose_ord.*)
      eapply wf_clos_trans. apply well_founded_sem_compose_ord.
      apply compose_match_state_siminj.
      eapply compose_core_diagram; eauto.
      eapply compose_core_initial; eauto.
      eapply compose_safely_halted; eauto.
 admit.
      eapply compose_at_externalRob; eauto.
 admit.
      eapply compose_after_externalRob; eauto.
  Proof.


  Lemma compose_at_external: forall cd J st1 m1 st3 m3 e vals1
           (CMS: compose_match_state cd J st1 m1 st3 m3)
           (AtExt1: at_external Sem1 st1 = Some (e, vals1)),
        (Mem.inject (injlist_compose J) m1 m3 /\
           exists vals3,
              Forall2 (val_inject (injlist_compose J)) vals1 vals3 /\
              Forall2 Val.has_type vals3 (sig_args (ef_sig e)) /\
              at_external Sem3 st3 = Some (e, vals3)).
  Proof.
    intros.
    inv CMS. rename c2 into st2. rename H into CMS12. rename H0 into CMS23.
    destruct (Sim_inj.core_at_external FSim12 _ _ _ _ _ _ _ _ CMS12 AtExt1) as [Minj1 [vals2 [ValsInj1 [HasType2 AtExt2]]]].
    destruct (Sim_inj.core_at_external FSim23 _ _ _ _ _ _ _ _ CMS23 AtExt2) as [Minj2 [vals3 [ValsInj2 [HasType3 AtExt3]]]].
    split. eapply inject_compose_app. apply Minj1. apply Minj2.
    exists vals3.
    split. rewrite injlist_compose_app. eapply (vals_inject_compose _ _ _ ValsInj1 _ _ ValsInj2).
    split; assumption.
  Qed.
cc

  Lemma compose_after_external: 
        forall (cd : data13) (js js' : list meminj) st1 st3 m1 m3 e vals1 ret1 rets m1' m3',
          let ret3 := last rets ret1 in
        forall (CMS: compose_match_state cd js st1 m1 st3 m3)
               (AtExt1: at_external Sem1 st1 = Some (e, vals1))
               (Incr: Forall2 inject_incr js js')
               (Sep13: inject_separated (injlist_compose js) (injlist_compose js') m1 m3)
               (CIL': Mem.inject (injlist_compose js') m1' m3')
               (RET': Sim_inj.check_returns js' ret1 rets)
               (MSQ: Sim_inj.mem_squareUni js m1 m3 m1' m3')
               (Tp3: Val.has_type ret3 (proj_sig_res (ef_sig e))),
        exists cd', exists st1', exists st3',
          after_external Sem1 ret1 st1 = Some st1' /\
          after_external Sem3 ret3 st3 = Some st3' /\
          compose_match_state cd' js' st1' m1' st3' m3'.
  Proof. intros.
    inv CMS. rename c2 into st2. rename H into CMS12. rename H0 into CMS23. 
    apply injlist_incr_split in Incr. destruct Incr as [js1' [js2' [XX [Incr1 Incr2]]]]. subst.
 (*  apply check_injectlist_split in CIL.
    destruct CIL as [[NIL CIL2] | [M1 [M2 [m [M [CCIL1 CCIL2]]]]]].
    (*Case js1 = nil*)
       subst. simpl in *.
       destruct (Sim_inj.core_at_external FSim12 _ _ _ _ _ _ _ _ CMS12 AtEXt1) 
          as [ms1 [Hm2 [CIL1 [vals2 [VI2 [Tp2 AtEXt2]]]]]].
        destruct ms1; try contradiction. clear CIL1. inv Incr1. simpl in *.
(*      assert (Num1:= Sim_inj.match_state_num_passes _ _ _ _ _ _ _ CMS12). *)
(* simpl in Num1. simpl in numpasses13. rewrite <- Num1 in numpasses13. simpl in *.*)  
(*       assert (NIL12:= Sim_inj.match_state_nil FSim12 _ _ _ _ _ CMS12). subst.*)
       assert (X1 :=  Sim_inj.core_after_external FSim12 d12 nil nil st1 st2 m1 nil e vals1 ret1 nil m1' nil).
       destruct X1 as [d12' [st1' [st2' [AftEXt1 [AftEXt2 CMS12']]]]].
         constructor.
         apply CMS12. 
         apply AtEXt1.
         constructor.
         simpl. (*apply inject_separated_refl.*) intros b; intros. inv H.
         constructor.
         constructor.
         simpl. apply Sim_inj.mem_square_mem_forward in MSQ. apply MSQ.
         simpl. eapply check_returns_types; eauto.
       simpl in *.
       assert (X2 :=  Sim_inj.core_after_external FSim23 d23 js2 js2' st2 st3 m1 ms e
                     vals2 ret1 rets m1' ms').
       destruct X2 as [d23' [stss' [st3' [AftEXt22 [AftEXt3 CMS23']]]]].
         apply CIL2.
         unfold m3 in *. apply CMS23.
         apply AtEXt2. 
         apply Incr2.
         unfold m3 in *. apply Sep13.
         apply CIL'.
         apply RET'.
         apply MSQ.
         unfold ret3 in *. apply Tp3.
       rewrite AftEXt2 in AftEXt22. apply eq_sym in AftEXt22. inv AftEXt22.
       exists (d23',d12'). exists st1'. exists st3'.
       split. apply AftEXt1. 
       split. unfold ret3 in *. apply AftEXt3. 
       assert (ZZ:= intro_compose_match_state _ _ _ _ _ _ _ _ _ _ CMS12' CMS23'). 
          simpl in ZZ. unfold m3' in *. apply ZZ. 
    Case js1 = cons*)
      (* unfold m3 in *. subst. *)
       destruct (Sim_inj.core_at_external FSim12 _ _ _ _ _ _ _ _ CMS12 AtExt1) as [Minj1 [vals2 [VI2 [Tp2 AtExt2]]]].
       assert (X1 :=  Sim_inj.core_after_external FSim12 d12 js1 js1' st1 st2 m1 m2 e vals1 ret1 rets m1').
       unfold 
       assert (Z1:= check_injectlist_split). in CIL'.
    destruct CIL as [[NIL CIL2] | [M1 [M2 [m [M [CCIL1 CCIL2]]]]]].
    (*Case js1 = nil*) destruct X1 as [d12' [st1' [st2' [AftExt1 [AftExt2 CMS12']]]]].
         constructor.
         apply CMS12. 
         apply AtExt1.
         constructor.
         simpl. (*apply inject_separated_refl.*) intros b; intros. inv H.
         constructor.
         constructor.
         simpl. apply Sim_inj.mem_square_mem_forward in MSQ. apply MSQ.
         simpl. admit. (*pull hastype back through rets*) 
       simpl in *.
       assert (X2 :=  Sim_inj.core_after_external FSim23 d23 js2 js2' st2 st3 m1 ms e
                     vals2 ret1 rets m1' ms').
       destruct X2 as [d23' [stss' [st3' [AftExt22 [AftExt3 CMS23']]]]].
         apply CIL2.
         unfold m3 in *. apply CMS23.
         apply AtExt2. 
         apply Incr2.
         unfold m3 in *. apply Sep13.
         apply CIL'.
         apply RET'.
         apply MSQ.
         unfold ret3 in *. apply Tp3.
       rewrite AftExt2 in AftExt22. apply eq_sym in AftExt22. inv AftExt22.
       exists (d23',d12'). exists st1'. exists st3'.
       split. apply AftExt1. 
       split. unfold ret3 in *. apply AftExt3. 
       assert (ZZ:= intro_compose_match_state _ _ _ _ _ _ _ _ _ _ CMS12' CMS23'). 
          simpl in ZZ. unfold m3' in *. apply ZZ. 
  
  
 constructor.
 simpl.
Admitted.  

  (* An axiom stating that inject forward simulations compose *)
  Lemma forward_simulation_inject_inject_compose :
    Sim_inj.Forward_simulation_inject Sem1 Sem3 ge1 ge3 entry_points13.
  Proof.
    intros. 
    eapply (@Sim_inj.Build_Forward_simulation_inject G1 C1 G3 C3 Sem1 Sem3 ge1 ge3 entry_points13 data13 numpasses13 compose_match_state).
      eapply compose_match_state_numpasses; eauto.
      eapply wf_clos_trans. apply well_founded_sem_compose_ord.
      apply compose_match_state_siminj. 
      apply compose_core_diagram.
      intros v1 v3 sig HEntry vals1 c1 m1 MIC1 IM1.
        apply (compose_core_initial v1 v3 sig HEntry vals1 c1 MIC1 m1 IM1).
      eapply compose_safely_halted; eauto.
      eapply compose_at_external; eauto.
      eapply compose_after_external; eauto.
aftertexternalRob.
  Lemma compose_after_externalRob: 
        forall (cd : data13) (js js' : list meminj) st1 st3 m1 ms e vals1 ret1 rets m1' ms',
          let m3 := last ms m1 in
          let ret3 := last rets ret1 in
        forall (CIL: Sim_inj.check_injectlist js m1 ms)
               (CMS: compose_match_state cd js st1 m1 st3 m3)
               (AtExt1: at_external Sem1 st1 = Some (e, vals1))
               (Incr: Forall2 inject_incr js js')
               (Sep13: inject_separated (injlist_compose js) (injlist_compose js') m1 m3),
          let m3' := last ms' m1' in
        forall (CIL': Sim_inj.check_injectlist js' m1' ms')
               (RET': Sim_inj.check_returns js' ret1 rets)
               (MSQ: Sim_inj.mem_square js m1 ms m1' ms')
               (Tp3: Val.has_type ret3 (proj_sig_res (ef_sig e))),x
        exists cd', exists st1', exists st3',
          after_external Sem1 ret1 st1 = Some st1' /\
          after_external Sem3 ret3 st3 = Some st3' /\
          compose_match_state cd' js' st1' m1' st3' m3'.
  Proof. intros.
    inv CMS. rename c2 into st2. rename H into CMS12. rename H0 into CMS23. 
    apply injlist_incr_split in Incr. destruct Incr as [js1' [js2' [XX [Incr1 Incr2]]]]. subst.
    apply check_injectlist_split in CIL.
    destruct CIL as [[NIL CIL2] | [M1 [M2 [m [M [CCIL1 CCIL2]]]]]].
    (*Case js1 = nil*)
       subst. simpl in *.
       destruct (Sim_inj.core_at_external FSim12 _ _ _ _ _ _ _ _ CMS12 AtExt1) 
          as [ms1 [Hm2 [CIL1 [vals2 [VI2 [Tp2 AtExt2]]]]]].
        destruct ms1; try contradiction. clear CIL1. inv Incr1. simpl in *.
(*      assert (Num1:= Sim_inj.match_state_num_passes _ _ _ _ _ _ _ CMS12). *)
(* simpl in Num1. simpl in numpasses13. rewrite <- Num1 in numpasses13. simpl in *.*)  
(*       assert (NIL12:= Sim_inj.match_state_nil FSim12 _ _ _ _ _ CMS12). subst.*)
       assert (X1 :=  Sim_inj.core_after_external FSim12 d12 nil nil st1 st2 m1 nil e vals1 ret1 nil m1' nil).
       destruct X1 as [d12' [st1' [st2' [AftExt1 [AftExt2 CMS12']]]]].
         constructor.
         apply CMS12. 
         apply AtExt1.
         constructor.
         simpl. (*apply inject_separated_refl.*) intros b; intros. inv H.
         constructor.
         constructor.
         simpl. apply Sim_inj.mem_square_mem_forward in MSQ. apply MSQ.
         simpl. eapply check_returns_types; eauto.
       simpl in *.
       assert (X2 :=  Sim_inj.core_after_external FSim23 d23 js2 js2' st2 st3 m1 ms e
                     vals2 ret1 rets m1' ms').
       destruct X2 as [d23' [stss' [st3' [AftExt22 [AftExt3 CMS23']]]]].
         apply CIL2.
         unfold m3 in *. apply CMS23.
         apply AtExt2. 
         apply Incr2.
         unfold m3 in *. apply Sep13.
         apply CIL'.
         apply RET'.
         apply MSQ.
         unfold ret3 in *. apply Tp3.
       rewrite AftExt2 in AftExt22. apply eq_sym in AftExt22. inv AftExt22.
       exists (d23',d12'). exists st1'. exists st3'.
       split. apply AftExt1. 
       split. unfold ret3 in *. apply AftExt3. 
       assert (ZZ:= intro_compose_match_state _ _ _ _ _ _ _ _ _ _ CMS12' CMS23'). 
          simpl in ZZ. unfold m3' in *. apply ZZ. 
    (*Case js1 = cons*)
       unfold m3 in *. subst. 
       destruct (Sim_inj.core_at_external FSim12 _ _ _ _ _ _ _ _ CMS12 AtExt1) 
          as [ms1 [Hm2 [CIL1 [vals2 [VI2 [Tp2 AtExt2]]]]]]. 
       simpl in *. subst.  clear CIL1 Hm2 ms1. xx clear CIL1 ms1. (* destruct ms1; try contradiction. clear CIL1. inv Incr1. simpl in *.*)
       assert (X1 :=  Sim_inj.core_after_external FSim12 d12 js1 js1' st1 st2 m1 ms1 e vals1 ret1). nil m1' nil).xx
       destruct X1 as [d12' [st1' [st2' [AftExt1 [AftExt2 CMS12']]]]].
         constructor.
         apply CMS12. 
         apply AtExt1.
         constructor.
         simpl. (*apply inject_separated_refl.*) intros b; intros. inv H.
         constructor.
         constructor.
         simpl. apply Sim_inj.mem_square_mem_forward in MSQ. apply MSQ.
         simpl. admit. (*pull hastype back through rets*) 
       simpl in *.
       assert (X2 :=  Sim_inj.core_after_external FSim23 d23 js2 js2' st2 st3 m1 ms e
                     vals2 ret1 rets m1' ms').
       destruct X2 as [d23' [stss' [st3' [AftExt22 [AftExt3 CMS23']]]]].
         apply CIL2.
         unfold m3 in *. apply CMS23.
         apply AtExt2. 
         apply Incr2.
         unfold m3 in *. apply Sep13.
         apply CIL'.
         apply RET'.
         apply MSQ.
         unfold ret3 in *. apply Tp3.
       rewrite AftExt2 in AftExt22. apply eq_sym in AftExt22. inv AftExt22.
       exists (d23',d12'). exists st1'. exists st3'.
       split. apply AftExt1. 
       split. unfold ret3 in *. apply AftExt3. 
       assert (ZZ:= intro_compose_match_state _ _ _ _ _ _ _ _ _ _ CMS12' CMS23'). 
          simpl in ZZ. unfold m3' in *. apply ZZ. 
  
  
 constructor.
 simpl.
       assert (NIL12':= Sim_inj.match_state_nil FSim12 _ _ _ _ _ CMS12'). subst.
 
apply  inv MSQ. unfold constructor.

       exists (d23,d12). exists 
    apply check_injectlist_split in CIL.
    destruct CIL as [[NIL CIL2] | [ms1 [ms2 [mm [M [CIL1 CIL2]]]]]].

assert (X1 :=  Sim_inj.core_after_external FSim12 d12 js1 js1' st1 st2 m1). ms e vals1 ret1 rets m1' ms').ss
    destruct X1 xx
       unfold m3. unfold m2. 
    destruct (Sim_inj.core_at_external FSim12 _ _ _ _ _ _ _ _ CMS12 AtExt1) as [ms1 [Hm2 [CIL1 [vals2 [VI2 [Tp2 AtExt2]]]]]].
    destruct (Sim_inj.core_at_external FSim23 _ _ _ _ _ _ _ _ CMS23 AtExt2) as [ms2 [Hm3 [CIL2 [vals3 [VI3 [Tpp AtExt]]]]]].
    exists (
 vals3' [MemInj2 [ValsInj2 [HasType3 AtExt3']]]].
    rewrite AtExt3 in AtExt3'. apply eq_sym in AtExt3'. inv AtExt3'.
    assert (AftExt1 := Sim_inj.core_after_external_reorder FSim12
      _ _ _ _ _ _ _ _ _ CMS12 MemInj1 AtExt1 AtExt2 ValsInj1 HasType2).
 _ _ j1' _ _ _ _ _ vals1 vals2 ret1 ret3 m1'). m2 CMS12 MemInj1  Incr1').
(*    apply Sim_inj.match_state_siminj in CMS12.
    apply Sim_inj.match_state_siminj in CMS23.*)
(*    unfold inject_separated in InjSep.*)
    destruct (inj_split _ _ _ InjIncr _ _ _ MemInj InjSep MemInj1 MemInj2)
       as [j1' [j2' [Incr1' [Incr2' JJ']]]]; subst.
xx
    unfold at_external in AtExt2. remember (csem Sem2). destruct c; simpl in *. destruct Sem2.
    unfold at_external in AtExt2.
  Qed.


  (* An axiom stating that inject forward simulations compose *)
  Lemma forward_simulation_inject_inject_compose :
    Sim_inj.Forward_simulation_inject Sem1 Sem3 ge1 ge3 entry_points13.
  Proof.
    intros. 
    eapply (@Sim_inj.Build_Forward_simulation_inject G1 C1 G3 C3 Sem1 Sem3 ge1 ge3 entry_points13 data13 numpasses13 compose_match_state).
      eapply compose_match_state_numpasses; eauto.
      eapply wf_clos_trans. apply well_founded_sem_compose_ord.
      apply compose_match_state_siminj. 
      apply compose_core_diagram.
      intros v1 v3 sig HEntry vals1 c1 m1 MIC1 IM1.
        apply (compose_core_initial v1 v3 sig HEntry vals1 c1 MIC1 m1 IM1).
      eapply compose_safely_halted; eauto.
      eapply compose_at_external; eauto.
atexternal.

  
  Lemma validblock_elim: forall m b b1 z, 
      (if zlt b (Mem.nextblock m) then Some (b, 0) else None) = Some (b1, z) ->
      b1 = b /\ z = 0.
  Proof. intros.
     remember (zlt b (Mem.nextblock m)) as zz.
     destruct zz. inv H. split; trivial. inversion H.
  Qed. 
  Lemma flat_injD: forall m b b1 delta,
       Mem.flat_inj (Mem.nextblock m) b = Some (b1, delta) -> b1 = b /\ delta = 0.
    Proof. intros. eapply validblock_elim. apply H. Qed.

  Lemma valid_block_flatinj: forall {A:Type} m b (X Y:A),
        Mem.valid_block m b -> (if zlt b (Mem.nextblock m) then X else Y) = X.
    Proof. intros.
      unfold Mem.valid_block in H.
      apply zlt_true. apply H.
    Qed.

  Lemma flatinj_compose: forall m m' 
       (Inj: Mem.inject (Mem.flat_inj (Mem.nextblock m)) m m'),
       Mem.flat_inj (Mem.nextblock m) = 
       inj_compose (Mem.flat_inj (Mem.nextblock m)) (Mem.flat_inj (Mem.nextblock m')).
    Proof.
       intros.
       apply extensionality. intros b.
       unfold inj_compose.
       remember (Mem.flat_inj (Mem.nextblock m) b) as mb.
       destruct mb; trivial.
       destruct p as [b' delta].
       apply eq_sym in Heqmb.
       destruct (flat_injD _ _ _ _ Heqmb). subst.
       assert (validb'3:= Mem.mi_mappedblocks _ _ _ Inj _ _ _ Heqmb).
       unfold Mem.flat_inj.
       rewrite valid_block_flatinj; trivial.
    Qed.

 

Lemma inj_split: forall j1 j2 j' (Incr: inject_incr (inj_compose j1 j2) j') m1 m2 m3
         (SI: Mem.inject (inj_compose j1 j2) m1 m3)
         (SEP: inject_separated (inj_compose j1 j2) j' m1 m3) 
         (SI1 : Mem.inject j1 m1 m2)
         (SI2 : Mem.inject j2 m2 m3),
exists j1', exists j2', 
   inject_incr j1 j1' /\ inject_incr j2 j2' /\ j' = inj_compose j1' j2'.
Proof. admit. Qed.
(*  intros. unfold inject_separated in SEP. destruct SI as [SIA SIB]. destruct SI1 as [SI1A SI1B]. destruct SI2 as [SI2A SI2B].
  exists (fun b => match j1 b with 
                      None => match j' b with
                                  None => None
                                | Some (b'',ofs'') => match j2 b with
                                                        None => Some (b,0)
                                                      | Some (b2,o2) => None
                                                     end
                                end
                    | Some (b',ofs') => Some (b',ofs')
                   end).
  exists (fun b => match j2 b with 
                      None => match j1 b with None => j' b
                                            | Some (b'',ofs'') => None end
                    | Some (b',ofs') => Some (b',ofs')
                   end).
  unfold inject_incr in *. intros.
  split. intros. rewrite H. trivial.
  split. intros. rewrite H. trivial.
  extensionality b.
     unfold inj_compose in *.
     remember (j1 b) as j1b.
     destruct j1b; apply eq_sym in Heqj1b.
       destruct p as [b' ofs'].
       remember (j2 b') as j2b'.
       destruct j2b'; apply eq_sym in Heqj2b'.
         destruct p as [b'' ofs''].
         specialize (Incr b b'' (ofs' + ofs'')). rewrite Heqj1b in Incr. rewrite Heqj2b' in Incr. apply (Incr (eq_refl _)).
       remember (j1 b') as j1b'.
       destruct j1b'; apply eq_sym in Heqj1b'.
         destruct p.
         remember (j' b) as j'b.
         destruct j'b; apply eq_sym in Heqj'b; trivial. destruct p.
         specialize (SEP b b1 z0). rewrite Heqj1b in SEP. rewrite Heqj2b' in SEP. rewrite Heqj'b in SEP.
         destruct (SEP (eq_refl _) (eq_refl _)).
         rewrite (SI1A _ H) in Heqj1b. congruence.
     remember (j' b) as j'b.
       destruct j'b; apply eq_sym in Heqj'b.
         destruct p.
         specialize (SEP b b0 z). rewrite Heqj1b in SEP. rewrite Heqj2b' in SEP. rewrite Heqj'b in SEP.
         destruct (SEP (eq_refl _) (eq_refl _)).
         rewrite (SI1A _ H) in Heqj1b. congruence.
     remember (j' b') as j'b'.
       destruct j'b'; apply eq_sym in Heqj'b'; trivial.
         destruct p. admit.

     assert (SPb := SEP b). rewrite Heqj1b in SPb.
     remember (j' b) as j'b.
       destruct j'b; apply eq_sym in Heqj'b.
         destruct p.
         destruct (SPb _ _ (eq_refl _) (eq_refl _)).
         remember (j2 b) as j2b.
         destruct j2b; apply eq_sym in Heqj2b.
         destruct p as [b'' ofs'']. admit. admit. trivial.
Qed.
  *)     
here

  Lemma compose_after_external: 
        forall cd j j' st1 st3 m1 m3 e vals1 vals3 ret1 ret3 m1' m3'
               (CMS: compose_match_state cd j st1 m1 st3 m3) 
               (MemInj: Mem.inject j m1 m3)
               (AtExt1: at_external Sem1 st1 = Some (e, vals1))
               (AtExt3: at_external Sem3 st3 = Some (e, vals3))
               (ValsInj: Forall2 (val_inject j) vals1 vals3) 
               (InjIncr: inject_incr j j')
               (InjSep: inject_separated j j' m1 m3)
               (MemInj': Mem.inject j' m1' m3')
               (ValInj': val_inject j' ret1 ret3)
               (unchangedUM1: mem_unchanged_on (loc_unmapped j) m1 m1')
               (unchangedOOR: mem_unchanged_on (loc_out_of_reach j m1) m3 m3')
               (FWD1: mem_forward m1 m1')
               (FWD3: mem_forward m3 m3')
               (ArgsHasTp: Forall2 Val.has_type vals3 (sig_args (ef_sig e)))
               (RetHasTp: Val.has_type ret3 (proj_sig_res (ef_sig e))),
        exists cd', exists st1', exists st3',
          after_external Sem1 ret1 st1 = Some st1' /\
          after_external Sem3 ret3 st3 = Some st3' /\
          compose_match_state cd' j' st1' m1' st3' m3'.
  Proof. intros.
    inv CMS. rename c2 into st2. rename H into CMS12. rename H0 into CMS23.
    destruct (Sim_inj.core_at_external FSim12 _ _ _ _ _ _ _ _ CMS12 AtExt1) as [vals2 [MemInj1 [ValsInj1 [HasType2 AtExt2]]]].
    destruct (Sim_inj.core_at_external FSim23 _ _ _ _ _ _ _ _ CMS23 AtExt2) as [vals3' [MemInj2 [ValsInj2 [HasType3 AtExt3']]]].
    rewrite AtExt3 in AtExt3'. apply eq_sym in AtExt3'. inv AtExt3'.
    assert (AftExt1 := Sim_inj.core_after_external_reorder FSim12
      _ _ _ _ _ _ _ _ _ CMS12 MemInj1 AtExt1 AtExt2 ValsInj1 HasType2).
 _ _ j1' _ _ _ _ _ vals1 vals2 ret1 ret3 m1'). m2 CMS12 MemInj1  Incr1').
(*    apply Sim_inj.match_state_siminj in CMS12.
    apply Sim_inj.match_state_siminj in CMS23.*)
(*    unfold inject_separated in InjSep.*)
    destruct (inj_split _ _ _ InjIncr _ _ _ MemInj InjSep MemInj1 MemInj2)
       as [j1' [j2' [Incr1' [Incr2' JJ']]]]; subst.
xx
    unfold at_external in AtExt2. remember (csem Sem2). destruct c; simpl in *. destruct Sem2.
    unfold at_external in AtExt2.
  Qed.

  (* An axiom stating that inject forward simulations compose *)
  Lemma forward_simulation_inject_inject_compose :
    Sim_inj.Forward_simulation_inject Sem1 Sem3 ge1 ge3 entry_points13.
  Proof.
    intros.
    eapply (@Sim_inj.Build_Forward_simulation_inject G1 C1 G3 C3 Sem1 Sem3 ge1 ge3 entry_points13 _ compose_match_state).
      eapply wf_clos_trans. apply well_founded_sem_compose_ord.
      apply compose_match_state_siminj. 
      apply compose_core_diagram.
      intros v1 v3 sig HEntry vals1 vals3 m1 m3 j M3SI V3SI valsInj valsTp Minj.
        apply (compose_core_initial v1 v3 sig HEntry vals1 vals3 m1 m3 j); trivial.
      eapply compose_safely_halted; eauto.
      eapply compose_at_external; eauto.
atexternal.
      

v1 v3 sig
       (HEntry: In (v1, v3, sig) entry_points13)
       (vals1 vals3 : list val) (m1 m3 : mem)
       j (HypJ: j = Mem.flat_inj (Mem.nextblock m1))
       (Mem3SelfInj: Mem.inject (Mem.flat_inj (Mem.nextblock m3)) m3 m3)
       (Vals3SelfInj: Forall2 (val_inject (Mem.flat_inj (Mem.nextblock m3))) vals3 vals3),
       Forall2 (val_inject j) vals1 vals3 ->
       Forall2 Val.has_type vals3 (sig_args sig) ->
       Mem.inject j m1 m3 ->
       exists cd : data13, exists c1 : C1, exists c3 : C3,
          make_initial_core Sem1 ge1 v1 vals1 = Some c1 /\
          make_initial_core Sem3 ge3 v3 vals3 = Some c3 /\
          compose_match_state cd j c1 m1 c3 m3.
  Lemma compose_core_initial: forall v1 v3 sig
       (HEntry: In (v1, v3, sig) entry_points13)
       (vals1 vals3 : list val) (m1 m3 : mem)
       j (HypJ: j = Mem.flat_inj (Mem.nextblock m1))
       (Mem3SelfInj: Mem.inject (Mem.flat_inj (Mem.nextblock m3)) m3 m3)
       (Vals3SelfInj: Forall2 (val_inject (Mem.flat_inj (Mem.nextblock m3))) vals3 vals3),
       Forall2 (val_inject j) vals1 vals3 ->
       Forall2 Val.has_type vals3 (sig_args sig) ->
       Mem.inject j m1 m3 ->
       exists cd : data13, exists c1 : C1, exists c3 : C3,
          make_initial_core Sem1 ge1 v1 vals1 = Some c1 /\
          make_initial_core Sem3 ge3 v3 vals3 = Some c3 /\
          compose_match_state cd j c1 m1 c3 m3.
  Proof.
    intros.
    assert (J1: exists v2, In (v1,v2,sig) entry_points12 /\ In (v2,v3,sig) entry_points23).
      pose proof EPC as myEPC.
      clear - HEntry myEPC.
      induction myEPC.
      simpl in HEntry. destruct HEntry. inv H.
      exists v2; split; simpl; auto.
      destruct (IHmyEPC H) as [v2' [? ?]].
      exists v2'; simpl; split; auto.
      inv HEntry.
   destruct J1 as [v2 [J12 J23]].
    generalize (Sim_inj.core_initial FSim12 _ _ _ J12); intro CI12.

    specialize (CI12 vals1 vals3 m1 m3 Mem3SelfInj Vals3SelfInj).
    destruct CI12 as [d12 [c1 [c2 [MIC1 [MIC2 MS12]]]]].
    (*1*)  subst. assumption.
    (*2*)  subst. assumption.
    (*3*)  subst. assumption.
    generalize (Sim_inj.core_initial FSim23 _ _ _ J23); intro CI23.
    specialize (CI23 vals3 vals3 m3 m3 Mem3SelfInj Vals3SelfInj).
    destruct CI23 as [d23 [c2' [c3 [MIC2' [MIC3 MS23]]]]]; trivial.
       (*1 subst.
       clear MS12 MIC1 MIC2 c1 c2. subst. remember (sig_args sig) as types. 
           clear - H H0 H1 SelfInj3.
           generalize dependent vals1. generalize dependent types.
           induction vals3; intros; simpl.
           (*Nil*) apply Forall2_nil.
           (*Cons*)
             inv H. inv H0. rename y into typA. rename x into a1. rename a into a3.
             apply Forall2_cons.
               Focus 2. eapply IHvals3. apply H7. apply H6.
               clear H6 H7.
               inversion H5; subst; clear H5; try constructor.
                 
                    assert (validj_m3b:= Mem.mi_mappedblocks _ _ _ H1 _ _ _ H).
                    unfold Mem.flat_inj; simpl.
                    econstructor. eapply valid_block_flatinj. assumption.
                      rewrite Int.add_zero. trivial.
                  
                 destruct a3; try constructor. 
                    assert (validj_m3b:= Mem.mi_mappedblocks _ _ _ SelfInj3).  _ _ _ H).
                    unfold Mem.flat_inj; simpl.
                    econstructor. eapply valid_block_flatinj. assumption.
                      rewrite Int.add_zero. trivial.econstructor.*)
    assert (c2' = c2) by congruence. subst.
    exists (d23,d12). (*(Some c2_,m2'),d23'').*)
    exists c1. exists c3.
    split; trivial.
    split; trivial.
    rewrite (flatinj_compose _ _ H1).
    econstructor; eauto.
  Qed.

  Lemma compose_safely_halted:
     forall d j c1 m1 c3 m3 v1 (CMS:compose_match_state d j c1 m1 c3 m3)
        (SH: safely_halted Sem1 ge1 c1 = Some v1),
        safely_halted Sem3 ge3 c3 = Some v1 /\ Mem.inject j m1 m3.
     Proof.
       intros.
       inv CMS. rename H into CMS12. rename H0 into CMS23.
       destruct (Sim_inj.core_halted FSim12 _ _ _ _ _ _ _ CMS12 SH) as [SH2 Inj1].
       destruct (Sim_inj.core_halted FSim23 _ _ _ _ _ _ _ CMS23 SH2) as [SH3 Inj2].
       split; trivial.
       eapply (Mem.inject_compose _ _ _ _ _ Inj1 Inj2).
     Qed.
 
  Lemma compose_at_external: forall cd j st1 m1 st3 m3 e vals1
           (CMS: compose_match_state cd j st1 m1 st3 m3)
           (AtExt1: at_external Sem1 st1 = Some (e, vals1)),
       exists ms : list mem,
  m2 = last ms m1 /\
  Sim_inj.check_injectlist js m1 ms /\
  (exists vals2 : list val,
     Forall2 (val_inject (injlist_compose js)) vals1 vals2 /\
     Forall2 Val.has_type vals2 (sig_args (ef_sig e)) /\
     at_external Sem3 st2 = Some (e, vals2)) exists vals3,
           Mem.inject j m1 m3 /\
           Forall2 (val_inject j) vals1 vals3 /\
           Forall2 Val.has_type vals3 (sig_args (ef_sig e)) /\
           at_external Sem3 st3 = Some (e, vals3).
  Proof.
    intros.
    inv CMS. rename c2 into st2. rename H into CMS12. rename H0 into CMS23.
    destruct (Sim_inj.core_at_external FSim12 _ _ _ _ _ _ _ _ CMS12 AtExt1) as [vals2 [MemInj1 [ValsInj1 [HasType2 AtExt2]]]].
    destruct (Sim_inj.core_at_external FSim23 _ _ _ _ _ _ _ _ CMS23 AtExt2) as [vals3 [MemInj2 [ValsInj2 [HasType3 AtExt4]]]].
    exists vals3.
    split. eapply (Mem.inject_compose _ _ _ _ _ MemInj1 MemInj2).
    split. apply (vals_inject_compose _ _ _ ValsInj1 _ _ ValsInj2).
    split; trivial.
  Qed.

  Lemma compose_core_initial: forall v1 v3 sig
       (HEntry: In (v1, v3, sig) entry_points13)
       (vals1 vals3 : list val) (m1 m3 : mem)
       j (HypJ: j = Mem.flat_inj (Mem.nextblock m1))
       (Mem3SelfInj: Mem.inject (Mem.flat_inj (Mem.nextblock m3)) m3 m3)
       (Vals3SelfInj: Forall2 (val_inject (Mem.flat_inj (Mem.nextblock m3))) vals3 vals3),
       Forall2 (val_inject j) vals1 vals3 ->
       Forall2 Val.has_type vals3 (sig_args sig) ->
       Mem.inject j m1 m3 ->
       exists cd : data13, exists c1 : C1, exists c3 : C3,
          make_initial_core Sem1 ge1 v1 vals1 = Some c1 /\
          make_initial_core Sem3 ge3 v3 vals3 = Some c3 /\
          compose_match_state cd j c1 m1 c3 m3.
  Proof. intros.
    assert (J1: exists v2, In (v1,v2,sig) entry_points12 /\ In (v2,v3,sig) entry_points23).
      pose proof EPC as myEPC.
      clear - HEntry myEPC.
      induction myEPC.
      simpl in HEntry. destruct HEntry. inv H.
      exists v2; split; simpl; auto.
      destruct (IHmyEPC H) as [v2' [? ?]].
      exists v2'; simpl; split; auto.
      inv HEntry.
   destruct J1 as [v2 [J12 J23]].
    generalize (Sim_inj.core_initial FSim12 _ _ _ J12); intro CI12.

    specialize (CI12 vals1 vals3 m1 m3 Mem3SelfInj Vals3SelfInj).
    destruct CI12 as [d12 [c1 [c2 [MIC1 [MIC2 MS12]]]]].
    (*1*)  subst. assumption.
    (*2*)  subst. assumption.
    (*3*)  subst. assumption.
    generalize (Sim_inj.core_initial FSim23 _ _ _ J23); intro CI23.
    specialize (CI23 vals3 vals3 m3 m3 Mem3SelfInj Vals3SelfInj).
    destruct CI23 as [d23 [c2' [c3 [MIC2' [MIC3 MS23]]]]]; trivial.
       (*1 subst.
       clear MS12 MIC1 MIC2 c1 c2. subst. remember (sig_args sig) as types. 
           clear - H H0 H1 SelfInj3.
           generalize dependent vals1. generalize dependent types.
           induction vals3; intros; simpl.
           (*Nil*) apply Forall2_nil.
           (*Cons*)
             inv H. inv H0. rename y into typA. rename x into a1. rename a into a3.
             apply Forall2_cons.
               Focus 2. eapply IHvals3. apply H7. apply H6.
               clear H6 H7.
               inversion H5; subst; clear H5; try constructor.
                 
                    assert (validj_m3b:= Mem.mi_mappedblocks _ _ _ H1 _ _ _ H).
                    unfold Mem.flat_inj; simpl.
                    econstructor. eapply valid_block_flatinj. assumption.
                      rewrite Int.add_zero. trivial.
                  
                 destruct a3; try constructor. 
                    assert (validj_m3b:= Mem.mi_mappedblocks _ _ _ SelfInj3).  _ _ _ H).
                    unfold Mem.flat_inj; simpl.
                    econstructor. eapply valid_block_flatinj. assumption.
                      rewrite Int.add_zero. trivial.econstructor.*)
    assert (c2' = c2) by congruence. subst.
    exists (d23,d12). (*(Some c2_,m2'),d23'').*)
    exists c1. exists c3.
    split; trivial.
    split; trivial.
    rewrite (flatinj_compose _ _ H1).
    econstructor; eauto.
  Qed.

  Lemma compose_safely_halted:
     forall d j c1 m1 c3 m3 v1 (CMS:compose_match_state d j c1 m1 c3 m3)
        (SH: safely_halted Sem1 ge1 c1 = Some v1),
        safely_halted Sem3 ge3 c3 = Some v1 /\ Mem.inject j m1 m3.
     Proof.
       intros.
       inv CMS. rename H into CMS12. rename H0 into CMS23.
       destruct (Sim_inj.core_halted FSim12 _ _ _ _ _ _ _ CMS12 SH) as [SH2 Inj1].
       destruct (Sim_inj.core_halted FSim23 _ _ _ _ _ _ _ CMS23 SH2) as [SH3 Inj2].
       split; trivial.xx
  (* An axiom stating that inject forward simulations compose *)
  Lemma forward_simulation_inject_inject_compose :
    Sim_inj.Forward_simulation_inject Sem1 Sem3 ge1 ge3 entry_points13.
  Proof.
    intros.
    eapply (@Sim_inj.Build_Forward_simulation_inject G1 C1 G3 C3 Sem1 Sem3 ge1 ge3 entry_points13 _ compose_match_state).
      eapply wf_clos_trans. apply well_founded_sem_compose_ord.
      apply compose_match_state_siminj. 
      apply compose_core_diagram.
      intros v1 v3 sig HEntry vals1 vals3 m1 m3 j M3SI V3SI valsInj valsTp Minj.
        apply (compose_core_initial v1 v3 sig HEntry vals1 vals3 m1 m3 j); trivial.
      

  (* An axiom stating that inject forward simulations compose *)
  Lemma forward_simulation_inject_inject_compose :
    Sim_inj.Forward_simulation_inject Sem1 Sem3 ge1 ge3 entry_points13.
  Proof.
    intros.
    eapply (@Sim_inj.Build_Forward_simulation_inject G1 C1 G3 C3 Sem1 Sem3 ge1 ge3 entry_points13 _ compose_match_state).
      eapply wf_clos_trans. apply well_founded_sem_compose_ord.
      apply compose_match_state_siminj. 
      apply fsim_compose_diagram.
intros.
     
      
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
              clos_trans _ (lex_ord (Sim_inj.core_ord FSim23) (Sim_inj.core_ord FSim12)) cd' cd).
   Proof.
    intros. inv H0. rename c2 into st2.
    destruct (Sim_inj.core_diagram FSim12 st1 m1 st1' m1'  H d12 st2 j1 m2 H1) as
      [st2' [m2' [d12' [j1' [Hj1' [Sep12 [MS12 Step2]]]]]]].
    assert (H5: corestep_plus Sem2 ge2 st2 m2 st2' m2' \/
               ((st2,m2) = (st2',m2') /\ Sim_inj.core_ord FSim12 d12' d12) ).
      destruct Step2. auto.
      destruct H0.
        destruct H0.
        destruct x. right. split; auto.
                    left. exists x; auto.
    clear Step2.
    assert (Inj1 := Sim_inj.match_state_siminj _ _ _ _ _ _ _ H1). 
    assert (Inj2 := Sim_inj.match_state_siminj _ _ _ _ _ _ _ H2).
    destruct H5 as [Step2 | [SEQ Ord]].
    (*case corestep_plus Sem2 ge2 st2 m2 st2' m2'*)
      destruct Step2.
      destruct Inj1 as [Inj1A Inj1B]. clear Inj1A.
      destruct Inj2 as [Inj2A Inj2B]. clear Inj2B. 
      apply csem_allowed_modifications in H. rename H into AM1.
      assert (AM2:= corestepN_allowed_modifications H0).
      clear H1. clear st1 st1.
      assert (AUX := @InjInj_AUX _ _ _ _ _ _ _ _ _ FSim23 _ _ _ _ _ H0 _ _ _ _ H2).
      destruct AUX as [st3' [m3' [d' [j2' [AM3 [Incr2 [Sep2 [MS EXEC]]]]]]]].
      exists st3'. exists m3'. exists (d',d12'). exists (inj_compose j1' j2'). 
      split. eapply inject_incr_compose. apply Hj1'. apply Incr2.
      split. (* (Incr1 : inject_incr j1 j1')
                (Incr2 : inject_incr j2 j2')
                (Sep12 : inject_separated j1 j1' m1 m2)
                (Sep23: inject_separated j2 j2' m2 m3),
                inject_separated (inj_compose j1 j2) (inj_compose j1' j2') m1 m3*)
              eapply inject_separated_compose. apply Hj1'. apply Incr2. apply Inj1B. apply Inj2A. apply Sep12. apply Sep2.
      split. econstructor. apply MS12. apply MS.
      destruct EXEC as [ExecPlus | [ExecStar Ord]].
        left; assumption.
        right. split; try assumption.
               eapply lex_ord_left. apply Ord.
    (*case (st2, m2) = (st2', m2') /\ Sim_inj.core_ord FSim12 d' d12*)
      inv SEQ. 
      exists st3. exists m3. exists (d23, d12'). (*was : exists (d',(Some c2,m2),d23).*)
      exists (inj_compose j1' j2).
      split. eapply inject_incr_compose. apply Hj1'. apply inject_incr_refl. 
      split. eapply inject_separated_compose. (*alternative : eapply inject_separated_siminj_compose.*)
               apply Hj1'. 
               apply inject_incr_refl.
               apply Inj1.
               apply Inj2. 
               apply Sep12.
               intros b; intros. congruence.
      split. econstructor. apply MS12. apply H2. 
      right. split. exists O. simpl; auto.
      apply lex_ord_right. apply Ord.
Qed.

  (* An axiom stating that inject forward simulations compose *)
  Lemma forward_simulation_inject_inject_compose :
    Sim_inj.Forward_simulation_inject Sem1 Sem3 ge1 ge3 entry_points13.
  Proof.
    intros.
    eapply (@Sim_inj.Build_Forward_simulation_inject G1 C1 G3 C3 Sem1 Sem3 ge1 ge3 entry_points13 _ compose_match_state).
      apply well_founded_sem_compose_ord.
      apply compose_match_state_siminj. 
      apply fsim_compose_diagram.
     ss
      
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
  Let AuxType:Type := (*(option C2) **) ((list meminj) * (list mem) * (list meminj))%type.

  Let data13 := (Sim_inj.core_data FSim12 * AuxType * Sim_inj.core_data FSim23)%type. 

  Let numpasses13 := ((Sim_inj.num_passes FSim12) + (Sim_inj.num_passes FSim23))%nat. 

  Inductive sem_compose_ord 
      : data13 -> data13 -> Prop :=

    | sem_compose_ord1 :
        forall (d12 d12':Sim_inj.core_data FSim12) (a:AuxType) (d23:Sim_inj.core_data FSim23),
           Sim_inj.core_ord FSim12 d12 d12' ->
           sem_compose_ord (d12,a,d23) (d12',a,d23)

    | sem_compose_ord2 :
        forall (d12 d12':Sim_inj.core_data FSim12) (a a':AuxType) (d23 d23' : Sim_inj.core_data FSim23),
           Sim_inj.core_ord FSim23 d23 d23' ->
           sem_compose_ord (d12,a,d23) (d12',a',d23').


  Lemma well_founded_sem_compose_ord : well_founded sem_compose_ord.
  Proof.
    intro. destruct a as [[d12 a] d23].
    revert d12 a.
(*
    destruct c2.
    2: constructor; intros. 2: inv H.
    set (q := (d23,c)).
    change d23 with (fst q). change c with (snd q). clearbody q.
    clear d23 c.
    induction q using (well_founded_induction (fsim_wf FSim23)).
    intros.
    set (q' := (d12,c)).
    change d12 with (fst q'). change c with (snd q').
    clearbody q'. clear d12 c.
    induction q' using (well_founded_induction (fsim_wf FSim12)).
    constructor; intros. inv H1.
    generalize (H0 (d12,x)). simpl. intros.
    apply H1. destruct q'; auto.
    generalize (H (d23,c2)).
    intros.
    spec H1. destruct q; auto.
    apply H1.
  Qed.
*)
  Admitted.

  Inductive compose_match_state : data13 -> list meminj -> C1 -> mem -> C3 -> mem -> Prop :=
    intro_compose_match_state : 
      forall d12 js1 js2 c2 m2 d23 c1 m1 c3 m3 ms1 ms2,
      Sim_inj.match_state FSim12 d12 js1 c1 m1 c2 m2 -> 
      Sim_inj.match_state FSim23 d23 js2 c2 m2 c3 m3 -> 
      compose_match_state (d12,(*(Some c2,*)(js1,ms1++ms2,js2),d23) (js1 ++ js2) c1 m1 c3 m3.
      (*compose_match_state (d23,(*(Some c2,m2),*)d12) (js1 ++ js2) c1 m1 c3 m3.*)

  Lemma compose_match_state_numpasses: 
        forall (cd : data13) (js : list meminj) (c1 : C1) (m1 : mem) (c3 : C3) (m3 : mem),
        compose_match_state cd js c1 m1 c3 m3 -> length js = numpasses13.
    Proof.
      intros.
      inv H. unfold numpasses13. 
      rewrite <- (Sim_inj.match_state_num_passes _ _ _ _ _ _ _ H0).
      rewrite <- (Sim_inj.match_state_num_passes _ _ _ _ _ _ _ H1).
      rewrite app_length. reflexivity.
    Qed.

  Lemma compose_match_state_siminj: forall d j st1 m1 st2 m2,
        compose_match_state d j st1 m1 st2 m2 -> siminj (injlist_compose j) m1 m2.
    Proof. 
      intros until m2. intros [H1 H2]. intros.
      apply Sim_inj.match_state_siminj in H.
      apply Sim_inj.match_state_siminj in H0.
      eapply siminj_list_compose; eauto.
    Qed.

  Lemma compose_core_diagram: 
        forall (st1 : C1) (m1 : mem) (st1' : C1) (m1' : mem),
                corestep Sem1 ge1 st1 m1 st1' m1' ->
        forall (cd : data13) (st3 : C3) (J : list meminj) (m3 : mem),
               compose_match_state cd J st1 m1 st3 m3 ->
        exists st3' : C3, exists m3' : mem, exists cd' : data13, exists J' : list meminj,
               Forall2 inject_incr J J' /\
               inject_separated (injlist_compose J) (injlist_compose J') m1 m3 /\
               compose_match_state cd' J' st1' m1' st3' m3' /\
               (corestep_plus Sem3 ge3 st3 m3 st3' m3' \/
                corestep_star Sem3 ge3 st3 m3 st3' m3' /\
                clos_trans data13 sem_compose_ord cd' cd). (* clos_trans data13
                (lex_ord (Sim_inj.core_ord FSim23) (Sim_inj.core_ord FSim12)) cd' cd).*)
   Proof. 
    intros. inv H0. rename c2 into st2. rename js1 into J1. rename js2 into J2. 
    destruct (Sim_inj.core_diagram FSim12 st1 m1 st1' m1' H _ _ _ _ H1) as
      [st2' [m2' [d12' [J1' [HJ1' [Sep12 [MS12 Step2]]]]]]].
    assert (H6: corestep_plus Sem2 ge2 st2 (last ms1 m1) st2' m2' \/
               ((st2,last ms1 m1) = (st2',m2') /\ Sim_inj.core_ord FSim12 d12' d12) ).
      destruct Step2. auto.
      destruct H0.
        destruct H0.
        destruct x. right. split; auto.
                    left. exists x; auto.
    clear Step2.
    assert (Inj1 := Sim_inj.match_state_siminj _ _ _ _ _ _ _ H1). 
    assert (Inj2 := Sim_inj.match_state_siminj _ _ _ _ _ _ _ H2).
    destruct H6 as [Step2 | [SEQ Ord]].
    (*case corestep_plus Sem2 ge2 st2 m2 st2' m2'*)
      destruct Step2.
      destruct Inj1 as [Inj1A Inj1B]. clear Inj1A.
      destruct Inj2 as [Inj2A Inj2B]. clear Inj2B. 
      apply csem_allowed_modifications in H. rename H into AM1.
      assert (AM2:= corestepN_allowed_modifications H0).
      clear H1. clear st1 st1.
      assert (AUX := @InjInj_core_diagram_AUX _ _ _ _ _ _ _ _ _ FSim23 _ _ _ _ _ H0 _ _ _ _ H2).
      destruct AUX as [st3' [m3' [d' [J2' [AM3 [Incr2 [Sep2 [MS EXEC]]]]]]]].
      exists st3'. exists m3'.
      eexists. (*unfold data13.  exists (d12',(J1',m2',J2'),d').*)
      exists (J1' ++ J2'). 
      split. eapply inject_incr_compose. apply HJ1'. apply Incr2.
      split. (* (Incr1 : inject_incr j1 j1')
                (Incr2 : inject_incr j2 j2')
                (Sep12 : inject_separated j1 j1' m1 m2)
                (Sep23: inject_separated j2 j2' m2 m3),
                inject_separated (inj_compose j1 j2) (inj_compose j1' j2') m1 m3*)
              eapply inject_separated_injlist_compose. apply HJ1'. apply Incr2. apply Inj1B. apply Inj2A. apply Sep12. apply Sep2.
      split. econstructor. apply MS12. apply MS.
      
      destruct EXEC as [ExecPlus | [ExecStar Ord]].
        left; assumption.
        right. split; try assumption.
             admit. (*  eapply lex_ord_clos_trans_left. apply Ord.*)
    (*case (st2, m2) = (st2', m2') /\ Sim_inj.core_ord FSim12 d' d12*)
      inv SEQ. 
      exists st3. exists m3. 
      exists (d12',(J1',m2',J2),d23). (*exists (d23, d12'). *)(*was : exists (d',(Some c2,m2),d23).*)
      exists (J1' ++ J2).
      split. eapply inject_incr_compose. apply HJ1'. apply inject_incr_list_refl. 
      split. eapply inject_separated_injlist_compose. (*alternative : eapply inject_separated_siminj_compose.*)
               apply HJ1'. 
               apply inject_incr_list_refl.
               apply Inj1.
               apply Inj2. 
               apply Sep12.
               intros b; intros. rewrite H0 in H3. inv H3. (*congruence.*)
      split. econstructor. apply MS12. apply H2. 
      right. split. exists O. simpl; auto.
        eapply t_step. econstructor. admit. (*seem to require changing the order of components!*) (*apply lex_ord_right. apply Ord.*)
  Qed.

  Lemma compose_core_initial:
        forall v1 v3 sig (HEntry : In (v1, v3, sig) entry_points13) vals1
               c1 m1 (MIC1 : make_initial_core Sem1 ge1 v1 vals1 = Some c1) 
              (IM1: initial_mem Sem1 ge1 m1),
        let js := Sim_inj.mkInjections m1 numpasses13 in
        exists cd, exists c3, exists vals3, exists m3,
          make_initial_core Sem3 ge3 v3 vals3 = Some c3 /\
          initial_mem Sem3 ge3 m3 /\ compose_match_state cd js c1 m1 c3 m3.
  Proof.
    intros.
    assert (J1: exists v2, In (v1,v2,sig) entry_points12 /\ In (v2,v3,sig) entry_points23).
      pose proof EPC as myEPC.
      clear - HEntry myEPC.
      induction myEPC.
      simpl in HEntry. destruct HEntry. inv H.
      exists v2; split; simpl; auto.
      destruct (IHmyEPC H) as [v2' [? ?]].
      exists v2'; simpl; split; auto.
      inv HEntry.
   destruct J1 as [v2 [J12 J23]].
    generalize (Sim_inj.core_initial FSim12 _ _ _ J12); intro CI12.

    specialize (CI12 _ _ _ MIC1 IM1).
    destruct CI12 as [d12 [c2 [vals2 [m2 [MIC2 [IM2 MS12]]]]]].
    generalize (Sim_inj.core_initial FSim23 _ _ _ J23); intro CI23.
    specialize (CI23 _ _ _ MIC2 IM2).
    destruct CI23 as [d23 [c3 [vals3 [m3 [MIC3 [IM3 MS23]]]]]].
    exists ((d12,
       (Sim_inj.mkInjections m1 (Sim_inj.num_passes FSim12), m2,
       Sim_inj.mkInjections m2 (Sim_inj.num_passes FSim23)), d23)). (*exists (d23,d12). *) 
    exists c3. exists vals3. exists m3.
    split; trivial.
    split; trivial.
    assert (ZZ:= intro_compose_match_state _ _ _ _ _ _ _ _ _ _ MS12 MS23).
    unfold js. unfold numpasses13. admit.
  Qed. (*rewrite (flatinj_compose _ _ H1).*)

  Lemma compose_safely_halted:
     forall (cd : data13) (js : list meminj) c1 m1 c3 m3 v1 
            (CMS: compose_match_state cd js c1 m1 c3 m3)
            (SH1: safely_halted Sem1 ge1 c1 = Some v1),
     safely_halted Sem3 ge3 c3 = Some v1 
     /\ exists ms, m3 = last ms m1 /\ Sim_inj.check_injectlist js m1 ms.
     Proof. 
       intros.
       inv CMS. rename H into CMS12. rename H0 into CMS23.
       destruct (Sim_inj.core_halted FSim12 _ _ _ _ _ _ _ CMS12 SH1) as [SH2 [ms1 [Hms1 Inj1]]].
       destruct (Sim_inj.core_halted FSim23 _ _ _ _ _ _ _ CMS23 SH2) as [SH3 [ms2 [Hms2 Inj2]]].
       split; trivial.
       clear - Inj1 Inj2 Hms1 Hms2. subst. 
       apply check_injectlist_app1; assumption. 
     Qed.

  Lemma compose_at_externalRob: forall cd J st1 m1 st3 m3 e vals1
           (CMS: compose_match_state cd J st1 m1 st3 m3)
           (AtExt1: at_external Sem1 st1 = Some (e, vals1)),
       exists ms,
           m3 = last ms m1 /\
           Sim_inj.check_injectlist J m1 ms /\
           exists vals3,
              Forall2 (val_inject (injlist_compose J)) vals1 vals3 /\
              Forall2 Val.has_type vals3 (sig_args (ef_sig e)) /\
              at_external Sem3 st3 = Some (e, vals3).
  Proof. 
    intros.
    inv CMS. rename c2 into st2. rename H into CMS12. rename H0 into CMS23.
    destruct (Sim_inj.core_at_externalRob FSim12 _ _ _ _ _ _ _ _ CMS12 AtExt1) as [ms2 [Hm2 [CIL2 [vals2 [ValsInj1 [HasType2 AtExt2]]]]]].
    destruct (Sim_inj.core_at_externalRob FSim23 _ _ _ _ _ _ _ _ CMS23 AtExt2) as [ms3 [Hm3 [CIL3 [vals3 [ValsInj2 [HasType3 AtExt4]]]]]].
    subst.
    assert (ZZ:= check_injectlist_app1 _ _ _ _ CIL2 _ CIL3).
    destruct ZZ as [ms [HMS1 HMS2]].
    exists ms.
    split. apply HMS1.
    split. apply HMS2.
    exists vals3.
    split. rewrite injlist_compose_app. 
           eapply (vals_inject_compose _ _ _ ValsInj1 _ _ ValsInj2).
    split; trivial.  
  Qed.

  Lemma compose_after_externalRob: 
        forall (cd : data13) (js js' : list meminj) st1 st3 m1 ms e vals1 ret1 rets m1' ms',
          let m3 := last ms m1 in
          let ret3 := last rets ret1 in
        forall (CIL: Sim_inj.check_injectlist js m1 ms)
               (CMS: compose_match_state cd js st1 m1 st3 m3)
               (AtExt1: at_external Sem1 st1 = Some (e, vals1))
               (Incr: Forall2 inject_incr js js')
               (Sep13: inject_separated (injlist_compose js) (injlist_compose js') m1 m3),
          let m3' := last ms' m1' in
        forall (CIL': Sim_inj.check_injectlist js' m1' ms')
               (RET': Sim_inj.check_returns js' ret1 rets)
               (MSQ: Sim_inj.mem_square js m1 ms m1' ms')
               (Tp3: Val.has_type ret3 (proj_sig_res (ef_sig e))),
        exists cd', exists st1', exists st3',
          after_external Sem1 ret1 st1 = Some st1' /\
          after_external Sem3 ret3 st3 = Some st3' /\
          compose_match_state cd' js' st1' m1' st3' m3'.
  Proof.
    intros.
    inv CMS. rename c2 into st2. rename H into CMS12. rename H0 into CMS23. 
    apply injlist_incr_split in Incr. destruct Incr as [js1' [js2' [XX [Incr1 Incr2]]]]. subst.
    unfold m3 in *.
    apply check_injectlist_split in CIL.
    destruct CIL as [[NIL CIL2] | [M1 [M2 [m [M [CCIL1 CCIL2]]]]]].
    (*Case js1 = nil*)
       subst. simpl in *.
       destruct (Sim_inj.core_at_externalRob FSim12 _ _ _ _ _ _ _ _ CMS12 AtExt1) 
          as [ms1 [Hm2 [CIL1 [vals2 [VI2 [Tp2 AtExt2]]]]]].
       destruct ms1; try contradiction. clear CIL1. inv Incr1. simpl in *.
       assert (X1 :=  Sim_inj.core_after_externalRob FSim12 d12 nil nil st1 st2 m1 nil e vals1 ret1 nil m1' nil).
       destruct X1 as [d12' [st1' [st2' [AftExt1 [AftExt2 CMS12']]]]].
         constructor.
         apply CMS12. 
         apply AtExt1.
         constructor.
         simpl. (*apply inject_separated_refl.*) intros b; intros. inv H.
         constructor.
         constructor.
         simpl. apply Sim_inj.mem_square_mem_forward in MSQ. apply MSQ.
         simpl. eapply check_returns_types; eauto.
       simpl in *.
       assert (X2 :=  Sim_inj.core_after_externalRob FSim23 d23 js2 js2' st2 st3 m1 ms e
                     vals2 ret1 rets m1' ms').
       destruct X2 as [d23' [stss' [st3' [AftExt22 [AftExt3 CMS23']]]]].
         apply CIL2.
         unfold m3 in *. apply CMS23.
         apply AtExt2. 
         apply Incr2.
         unfold m3 in *. apply Sep13.
         apply CIL'.
         apply RET'.
         apply MSQ.
         unfold ret3 in *. apply Tp3.
       rewrite AftExt2 in AftExt22. apply eq_sym in AftExt22. inv AftExt22.
       eexists. (*exists (d23',d12').*)
       exists st1'. exists st3'.
       split. apply AftExt1. 
       split. unfold ret3 in *. apply AftExt3. 
       assert (ZZ:= intro_compose_match_state _ _ _ _ _ _ _ _ _ _ CMS12' CMS23'). 
          simpl in ZZ. unfold m3' in *. apply ZZ. 
    (*Case js1 = cons*)
       unfold m3 in *. subst.
       destruct (Sim_inj.core_at_externalRob FSim12 _ _ _ _ _ _ _ _ CMS12 AtExt1) as [ms1 [Hm2 [CIL1 [vals2 [VI1 [ValTp2 AtExt2]]]]]]. 
          subst.
 (*       assert (exists N1, exists n, ms1 = N1 ++ n :: nil). admit. destruct H as [N1 [n HH]]. subst.
 *)
       destruct (Sim_inj.core_at_externalRob FSim23 _ _ _ _ _ _ _ _ CMS23 AtExt2) as [ms2 [Hm3 [CIL2 [vals3 [VI2 [ValTp3 AtExt3]]]]]]. 
       simpl in *. subst. (*  clear CIL1 Hm2 ms1. xx clear CIL1 ms1.*) (* destruct ms1; try contradiction. clear CIL1. inv Incr1. simpl in *.*)
       rewrite Hm3 in *. clear Hm3.
       
       assert (X1 :=  Sim_inj.core_after_externalRob FSim12 d12 js1 js1' st1 st2 m1 (M1 ++ m :: nil) e vals1 ret1).
       destruct X1 as [d12' [st1' [st2' [AftExt1 [AftExt2 CMS12']]]]].
         constructor.
       destruct (Sim_inj.core_at_external FSim12 _ _ _ _ _ _ _ _ CMS12 AtExt1) as [INJ1 [vals2 [VI1 [ArgTp2 AtExt2]]]].
          (*Rob .. as [ms1 [Hm2 [CIL1 [vals2 [VI2 [Tp2 AtEXt2]]]]]]. *)
       destruct (Sim_inj.core_at_external FSim23 _ _ _ _ _ _ _ _ CMS23 AtExt2) as [INJ2 [vals3 [VI2 [ArgTp3 AtExt3]]]].
          (*Rob .. as [ms1 [Hm2 [CIL1 [vals2 [VI2 [Tp2 AtEXt2]]]]]]. *)
       simpl in *. subst. (*  clear CIL1 Hm2 ms1. xx clear CIL1 ms1.*) (* destruct ms1; try contradiction. clear CIL1. inv Incr1. simpl in *.*)
       assert (X1 :=  Sim_inj.core_after_externalRob FSim12 d12 js1 js1' st1 st2 m1 (M1 ++ m :: nil) e vals1 ret1). nil m1' nil).xx
       destruct X1 as [d12' [st1' [st2' [AftExt1 [AftExt2 CMS12']]]]].
         constructor.
         apply CMS12. 
         apply AtExt1.
         constructor.
         simpl. (*apply inject_separated_refl.*) intros b; intros. inv H.
         constructor.
         constructor.
         simpl. apply Sim_inj.mem_square_mem_forward in MSQ. apply MSQ.
         simpl. admit. (*pull hastype back through rets*) 
       simpl in *.
       assert (X2 :=  Sim_inj.core_after_external FSim23 d23 js2 js2' st2 st3 m1 ms e
                     vals2 ret1 rets m1' ms').
       destruct X2 as [d23' [stss' [st3' [AftExt22 [AftExt3 CMS23']]]]].
         apply CIL2.
         unfold m3 in *. apply CMS23.
         apply AtExt2. 
         apply Incr2.
         unfold m3 in *. apply Sep13.
         apply CIL'.
         apply RET'.
         apply MSQ.
         unfold ret3 in *. apply Tp3.
       rewrite AftExt2 in AftExt22. apply eq_sym in AftExt22. inv AftExt22.
       exists (d23',d12'). exists st1'. exists st3'.
       split. apply AftExt1. 
       split. unfold ret3 in *. apply AftExt3. 
       assert (ZZ:= intro_compose_match_state _ _ _ _ _ _ _ _ _ _ CMS12' CMS23'). 
          simpl in ZZ. unfold m3' in *. apply ZZ. 
  
  
 constructor.
 simpl.
       assert (NIL12':= Sim_inj.match_state_nil FSim12 _ _ _ _ _ CMS12'). subst.
 
apply  inv MSQ. unfold constructor.

       exists (d23,d12). exists 
    apply check_injectlist_split in CIL.
    destruct CIL as [[NIL CIL2] | [ms1 [ms2 [mm [M [CIL1 CIL2]]]]]].

assert (X1 :=  Sim_inj.core_after_external FSim12 d12 js1 js1' st1 st2 m1). ms e vals1 ret1 rets m1' ms').ss
    destruct X1 xx
       unfold m3. unfold m2. 
    destruct (Sim_inj.core_at_external FSim12 _ _ _ _ _ _ _ _ CMS12 AtExt1) as [ms1 [Hm2 [CIL1 [vals2 [VI2 [Tp2 AtExt2]]]]]].
    destruct (Sim_inj.core_at_external FSim23 _ _ _ _ _ _ _ _ CMS23 AtExt2) as [ms2 [Hm3 [CIL2 [vals3 [VI3 [Tpp AtExt]]]]]].
    exists (
 vals3' [MemInj2 [ValsInj2 [HasType3 AtExt3']]]].
    rewrite AtExt3 in AtExt3'. apply eq_sym in AtExt3'. inv AtExt3'.
    assert (AftExt1 := Sim_inj.core_after_external_reorder FSim12
      _ _ _ _ _ _ _ _ _ CMS12 MemInj1 AtExt1 AtExt2 ValsInj1 HasType2).
 _ _ j1' _ _ _ _ _ vals1 vals2 ret1 ret3 m1'). m2 CMS12 MemInj1  Incr1').
(*    apply Sim_inj.match_state_siminj in CMS12.
    apply Sim_inj.match_state_siminj in CMS23.*)
(*    unfold inject_separated in InjSep.*)
    destruct (inj_split _ _ _ InjIncr _ _ _ MemInj InjSep MemInj1 MemInj2)
       as [j1' [j2' [Incr1' [Incr2' JJ']]]]; subst.
xx
    unfold at_external in AtExt2. remember (csem Sem2). destruct c; simpl in *. destruct Sem2.
    unfold at_external in AtExt2.
  Qed.

 Admitted.

  (* An axiom stating that inject forward simulations compose *)
  Lemma forward_simulation_inject_inject_compose :
    Sim_inj.Forward_simulation_inject Sem1 Sem3 ge1 ge3 entry_points13.
  Proof.
    intros. 
    eapply (@Sim_inj.Build_Forward_simulation_inject G1 C1 G3 C3 Sem1 Sem3 ge1 ge3
              entry_points13 data13 numpasses13 compose_match_state). (* with (core_ord:=sem_compose_ord).*)
      eapply compose_match_state_numpasses; eauto.
(*      apply well_founded_sem_compose_ord.*)
      eapply wf_clos_trans. apply well_founded_sem_compose_ord.
      apply compose_match_state_siminj.
      eapply compose_core_diagram; eauto.
      eapply compose_core_initial; eauto.
      eapply compose_safely_halted; eauto.
 admit.
      eapply compose_at_externalRob; eauto.
 admit.
      eapply compose_after_externalRob; eauto.
  Proof.


  Lemma compose_at_external: forall cd J st1 m1 st3 m3 e vals1
           (CMS: compose_match_state cd J st1 m1 st3 m3)
           (AtExt1: at_external Sem1 st1 = Some (e, vals1)),
        (Mem.inject (injlist_compose J) m1 m3 /\
           exists vals3,
              Forall2 (val_inject (injlist_compose J)) vals1 vals3 /\
              Forall2 Val.has_type vals3 (sig_args (ef_sig e)) /\
              at_external Sem3 st3 = Some (e, vals3)).
  Proof.
    intros.
    inv CMS. rename c2 into st2. rename H into CMS12. rename H0 into CMS23.
    destruct (Sim_inj.core_at_external FSim12 _ _ _ _ _ _ _ _ CMS12 AtExt1) as [Minj1 [vals2 [ValsInj1 [HasType2 AtExt2]]]].
    destruct (Sim_inj.core_at_external FSim23 _ _ _ _ _ _ _ _ CMS23 AtExt2) as [Minj2 [vals3 [ValsInj2 [HasType3 AtExt3]]]].
    split. eapply inject_compose_app. apply Minj1. apply Minj2.
    exists vals3.
    split. rewrite injlist_compose_app. eapply (vals_inject_compose _ _ _ ValsInj1 _ _ ValsInj2).
    split; assumption.
  Qed.
cc

  Lemma compose_after_external: 
        forall (cd : data13) (js js' : list meminj) st1 st3 m1 m3 e vals1 ret1 rets m1' m3',
          let ret3 := last rets ret1 in
        forall (CMS: compose_match_state cd js st1 m1 st3 m3)
               (AtExt1: at_external Sem1 st1 = Some (e, vals1))
               (Incr: Forall2 inject_incr js js')
               (Sep13: inject_separated (injlist_compose js) (injlist_compose js') m1 m3)
               (CIL': Mem.inject (injlist_compose js') m1' m3')
               (RET': Sim_inj.check_returns js' ret1 rets)
               (MSQ: Sim_inj.mem_squareUni js m1 m3 m1' m3')
               (Tp3: Val.has_type ret3 (proj_sig_res (ef_sig e))),
        exists cd', exists st1', exists st3',
          after_external Sem1 ret1 st1 = Some st1' /\
          after_external Sem3 ret3 st3 = Some st3' /\
          compose_match_state cd' js' st1' m1' st3' m3'.
  Proof. intros.
    inv CMS. rename c2 into st2. rename H into CMS12. rename H0 into CMS23. 
    apply injlist_incr_split in Incr. destruct Incr as [js1' [js2' [XX [Incr1 Incr2]]]]. subst.
 (*  apply check_injectlist_split in CIL.
    destruct CIL as [[NIL CIL2] | [M1 [M2 [m [M [CCIL1 CCIL2]]]]]].
    (*Case js1 = nil*)
       subst. simpl in *.
       destruct (Sim_inj.core_at_external FSim12 _ _ _ _ _ _ _ _ CMS12 AtEXt1) 
          as [ms1 [Hm2 [CIL1 [vals2 [VI2 [Tp2 AtEXt2]]]]]].
        destruct ms1; try contradiction. clear CIL1. inv Incr1. simpl in *.
(*      assert (Num1:= Sim_inj.match_state_num_passes _ _ _ _ _ _ _ CMS12). *)
(* simpl in Num1. simpl in numpasses13. rewrite <- Num1 in numpasses13. simpl in *.*)  
(*       assert (NIL12:= Sim_inj.match_state_nil FSim12 _ _ _ _ _ CMS12). subst.*)
       assert (X1 :=  Sim_inj.core_after_external FSim12 d12 nil nil st1 st2 m1 nil e vals1 ret1 nil m1' nil).
       destruct X1 as [d12' [st1' [st2' [AftEXt1 [AftEXt2 CMS12']]]]].
         constructor.
         apply CMS12. 
         apply AtEXt1.
         constructor.
         simpl. (*apply inject_separated_refl.*) intros b; intros. inv H.
         constructor.
         constructor.
         simpl. apply Sim_inj.mem_square_mem_forward in MSQ. apply MSQ.
         simpl. eapply check_returns_types; eauto.
       simpl in *.
       assert (X2 :=  Sim_inj.core_after_external FSim23 d23 js2 js2' st2 st3 m1 ms e
                     vals2 ret1 rets m1' ms').
       destruct X2 as [d23' [stss' [st3' [AftEXt22 [AftEXt3 CMS23']]]]].
         apply CIL2.
         unfold m3 in *. apply CMS23.
         apply AtEXt2. 
         apply Incr2.
         unfold m3 in *. apply Sep13.
         apply CIL'.
         apply RET'.
         apply MSQ.
         unfold ret3 in *. apply Tp3.
       rewrite AftEXt2 in AftEXt22. apply eq_sym in AftEXt22. inv AftEXt22.
       exists (d23',d12'). exists st1'. exists st3'.
       split. apply AftEXt1. 
       split. unfold ret3 in *. apply AftEXt3. 
       assert (ZZ:= intro_compose_match_state _ _ _ _ _ _ _ _ _ _ CMS12' CMS23'). 
          simpl in ZZ. unfold m3' in *. apply ZZ. 
    Case js1 = cons*)
      (* unfold m3 in *. subst. *)
       destruct (Sim_inj.core_at_external FSim12 _ _ _ _ _ _ _ _ CMS12 AtExt1) as [Minj1 [vals2 [VI2 [Tp2 AtExt2]]]].
       assert (X1 :=  Sim_inj.core_after_external FSim12 d12 js1 js1' st1 st2 m1 m2 e vals1 ret1 rets m1').
       unfold 
       assert (Z1:= check_injectlist_split). in CIL'.
    destruct CIL as [[NIL CIL2] | [M1 [M2 [m [M [CCIL1 CCIL2]]]]]].
    (*Case js1 = nil*) destruct X1 as [d12' [st1' [st2' [AftExt1 [AftExt2 CMS12']]]]].
         constructor.
         apply CMS12. 
         apply AtExt1.
         constructor.
         simpl. (*apply inject_separated_refl.*) intros b; intros. inv H.
         constructor.
         constructor.
         simpl. apply Sim_inj.mem_square_mem_forward in MSQ. apply MSQ.
         simpl. admit. (*pull hastype back through rets*) 
       simpl in *.
       assert (X2 :=  Sim_inj.core_after_external FSim23 d23 js2 js2' st2 st3 m1 ms e
                     vals2 ret1 rets m1' ms').
       destruct X2 as [d23' [stss' [st3' [AftExt22 [AftExt3 CMS23']]]]].
         apply CIL2.
         unfold m3 in *. apply CMS23.
         apply AtExt2. 
         apply Incr2.
         unfold m3 in *. apply Sep13.
         apply CIL'.
         apply RET'.
         apply MSQ.
         unfold ret3 in *. apply Tp3.
       rewrite AftExt2 in AftExt22. apply eq_sym in AftExt22. inv AftExt22.
       exists (d23',d12'). exists st1'. exists st3'.
       split. apply AftExt1. 
       split. unfold ret3 in *. apply AftExt3. 
       assert (ZZ:= intro_compose_match_state _ _ _ _ _ _ _ _ _ _ CMS12' CMS23'). 
          simpl in ZZ. unfold m3' in *. apply ZZ. 
  
  
 constructor.
 simpl.
Admitted.  

  (* An axiom stating that inject forward simulations compose *)
  Lemma forward_simulation_inject_inject_compose :
    Sim_inj.Forward_simulation_inject Sem1 Sem3 ge1 ge3 entry_points13.
  Proof.
    intros. 
    eapply (@Sim_inj.Build_Forward_simulation_inject G1 C1 G3 C3 Sem1 Sem3 ge1 ge3 entry_points13 data13 numpasses13 compose_match_state).
      eapply compose_match_state_numpasses; eauto.
      eapply wf_clos_trans. apply well_founded_sem_compose_ord.
      apply compose_match_state_siminj. 
      apply compose_core_diagram.
      intros v1 v3 sig HEntry vals1 c1 m1 MIC1 IM1.
        apply (compose_core_initial v1 v3 sig HEntry vals1 c1 MIC1 m1 IM1).
      eapply compose_safely_halted; eauto.
      eapply compose_at_external; eauto.
      eapply compose_after_external; eauto.
aftertexternalRob.
  Lemma compose_after_externalRob: 
        forall (cd : data13) (js js' : list meminj) st1 st3 m1 ms e vals1 ret1 rets m1' ms',
          let m3 := last ms m1 in
          let ret3 := last rets ret1 in
        forall (CIL: Sim_inj.check_injectlist js m1 ms)
               (CMS: compose_match_state cd js st1 m1 st3 m3)
               (AtExt1: at_external Sem1 st1 = Some (e, vals1))
               (Incr: Forall2 inject_incr js js')
               (Sep13: inject_separated (injlist_compose js) (injlist_compose js') m1 m3),
          let m3' := last ms' m1' in
        forall (CIL': Sim_inj.check_injectlist js' m1' ms')
               (RET': Sim_inj.check_returns js' ret1 rets)
               (MSQ: Sim_inj.mem_square js m1 ms m1' ms')
               (Tp3: Val.has_type ret3 (proj_sig_res (ef_sig e))),x
        exists cd', exists st1', exists st3',
          after_external Sem1 ret1 st1 = Some st1' /\
          after_external Sem3 ret3 st3 = Some st3' /\
          compose_match_state cd' js' st1' m1' st3' m3'.
  Proof. intros.
    inv CMS. rename c2 into st2. rename H into CMS12. rename H0 into CMS23. 
    apply injlist_incr_split in Incr. destruct Incr as [js1' [js2' [XX [Incr1 Incr2]]]]. subst.
    apply check_injectlist_split in CIL.
    destruct CIL as [[NIL CIL2] | [M1 [M2 [m [M [CCIL1 CCIL2]]]]]].
    (*Case js1 = nil*)
       subst. simpl in *.
       destruct (Sim_inj.core_at_external FSim12 _ _ _ _ _ _ _ _ CMS12 AtExt1) 
          as [ms1 [Hm2 [CIL1 [vals2 [VI2 [Tp2 AtExt2]]]]]].
        destruct ms1; try contradiction. clear CIL1. inv Incr1. simpl in *.
(*      assert (Num1:= Sim_inj.match_state_num_passes _ _ _ _ _ _ _ CMS12). *)
(* simpl in Num1. simpl in numpasses13. rewrite <- Num1 in numpasses13. simpl in *.*)  
(*       assert (NIL12:= Sim_inj.match_state_nil FSim12 _ _ _ _ _ CMS12). subst.*)
       assert (X1 :=  Sim_inj.core_after_external FSim12 d12 nil nil st1 st2 m1 nil e vals1 ret1 nil m1' nil).
       destruct X1 as [d12' [st1' [st2' [AftExt1 [AftExt2 CMS12']]]]].
         constructor.
         apply CMS12. 
         apply AtExt1.
         constructor.
         simpl. (*apply inject_separated_refl.*) intros b; intros. inv H.
         constructor.
         constructor.
         simpl. apply Sim_inj.mem_square_mem_forward in MSQ. apply MSQ.
         simpl. eapply check_returns_types; eauto.
       simpl in *.
       assert (X2 :=  Sim_inj.core_after_external FSim23 d23 js2 js2' st2 st3 m1 ms e
                     vals2 ret1 rets m1' ms').
       destruct X2 as [d23' [stss' [st3' [AftExt22 [AftExt3 CMS23']]]]].
         apply CIL2.
         unfold m3 in *. apply CMS23.
         apply AtExt2. 
         apply Incr2.
         unfold m3 in *. apply Sep13.
         apply CIL'.
         apply RET'.
         apply MSQ.
         unfold ret3 in *. apply Tp3.
       rewrite AftExt2 in AftExt22. apply eq_sym in AftExt22. inv AftExt22.
       exists (d23',d12'). exists st1'. exists st3'.
       split. apply AftExt1. 
       split. unfold ret3 in *. apply AftExt3. 
       assert (ZZ:= intro_compose_match_state _ _ _ _ _ _ _ _ _ _ CMS12' CMS23'). 
          simpl in ZZ. unfold m3' in *. apply ZZ. 
    (*Case js1 = cons*)
       unfold m3 in *. subst. 
       destruct (Sim_inj.core_at_external FSim12 _ _ _ _ _ _ _ _ CMS12 AtExt1) 
          as [ms1 [Hm2 [CIL1 [vals2 [VI2 [Tp2 AtExt2]]]]]]. 
       simpl in *. subst.  clear CIL1 Hm2 ms1. xx clear CIL1 ms1. (* destruct ms1; try contradiction. clear CIL1. inv Incr1. simpl in *.*)
       assert (X1 :=  Sim_inj.core_after_external FSim12 d12 js1 js1' st1 st2 m1 ms1 e vals1 ret1). nil m1' nil).xx
       destruct X1 as [d12' [st1' [st2' [AftExt1 [AftExt2 CMS12']]]]].
         constructor.
         apply CMS12. 
         apply AtExt1.
         constructor.
         simpl. (*apply inject_separated_refl.*) intros b; intros. inv H.
         constructor.
         constructor.
         simpl. apply Sim_inj.mem_square_mem_forward in MSQ. apply MSQ.
         simpl. admit. (*pull hastype back through rets*) 
       simpl in *.
       assert (X2 :=  Sim_inj.core_after_external FSim23 d23 js2 js2' st2 st3 m1 ms e
                     vals2 ret1 rets m1' ms').
       destruct X2 as [d23' [stss' [st3' [AftExt22 [AftExt3 CMS23']]]]].
         apply CIL2.
         unfold m3 in *. apply CMS23.
         apply AtExt2. 
         apply Incr2.
         unfold m3 in *. apply Sep13.
         apply CIL'.
         apply RET'.
         apply MSQ.
         unfold ret3 in *. apply Tp3.
       rewrite AftExt2 in AftExt22. apply eq_sym in AftExt22. inv AftExt22.
       exists (d23',d12'). exists st1'. exists st3'.
       split. apply AftExt1. 
       split. unfold ret3 in *. apply AftExt3. 
       assert (ZZ:= intro_compose_match_state _ _ _ _ _ _ _ _ _ _ CMS12' CMS23'). 
          simpl in ZZ. unfold m3' in *. apply ZZ. 
  
  
 constructor.
 simpl.
       assert (NIL12':= Sim_inj.match_state_nil FSim12 _ _ _ _ _ CMS12'). subst.
 
apply  inv MSQ. unfold constructor.

       exists (d23,d12). exists 
    apply check_injectlist_split in CIL.
    destruct CIL as [[NIL CIL2] | [ms1 [ms2 [mm [M [CIL1 CIL2]]]]]].

assert (X1 :=  Sim_inj.core_after_external FSim12 d12 js1 js1' st1 st2 m1). ms e vals1 ret1 rets m1' ms').ss
    destruct X1 xx
       unfold m3. unfold m2. 
    destruct (Sim_inj.core_at_external FSim12 _ _ _ _ _ _ _ _ CMS12 AtExt1) as [ms1 [Hm2 [CIL1 [vals2 [VI2 [Tp2 AtExt2]]]]]].
    destruct (Sim_inj.core_at_external FSim23 _ _ _ _ _ _ _ _ CMS23 AtExt2) as [ms2 [Hm3 [CIL2 [vals3 [VI3 [Tpp AtExt]]]]]].
    exists (
 vals3' [MemInj2 [ValsInj2 [HasType3 AtExt3']]]].
    rewrite AtExt3 in AtExt3'. apply eq_sym in AtExt3'. inv AtExt3'.
    assert (AftExt1 := Sim_inj.core_after_external_reorder FSim12
      _ _ _ _ _ _ _ _ _ CMS12 MemInj1 AtExt1 AtExt2 ValsInj1 HasType2).
 _ _ j1' _ _ _ _ _ vals1 vals2 ret1 ret3 m1'). m2 CMS12 MemInj1  Incr1').
(*    apply Sim_inj.match_state_siminj in CMS12.
    apply Sim_inj.match_state_siminj in CMS23.*)
(*    unfold inject_separated in InjSep.*)
    destruct (inj_split _ _ _ InjIncr _ _ _ MemInj InjSep MemInj1 MemInj2)
       as [j1' [j2' [Incr1' [Incr2' JJ']]]]; subst.
xx
    unfold at_external in AtExt2. remember (csem Sem2). destruct c; simpl in *. destruct Sem2.
    unfold at_external in AtExt2.
  Qed.


  (* An axiom stating that inject forward simulations compose *)
  Lemma forward_simulation_inject_inject_compose :
    Sim_inj.Forward_simulation_inject Sem1 Sem3 ge1 ge3 entry_points13.
  Proof.
    intros. 
    eapply (@Sim_inj.Build_Forward_simulation_inject G1 C1 G3 C3 Sem1 Sem3 ge1 ge3 entry_points13 data13 numpasses13 compose_match_state).
      eapply compose_match_state_numpasses; eauto.
      eapply wf_clos_trans. apply well_founded_sem_compose_ord.
      apply compose_match_state_siminj. 
      apply compose_core_diagram.
      intros v1 v3 sig HEntry vals1 c1 m1 MIC1 IM1.
        apply (compose_core_initial v1 v3 sig HEntry vals1 c1 MIC1 m1 IM1).
      eapply compose_safely_halted; eauto.
      eapply compose_at_external; eauto.
atexternal.

  
  Lemma validblock_elim: forall m b b1 z, 
      (if zlt b (Mem.nextblock m) then Some (b, 0) else None) = Some (b1, z) ->
      b1 = b /\ z = 0.
  Proof. intros.
     remember (zlt b (Mem.nextblock m)) as zz.
     destruct zz. inv H. split; trivial. inversion H.
  Qed. 
  Lemma flat_injD: forall m b b1 delta,
       Mem.flat_inj (Mem.nextblock m) b = Some (b1, delta) -> b1 = b /\ delta = 0.
    Proof. intros. eapply validblock_elim. apply H. Qed.

  Lemma valid_block_flatinj: forall {A:Type} m b (X Y:A),
        Mem.valid_block m b -> (if zlt b (Mem.nextblock m) then X else Y) = X.
    Proof. intros.
      unfold Mem.valid_block in H.
      apply zlt_true. apply H.
    Qed.

  Lemma flatinj_compose: forall m m' 
       (Inj: Mem.inject (Mem.flat_inj (Mem.nextblock m)) m m'),
       Mem.flat_inj (Mem.nextblock m) = 
       inj_compose (Mem.flat_inj (Mem.nextblock m)) (Mem.flat_inj (Mem.nextblock m')).
    Proof.
       intros.
       apply extensionality. intros b.
       unfold inj_compose.
       remember (Mem.flat_inj (Mem.nextblock m) b) as mb.
       destruct mb; trivial.
       destruct p as [b' delta].
       apply eq_sym in Heqmb.
       destruct (flat_injD _ _ _ _ Heqmb). subst.
       assert (validb'3:= Mem.mi_mappedblocks _ _ _ Inj _ _ _ Heqmb).
       unfold Mem.flat_inj.
       rewrite valid_block_flatinj; trivial.
    Qed.

 

Lemma inj_split: forall j1 j2 j' (Incr: inject_incr (inj_compose j1 j2) j') m1 m2 m3
         (SI: Mem.inject (inj_compose j1 j2) m1 m3)
         (SEP: inject_separated (inj_compose j1 j2) j' m1 m3) 
         (SI1 : Mem.inject j1 m1 m2)
         (SI2 : Mem.inject j2 m2 m3),
exists j1', exists j2', 
   inject_incr j1 j1' /\ inject_incr j2 j2' /\ j' = inj_compose j1' j2'.
Proof. admit. Qed.
(*  intros. unfold inject_separated in SEP. destruct SI as [SIA SIB]. destruct SI1 as [SI1A SI1B]. destruct SI2 as [SI2A SI2B].
  exists (fun b => match j1 b with 
                      None => match j' b with
                                  None => None
                                | Some (b'',ofs'') => match j2 b with
                                                        None => Some (b,0)
                                                      | Some (b2,o2) => None
                                                     end
                                end
                    | Some (b',ofs') => Some (b',ofs')
                   end).
  exists (fun b => match j2 b with 
                      None => match j1 b with None => j' b
                                            | Some (b'',ofs'') => None end
                    | Some (b',ofs') => Some (b',ofs')
                   end).
  unfold inject_incr in *. intros.
  split. intros. rewrite H. trivial.
  split. intros. rewrite H. trivial.
  extensionality b.
     unfold inj_compose in *.
     remember (j1 b) as j1b.
     destruct j1b; apply eq_sym in Heqj1b.
       destruct p as [b' ofs'].
       remember (j2 b') as j2b'.
       destruct j2b'; apply eq_sym in Heqj2b'.
         destruct p as [b'' ofs''].
         specialize (Incr b b'' (ofs' + ofs'')). rewrite Heqj1b in Incr. rewrite Heqj2b' in Incr. apply (Incr (eq_refl _)).
       remember (j1 b') as j1b'.
       destruct j1b'; apply eq_sym in Heqj1b'.
         destruct p.
         remember (j' b) as j'b.
         destruct j'b; apply eq_sym in Heqj'b; trivial. destruct p.
         specialize (SEP b b1 z0). rewrite Heqj1b in SEP. rewrite Heqj2b' in SEP. rewrite Heqj'b in SEP.
         destruct (SEP (eq_refl _) (eq_refl _)).
         rewrite (SI1A _ H) in Heqj1b. congruence.
     remember (j' b) as j'b.
       destruct j'b; apply eq_sym in Heqj'b.
         destruct p.
         specialize (SEP b b0 z). rewrite Heqj1b in SEP. rewrite Heqj2b' in SEP. rewrite Heqj'b in SEP.
         destruct (SEP (eq_refl _) (eq_refl _)).
         rewrite (SI1A _ H) in Heqj1b. congruence.
     remember (j' b') as j'b'.
       destruct j'b'; apply eq_sym in Heqj'b'; trivial.
         destruct p. admit.

     assert (SPb := SEP b). rewrite Heqj1b in SPb.
     remember (j' b) as j'b.
       destruct j'b; apply eq_sym in Heqj'b.
         destruct p.
         destruct (SPb _ _ (eq_refl _) (eq_refl _)).
         remember (j2 b) as j2b.
         destruct j2b; apply eq_sym in Heqj2b.
         destruct p as [b'' ofs'']. admit. admit. trivial.
Qed.
  *)     
here

  Lemma compose_after_external: 
        forall cd j j' st1 st3 m1 m3 e vals1 vals3 ret1 ret3 m1' m3'
               (CMS: compose_match_state cd j st1 m1 st3 m3) 
               (MemInj: Mem.inject j m1 m3)
               (AtExt1: at_external Sem1 st1 = Some (e, vals1))
               (AtExt3: at_external Sem3 st3 = Some (e, vals3))
               (ValsInj: Forall2 (val_inject j) vals1 vals3) 
               (InjIncr: inject_incr j j')
               (InjSep: inject_separated j j' m1 m3)
               (MemInj': Mem.inject j' m1' m3')
               (ValInj': val_inject j' ret1 ret3)
               (unchangedUM1: mem_unchanged_on (loc_unmapped j) m1 m1')
               (unchangedOOR: mem_unchanged_on (loc_out_of_reach j m1) m3 m3')
               (FWD1: mem_forward m1 m1')
               (FWD3: mem_forward m3 m3')
               (ArgsHasTp: Forall2 Val.has_type vals3 (sig_args (ef_sig e)))
               (RetHasTp: Val.has_type ret3 (proj_sig_res (ef_sig e))),
        exists cd', exists st1', exists st3',
          after_external Sem1 ret1 st1 = Some st1' /\
          after_external Sem3 ret3 st3 = Some st3' /\
          compose_match_state cd' j' st1' m1' st3' m3'.
  Proof. intros.
    inv CMS. rename c2 into st2. rename H into CMS12. rename H0 into CMS23.
    destruct (Sim_inj.core_at_external FSim12 _ _ _ _ _ _ _ _ CMS12 AtExt1) as [vals2 [MemInj1 [ValsInj1 [HasType2 AtExt2]]]].
    destruct (Sim_inj.core_at_external FSim23 _ _ _ _ _ _ _ _ CMS23 AtExt2) as [vals3' [MemInj2 [ValsInj2 [HasType3 AtExt3']]]].
    rewrite AtExt3 in AtExt3'. apply eq_sym in AtExt3'. inv AtExt3'.
    assert (AftExt1 := Sim_inj.core_after_external_reorder FSim12
      _ _ _ _ _ _ _ _ _ CMS12 MemInj1 AtExt1 AtExt2 ValsInj1 HasType2).
 _ _ j1' _ _ _ _ _ vals1 vals2 ret1 ret3 m1'). m2 CMS12 MemInj1  Incr1').
(*    apply Sim_inj.match_state_siminj in CMS12.
    apply Sim_inj.match_state_siminj in CMS23.*)
(*    unfold inject_separated in InjSep.*)
    destruct (inj_split _ _ _ InjIncr _ _ _ MemInj InjSep MemInj1 MemInj2)
       as [j1' [j2' [Incr1' [Incr2' JJ']]]]; subst.
xx
    unfold at_external in AtExt2. remember (csem Sem2). destruct c; simpl in *. destruct Sem2.
    unfold at_external in AtExt2.
  Qed.

  (* An axiom stating that inject forward simulations compose *)
  Lemma forward_simulation_inject_inject_compose :
    Sim_inj.Forward_simulation_inject Sem1 Sem3 ge1 ge3 entry_points13.
  Proof.
    intros.
    eapply (@Sim_inj.Build_Forward_simulation_inject G1 C1 G3 C3 Sem1 Sem3 ge1 ge3 entry_points13 _ compose_match_state).
      eapply wf_clos_trans. apply well_founded_sem_compose_ord.
      apply compose_match_state_siminj. 
      apply compose_core_diagram.
      intros v1 v3 sig HEntry vals1 vals3 m1 m3 j M3SI V3SI valsInj valsTp Minj.
        apply (compose_core_initial v1 v3 sig HEntry vals1 vals3 m1 m3 j); trivial.
      eapply compose_safely_halted; eauto.
      eapply compose_at_external; eauto.
atexternal.
      

v1 v3 sig
       (HEntry: In (v1, v3, sig) entry_points13)
       (vals1 vals3 : list val) (m1 m3 : mem)
       j (HypJ: j = Mem.flat_inj (Mem.nextblock m1))
       (Mem3SelfInj: Mem.inject (Mem.flat_inj (Mem.nextblock m3)) m3 m3)
       (Vals3SelfInj: Forall2 (val_inject (Mem.flat_inj (Mem.nextblock m3))) vals3 vals3),
       Forall2 (val_inject j) vals1 vals3 ->
       Forall2 Val.has_type vals3 (sig_args sig) ->
       Mem.inject j m1 m3 ->
       exists cd : data13, exists c1 : C1, exists c3 : C3,
          make_initial_core Sem1 ge1 v1 vals1 = Some c1 /\
          make_initial_core Sem3 ge3 v3 vals3 = Some c3 /\
          compose_match_state cd j c1 m1 c3 m3.
  Lemma compose_core_initial: forall v1 v3 sig
       (HEntry: In (v1, v3, sig) entry_points13)
       (vals1 vals3 : list val) (m1 m3 : mem)
       j (HypJ: j = Mem.flat_inj (Mem.nextblock m1))
       (Mem3SelfInj: Mem.inject (Mem.flat_inj (Mem.nextblock m3)) m3 m3)
       (Vals3SelfInj: Forall2 (val_inject (Mem.flat_inj (Mem.nextblock m3))) vals3 vals3),
       Forall2 (val_inject j) vals1 vals3 ->
       Forall2 Val.has_type vals3 (sig_args sig) ->
       Mem.inject j m1 m3 ->
       exists cd : data13, exists c1 : C1, exists c3 : C3,
          make_initial_core Sem1 ge1 v1 vals1 = Some c1 /\
          make_initial_core Sem3 ge3 v3 vals3 = Some c3 /\
          compose_match_state cd j c1 m1 c3 m3.
  Proof.
    intros.
    assert (J1: exists v2, In (v1,v2,sig) entry_points12 /\ In (v2,v3,sig) entry_points23).
      pose proof EPC as myEPC.
      clear - HEntry myEPC.
      induction myEPC.
      simpl in HEntry. destruct HEntry. inv H.
      exists v2; split; simpl; auto.
      destruct (IHmyEPC H) as [v2' [? ?]].
      exists v2'; simpl; split; auto.
      inv HEntry.
   destruct J1 as [v2 [J12 J23]].
    generalize (Sim_inj.core_initial FSim12 _ _ _ J12); intro CI12.

    specialize (CI12 vals1 vals3 m1 m3 Mem3SelfInj Vals3SelfInj).
    destruct CI12 as [d12 [c1 [c2 [MIC1 [MIC2 MS12]]]]].
    (*1*)  subst. assumption.
    (*2*)  subst. assumption.
    (*3*)  subst. assumption.
    generalize (Sim_inj.core_initial FSim23 _ _ _ J23); intro CI23.
    specialize (CI23 vals3 vals3 m3 m3 Mem3SelfInj Vals3SelfInj).
    destruct CI23 as [d23 [c2' [c3 [MIC2' [MIC3 MS23]]]]]; trivial.
       (*1 subst.
       clear MS12 MIC1 MIC2 c1 c2. subst. remember (sig_args sig) as types. 
           clear - H H0 H1 SelfInj3.
           generalize dependent vals1. generalize dependent types.
           induction vals3; intros; simpl.
           (*Nil*) apply Forall2_nil.
           (*Cons*)
             inv H. inv H0. rename y into typA. rename x into a1. rename a into a3.
             apply Forall2_cons.
               Focus 2. eapply IHvals3. apply H7. apply H6.
               clear H6 H7.
               inversion H5; subst; clear H5; try constructor.
                 
                    assert (validj_m3b:= Mem.mi_mappedblocks _ _ _ H1 _ _ _ H).
                    unfold Mem.flat_inj; simpl.
                    econstructor. eapply valid_block_flatinj. assumption.
                      rewrite Int.add_zero. trivial.
                  
                 destruct a3; try constructor. 
                    assert (validj_m3b:= Mem.mi_mappedblocks _ _ _ SelfInj3).  _ _ _ H).
                    unfold Mem.flat_inj; simpl.
                    econstructor. eapply valid_block_flatinj. assumption.
                      rewrite Int.add_zero. trivial.econstructor.*)
    assert (c2' = c2) by congruence. subst.
    exists (d23,d12). (*(Some c2_,m2'),d23'').*)
    exists c1. exists c3.
    split; trivial.
    split; trivial.
    rewrite (flatinj_compose _ _ H1).
    econstructor; eauto.
  Qed.

  Lemma compose_safely_halted:
     forall d j c1 m1 c3 m3 v1 (CMS:compose_match_state d j c1 m1 c3 m3)
        (SH: safely_halted Sem1 ge1 c1 = Some v1),
        safely_halted Sem3 ge3 c3 = Some v1 /\ Mem.inject j m1 m3.
     Proof.
       intros.
       inv CMS. rename H into CMS12. rename H0 into CMS23.
       destruct (Sim_inj.core_halted FSim12 _ _ _ _ _ _ _ CMS12 SH) as [SH2 Inj1].
       destruct (Sim_inj.core_halted FSim23 _ _ _ _ _ _ _ CMS23 SH2) as [SH3 Inj2].
       split; trivial.
       eapply (Mem.inject_compose _ _ _ _ _ Inj1 Inj2).
     Qed.
 
  Lemma compose_at_external: forall cd j st1 m1 st3 m3 e vals1
           (CMS: compose_match_state cd j st1 m1 st3 m3)
           (AtExt1: at_external Sem1 st1 = Some (e, vals1)),
       exists ms : list mem,
  m2 = last ms m1 /\
  Sim_inj.check_injectlist js m1 ms /\
  (exists vals2 : list val,
     Forall2 (val_inject (injlist_compose js)) vals1 vals2 /\
     Forall2 Val.has_type vals2 (sig_args (ef_sig e)) /\
     at_external Sem3 st2 = Some (e, vals2)) exists vals3,
           Mem.inject j m1 m3 /\
           Forall2 (val_inject j) vals1 vals3 /\
           Forall2 Val.has_type vals3 (sig_args (ef_sig e)) /\
           at_external Sem3 st3 = Some (e, vals3).
  Proof.
    intros.
    inv CMS. rename c2 into st2. rename H into CMS12. rename H0 into CMS23.
    destruct (Sim_inj.core_at_external FSim12 _ _ _ _ _ _ _ _ CMS12 AtExt1) as [vals2 [MemInj1 [ValsInj1 [HasType2 AtExt2]]]].
    destruct (Sim_inj.core_at_external FSim23 _ _ _ _ _ _ _ _ CMS23 AtExt2) as [vals3 [MemInj2 [ValsInj2 [HasType3 AtExt4]]]].
    exists vals3.
    split. eapply (Mem.inject_compose _ _ _ _ _ MemInj1 MemInj2).
    split. apply (vals_inject_compose _ _ _ ValsInj1 _ _ ValsInj2).
    split; trivial.
  Qed.

  Lemma compose_core_initial: forall v1 v3 sig
       (HEntry: In (v1, v3, sig) entry_points13)
       (vals1 vals3 : list val) (m1 m3 : mem)
       j (HypJ: j = Mem.flat_inj (Mem.nextblock m1))
       (Mem3SelfInj: Mem.inject (Mem.flat_inj (Mem.nextblock m3)) m3 m3)
       (Vals3SelfInj: Forall2 (val_inject (Mem.flat_inj (Mem.nextblock m3))) vals3 vals3),
       Forall2 (val_inject j) vals1 vals3 ->
       Forall2 Val.has_type vals3 (sig_args sig) ->
       Mem.inject j m1 m3 ->
       exists cd : data13, exists c1 : C1, exists c3 : C3,
          make_initial_core Sem1 ge1 v1 vals1 = Some c1 /\
          make_initial_core Sem3 ge3 v3 vals3 = Some c3 /\
          compose_match_state cd j c1 m1 c3 m3.
  Proof. intros.
    assert (J1: exists v2, In (v1,v2,sig) entry_points12 /\ In (v2,v3,sig) entry_points23).
      pose proof EPC as myEPC.
      clear - HEntry myEPC.
      induction myEPC.
      simpl in HEntry. destruct HEntry. inv H.
      exists v2; split; simpl; auto.
      destruct (IHmyEPC H) as [v2' [? ?]].
      exists v2'; simpl; split; auto.
      inv HEntry.
   destruct J1 as [v2 [J12 J23]].
    generalize (Sim_inj.core_initial FSim12 _ _ _ J12); intro CI12.

    specialize (CI12 vals1 vals3 m1 m3 Mem3SelfInj Vals3SelfInj).
    destruct CI12 as [d12 [c1 [c2 [MIC1 [MIC2 MS12]]]]].
    (*1*)  subst. assumption.
    (*2*)  subst. assumption.
    (*3*)  subst. assumption.
    generalize (Sim_inj.core_initial FSim23 _ _ _ J23); intro CI23.
    specialize (CI23 vals3 vals3 m3 m3 Mem3SelfInj Vals3SelfInj).
    destruct CI23 as [d23 [c2' [c3 [MIC2' [MIC3 MS23]]]]]; trivial.
       (*1 subst.
       clear MS12 MIC1 MIC2 c1 c2. subst. remember (sig_args sig) as types. 
           clear - H H0 H1 SelfInj3.
           generalize dependent vals1. generalize dependent types.
           induction vals3; intros; simpl.
           (*Nil*) apply Forall2_nil.
           (*Cons*)
             inv H. inv H0. rename y into typA. rename x into a1. rename a into a3.
             apply Forall2_cons.
               Focus 2. eapply IHvals3. apply H7. apply H6.
               clear H6 H7.
               inversion H5; subst; clear H5; try constructor.
                 
                    assert (validj_m3b:= Mem.mi_mappedblocks _ _ _ H1 _ _ _ H).
                    unfold Mem.flat_inj; simpl.
                    econstructor. eapply valid_block_flatinj. assumption.
                      rewrite Int.add_zero. trivial.
                  
                 destruct a3; try constructor. 
                    assert (validj_m3b:= Mem.mi_mappedblocks _ _ _ SelfInj3).  _ _ _ H).
                    unfold Mem.flat_inj; simpl.
                    econstructor. eapply valid_block_flatinj. assumption.
                      rewrite Int.add_zero. trivial.econstructor.*)
    assert (c2' = c2) by congruence. subst.
    exists (d23,d12). (*(Some c2_,m2'),d23'').*)
    exists c1. exists c3.
    split; trivial.
    split; trivial.
    rewrite (flatinj_compose _ _ H1).
    econstructor; eauto.
  Qed.

  Lemma compose_safely_halted:
     forall d j c1 m1 c3 m3 v1 (CMS:compose_match_state d j c1 m1 c3 m3)
        (SH: safely_halted Sem1 ge1 c1 = Some v1),
        safely_halted Sem3 ge3 c3 = Some v1 /\ Mem.inject j m1 m3.
     Proof.
       intros.
       inv CMS. rename H into CMS12. rename H0 into CMS23.
       destruct (Sim_inj.core_halted FSim12 _ _ _ _ _ _ _ CMS12 SH) as [SH2 Inj1].
       destruct (Sim_inj.core_halted FSim23 _ _ _ _ _ _ _ CMS23 SH2) as [SH3 Inj2].
       split; trivial.xx
  (* An axiom stating that inject forward simulations compose *)
  Lemma forward_simulation_inject_inject_compose :
    Sim_inj.Forward_simulation_inject Sem1 Sem3 ge1 ge3 entry_points13.
  Proof.
    intros.
    eapply (@Sim_inj.Build_Forward_simulation_inject G1 C1 G3 C3 Sem1 Sem3 ge1 ge3 entry_points13 _ compose_match_state).
      eapply wf_clos_trans. apply well_founded_sem_compose_ord.
      apply compose_match_state_siminj. 
      apply compose_core_diagram.
      intros v1 v3 sig HEntry vals1 vals3 m1 m3 j M3SI V3SI valsInj valsTp Minj.
        apply (compose_core_initial v1 v3 sig HEntry vals1 vals3 m1 m3 j); trivial.
      

  (* An axiom stating that inject forward simulations compose *)
  Lemma forward_simulation_inject_inject_compose :
    Sim_inj.Forward_simulation_inject Sem1 Sem3 ge1 ge3 entry_points13.
  Proof.
    intros.
    eapply (@Sim_inj.Build_Forward_simulation_inject G1 C1 G3 C3 Sem1 Sem3 ge1 ge3 entry_points13 _ compose_match_state).
      eapply wf_clos_trans. apply well_founded_sem_compose_ord.
      apply compose_match_state_siminj. 
      apply fsim_compose_diagram.
intros.
     
      
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
              clos_trans _ (lex_ord (Sim_inj.core_ord FSim23) (Sim_inj.core_ord FSim12)) cd' cd).
   Proof.
    intros. inv H0. rename c2 into st2.
    destruct (Sim_inj.core_diagram FSim12 st1 m1 st1' m1'  H d12 st2 j1 m2 H1) as
      [st2' [m2' [d12' [j1' [Hj1' [Sep12 [MS12 Step2]]]]]]].
    assert (H5: corestep_plus Sem2 ge2 st2 m2 st2' m2' \/
               ((st2,m2) = (st2',m2') /\ Sim_inj.core_ord FSim12 d12' d12) ).
      destruct Step2. auto.
      destruct H0.
        destruct H0.
        destruct x. right. split; auto.
                    left. exists x; auto.
    clear Step2.
    assert (Inj1 := Sim_inj.match_state_siminj _ _ _ _ _ _ _ H1). 
    assert (Inj2 := Sim_inj.match_state_siminj _ _ _ _ _ _ _ H2).
    destruct H5 as [Step2 | [SEQ Ord]].
    (*case corestep_plus Sem2 ge2 st2 m2 st2' m2'*)
      destruct Step2.
      destruct Inj1 as [Inj1A Inj1B]. clear Inj1A.
      destruct Inj2 as [Inj2A Inj2B]. clear Inj2B. 
      apply csem_allowed_modifications in H. rename H into AM1.
      assert (AM2:= corestepN_allowed_modifications H0).
      clear H1. clear st1 st1.
      assert (AUX := @InjInj_AUX _ _ _ _ _ _ _ _ _ FSim23 _ _ _ _ _ H0 _ _ _ _ H2).
      destruct AUX as [st3' [m3' [d' [j2' [AM3 [Incr2 [Sep2 [MS EXEC]]]]]]]].
      exists st3'. exists m3'. exists (d',d12'). exists (inj_compose j1' j2'). 
      split. eapply inject_incr_compose. apply Hj1'. apply Incr2.
      split. (* (Incr1 : inject_incr j1 j1')
                (Incr2 : inject_incr j2 j2')
                (Sep12 : inject_separated j1 j1' m1 m2)
                (Sep23: inject_separated j2 j2' m2 m3),
                inject_separated (inj_compose j1 j2) (inj_compose j1' j2') m1 m3*)
              eapply inject_separated_compose. apply Hj1'. apply Incr2. apply Inj1B. apply Inj2A. apply Sep12. apply Sep2.
      split. econstructor. apply MS12. apply MS.
      destruct EXEC as [ExecPlus | [ExecStar Ord]].
        left; assumption.
        right. split; try assumption.
               eapply lex_ord_left. apply Ord.
    (*case (st2, m2) = (st2', m2') /\ Sim_inj.core_ord FSim12 d' d12*)
      inv SEQ. 
      exists st3. exists m3. exists (d23, d12'). (*was : exists (d',(Some c2,m2),d23).*)
      exists (inj_compose j1' j2).
      split. eapply inject_incr_compose. apply Hj1'. apply inject_incr_refl. 
      split. eapply inject_separated_compose. (*alternative : eapply inject_separated_siminj_compose.*)
               apply Hj1'. 
               apply inject_incr_refl.
               apply Inj1.
               apply Inj2. 
               apply Sep12.
               intros b; intros. congruence.
      split. econstructor. apply MS12. apply H2. 
      right. split. exists O. simpl; auto.
      apply lex_ord_right. apply Ord.
Qed.

  (* An axiom stating that inject forward simulations compose *)
  Lemma forward_simulation_inject_inject_compose :
    Sim_inj.Forward_simulation_inject Sem1 Sem3 ge1 ge3 entry_points13.
  Proof.
    intros.
    eapply (@Sim_inj.Build_Forward_simulation_inject G1 C1 G3 C3 Sem1 Sem3 ge1 ge3 entry_points13 _ compose_match_state).
      apply well_founded_sem_compose_ord.
      apply compose_match_state_siminj. 
      apply fsim_compose_diagram.
     ss
      
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