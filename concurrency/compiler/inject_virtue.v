Require Import Omega.

Require Import Coq.Classes.Morphisms.
Require Import Relation_Definitions.

Require Import compcert.common.Globalenvs.
Require Import compcert.common.ExposedSimulations.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.lib.Coqlib.

Require Import VST.concurrency.lib.tactics.
Require Import VST.concurrency.common.permissions. Import permissions.
Require Import VST.concurrency.compiler.advanced_permissions.
Require Import VST.concurrency.common.semantics. 
Require Import VST.concurrency.common.HybridMachine.
Require Import VST.concurrency.compiler.mem_equiv.
Require Import VST.concurrency.compiler.pair.
Require Import VST.concurrency.memsem_lemmas.
Require Import VST.concurrency.common.bounded_maps.
Require Import VST.concurrency.lib.Coqlib3.


Section VirtueInject.
  

  Fixpoint build_function_for_a_block
           (mu:meminj) {A} (b: positive) (ls: list (positive * (Z -> option A))):
    Z -> option A:=
    match ls with
    | nil => (fun _ => None)
    | (b0, fb)::ls' =>
      match mu b0 with
      | Some (b1, delt) =>
        if PMap.elt_eq b b1 then
          merge_func (fun p => (fb (p - delt)%Z)) (build_function_for_a_block mu b ls')
        else  (build_function_for_a_block mu b ls')
      | None => (build_function_for_a_block mu b ls') 
      end
    end.
  
  Definition tree_map_inject_over_tree {A B}
             (t:PTree.t (Z -> option B))(mu:meminj) (map:PTree.t (Z -> option A)):
    PTree.t (Z -> option A):=
    PTree.map (fun b _ => build_function_for_a_block mu b (PTree.elements map)) t.

  Definition tree_map_inject_over_mem {A} m mu map:
    PTree.t (Z -> option A) :=
    tree_map_inject_over_tree (snd (getMaxPerm m)) mu map.
  
  (* apply an injections to the elements of a tree. *)
  Fixpoint apply_injection_elements {A}
           (mu:meminj) (ls: list (positive * (Z -> option A)))
    : list (positive * (Z -> option A)) :=
    match ls with
      nil => nil
    | cons (b, ofs_f) ls' =>
      match (mu b) with
      | None => apply_injection_elements mu ls'
      | Some (b',d) =>
        cons (b', fun ofs => ofs_f (ofs-d)%Z)
             (apply_injection_elements mu ls')
      end
    end.
  Fixpoint extract_function_for_block
           {A} (b: positive) (ls: list (positive * (Z -> option A)))
    : Z -> option A :=
    match ls with
      nil => fun _ => None
    | cons (b', ofs_f') ls' =>
      if (Pos.eq_dec b b') then
        merge_func ofs_f' (extract_function_for_block b ls')
      else (extract_function_for_block b ls')
    end.

  Fixpoint map_from_list
           {A:Type}
           (mu:meminj) (ls: list (positive * (Z -> option A))):
    PTree.t (Z -> option A) :=
    match ls with
      nil => @PTree.empty (BinNums.Z -> option A)
    | cons (b, ofs_f) ls =>
      let t:= map_from_list mu ls in
      match mu b with
        None => t
      | Some (b',d) =>
        match PTree.get b' t with
          None => PTree.set b' (fun ofs => ofs_f (ofs-d)%Z) t
        | Some f_old =>
          PTree.set b' (merge_func (fun ofs => ofs_f (ofs-d)%Z) f_old) t
        end end end.

  Definition tree_map_inject {A}(mu:meminj) (map:PTree.t (Z -> option A)):
    PTree.t (Z -> option A):=
    map_from_list mu (PTree.elements map).
  Definition virtueThread_inject m (mu:meminj) (virtue:delta_map * delta_map):
    delta_map * delta_map:=
    pair1 (tree_map_inject_over_mem m mu) virtue.
  Hint Unfold virtueThread_inject: pair.

  (*NOTE: default is set to (fun _=> None)
          used to be, [fst map] but this makes no sense since it is not "mapped"
          it rellied in the fact that fst map s empty... which is the same...
   *)
  Definition inject_access_map m (mu:meminj) (map:access_map): access_map:=
    ((* fst map*) (fun _=> None)  , tree_map_inject_over_mem m mu (snd map)).

  Lemma tree_map_inject_over_mem_correct:
    forall {A} m2 mu (perm:PTree.t (Z -> option A)) b1 b2 ofs delt,
      mu b1 = Some (b2, delt) ->
      Mem.perm m2 b2 (ofs + delt) Max Nonempty -> 
      (tree_map_inject_over_mem m2 mu perm) ! b2 =
      Some (build_function_for_a_block
              mu b2 (PTree.elements perm)).
  Proof.
    unfold tree_map_inject_over_mem, tree_map_inject_over_tree.
    intros. rewrite PTree.gmap.
    unfold Mem.perm,Mem.perm_order' in *.
    unfold PMap.get in H0.
    destruct ((snd (Mem.mem_access m2)) ! b2) eqn:HH. 
    2: { rewrite Clight_bounds.Mem_canonical_useful in H0; inv H0. }
    unfold getMaxPerm; simpl.
    rewrite PTree.gmap1.
    rewrite HH; simpl.
    reflexivity.
  Qed.
  Lemma build_function_for_a_block_correct_backwards:
    forall {A} (mu:meminj) b2 ofs_delt perm elements,
      @build_function_for_a_block mu A b2 elements ofs_delt = Some perm ->
      exists b1 delt ofs f, mu b1 = Some (b2, delt) /\
                            ofs_delt = ofs + delt /\
                            In (b1,f) elements /\
                            f ofs = Some perm.
  Proof.
    intros *.
    induction elements; simpl; intros HH.
    - congruence.
    - destruct a as (b1', f').
      unfold merge_func in *.
      repeat match_case in HH; subst;
        try solve[eapply IHelements in HH; normal; eauto].
      + inv HH; do 4 eexists; repeat weak_split eauto.
        omega.
  Qed.


  (** *No overlap*)
  Definition no_overlap {A} (f:meminj) (perms:PMap.t (Z -> option A)):=
    forall b1 b1' delta1 b2 b2' delta2 ofs1 ofs2,
      b1 <> b2 ->
      f b1 = Some (b1', delta1) ->
      f b2 = Some (b2', delta2) ->
      at_least_Some (perms !! b1 ofs1)  ->
      at_least_Some (perms !! b2 ofs2) ->
      b1' <> b2' \/ ofs1 + delta1 <> ofs2 + delta2.
  Definition dmap_no_overlap (f:meminj) (dm:delta_map):=
    no_overlap f (fun _ : Z => None, dm).
  Definition list_no_overlap {A} (mu:meminj) elements:Prop:=
    forall b1 b1' delta b2 delta' ofs ofs' f f' (perm perm': A) ,
      b1 <> b1' ->
      mu b1 = Some(b2, delta) ->
      mu b1' = Some(b2, delta') ->
      In (b1,f) elements ->
      In (b1',f') elements ->
      f ofs = Some perm ->
      f' ofs' = Some perm' ->
      ofs + delta <> ofs' + delta'.
  Definition list_no_overlap_one {A} (mu:meminj) b1 b2 ofs elements:Prop:=
    forall delta,
      mu b1 = Some (b2, delta) ->
      forall b1' f' ofs' delta' (perm':A),
        b1 <> b1' ->
        mu b1' = Some(b2, delta') ->
        In (b1',f') elements ->
        f' ofs' = Some perm' ->
        ofs' + delta' <> ofs + delta.
  Lemma list_no_overlap_to_one:
    forall {A} mu elements,
      @list_no_overlap A mu elements ->
      forall b1 b2 ofs f perm,
        In (b1, f) elements -> f ofs = Some perm ->
        list_no_overlap_one mu b1 b2 ofs elements.
  Proof. intros ** ? **. symmetry. eapply H; eauto. Qed.
  Lemma list_perm_no_overlap:
    forall {A} mu p,
      @no_overlap A mu p ->
      list_no_overlap mu (PTree.elements (snd p)).
  Proof.
    unfold no_overlap, list_no_overlap.
    simpl; intros.
    exploit H; eauto.
    - unfold PMap.get; erewrite PTree.elements_complete; eauto.
      eapply at_least_Some_trivial; eassumption.
    - unfold PMap.get; erewrite PTree.elements_complete; eauto.
      eapply at_least_Some_trivial; eassumption.
    - intros [? | ?]; eauto.
  Qed.
  
  Lemma list_dmap_no_overlap:
    forall mu p,
      dmap_no_overlap mu p ->
      list_no_overlap mu (PTree.elements p).
  Proof.
    unfold dmap_no_overlap, list_no_overlap.
    simpl; intros.
    exploit H; eauto.
    - unfold dmap_get, PMap.get, PTree.get; erewrite PTree.elements_complete; eauto.
      eapply at_least_Some_trivial. rewrite H5; eauto.
    - unfold dmap_get, PMap.get, PTree.get; erewrite PTree.elements_complete; eauto.
      eapply at_least_Some_trivial.  rewrite H6; eauto.
    - intros [? | ?]; eauto.
  Qed.
  
  
  
  Lemma build_function_for_a_block_correct_forward:
    forall {A} (mu:meminj) b2 ofs delta f b1 perms elements,
      mu b1 = Some (b2, delta) ->
      In (b1,f) elements ->
      f ofs = Some perms ->
      list_no_overlap_one mu b1 b2 ofs elements ->
      list_norepet (map fst elements) ->
      @build_function_for_a_block mu A b2 elements (ofs + delta) =
      Some perms.
  Proof.
    intros *. induction elements; simpl; intros; subst.
    - inv H0.
    - inv H3.
      destruct H0.
      + subst. rewrite H.
        repeat match_case; subst.
        unfold merge_func.
        replace (ofs + delta - delta) with ofs by omega.
        rewrite H1; auto.
      + unfold merge_func.
        assert (list_no_overlap_one mu b1 b2 ofs ( elements)).
        { intros ? **. eapply H2; eauto. right; auto. }
        
        repeat match_case; subst;
          try solve[eapply IHelements; eauto].
        exploit (H2 _ H b o); eauto.
        * clear - H6 H0; simpl in *.
          intros ?; subst.
          apply H6. revert H0; clear.
          induction elements; auto.
          simpl; intros. destruct H0; subst; auto.
        * constructor; auto.
        * omega.
        * intros HH; inv HH.
  Qed.


  Lemma tree_map_inject_over_mem_correct_backwards:
    forall {A} m2 mu dmap b2 fp ofs_delta p,
      (@tree_map_inject_over_mem A m2 mu dmap) ! b2 = Some fp ->
      fp ofs_delta = Some p ->
      exists b1 (delt ofs:Z) fp1, mu b1 = Some (b2, delt) /\
                                  ofs_delta = ofs + delt /\
                                  dmap ! b1 = Some fp1 /\
                                  fp1 ofs = Some p.
  Proof.
    unfold tree_map_inject_over_mem,
    tree_map_inject_over_tree,dmap_get; simpl; intros.
    rewrite PTree.gmap , PTree.gmap1 in H.
    unfold option_map in H.
    destruct ((snd (Mem.mem_access m2)) ! b2) eqn:HH.
    2:{ simpl in H; congruence. }
    inversion H.
    rewrite <- H2 in H0.
    apply build_function_for_a_block_correct_backwards in H0.
    normal; eauto.
    eapply PTree.elements_complete; auto.
  Qed.

  Lemma tree_map_inject_over_mem_correct_forward:
    forall (mu:meminj) m2 b2 ofs delta b1 (dmap: delta_map) p,
      mu b1 = Some (b2, delta) ->
      dmap_get dmap b1 ofs = Some p ->
      ( option_implication (dmap ! b1) ((snd (getMaxPerm m2)) ! b2) )->
      dmap_no_overlap mu dmap ->
      dmap_get (tree_map_inject_over_mem m2 mu dmap) b2 (ofs + delta) = Some p.
  Proof.
    intros. 
    specialize H1.
    unfold tree_map_inject_over_mem,
    tree_map_inject_over_tree,dmap_get, PMap.get in *;
      simpl in *; intros.
    repeat match_case in H0; try congruence.
    rewrite PTree.gmap, PTree.gmap1; unfold option_map.
    unfold getMaxPerm in H1.
    simpl in *. rewrite PTree.gmap1 in H1; simpl.
    destruct ((snd (Mem.mem_access m2)) ! b2) eqn:HH.
    2:{ inv H1. }
    simpl in *.
    exploit (@build_function_for_a_block_correct_forward (option permission)); eauto.
    - eapply PTree.elements_correct.
      unfold dmap_get in *.
      rewrite Heqo. reflexivity.
    - eapply list_no_overlap_to_one; eauto.
      + eapply list_dmap_no_overlap; eauto.
      + eapply PTree.elements_correct; eauto.
    - apply PTree.elements_keys_norepet.
  Qed.
  
  Lemma tree_map_inject_over_mem_correct_forward_perm:
    forall (mu:meminj) m2 b2 ofs delta b1 (perm: access_map) p,
      mu b1 = Some (b2, delta) ->
      perm !! b1 ofs = Some p ->
      isCanonical perm ->
      (option_implication ((snd perm) ! b1) ((snd (getMaxPerm m2)) ! b2) ) ->
      no_overlap mu perm ->
      (fun _ => None, tree_map_inject_over_mem m2 mu (snd perm)) !! b2 (ofs + delta)
      = Some p.
  Proof.
    intros. 
    unfold tree_map_inject_over_mem,
    tree_map_inject_over_tree,dmap_get in *; simpl; intros.
    unfold PMap.get in *; simpl in *.
    repeat match_case in H0; try congruence.
    2:{ rewrite H1 in H0; congruence. }
    rewrite PTree.gmap, PTree.gmap1; unfold option_map.
    simpl in *. rewrite PTree.gmap1 in H2; simpl.
    destruct ((snd (Mem.mem_access m2)) ! b2) eqn:HH.
    2:{ inv H2. }
    simpl in *.
    exploit (@build_function_for_a_block_correct_forward); eauto.
    - eapply PTree.elements_correct.
      eapply Heqo.
    - eapply list_no_overlap_to_one; eauto.
      + eapply list_perm_no_overlap; eauto.
      + eapply PTree.elements_correct; eauto.
    - apply PTree.elements_keys_norepet.
  Qed.
  
  Lemma dmap_inject_correct_backwards:
    forall m2 mu dmap b2 ofs_delt p,
      dmap_get (tree_map_inject_over_mem m2 mu dmap) b2 (ofs_delt) = Some p ->
      exists b1 delt ofs, mu b1 = Some (b2, delt) /\
                          ofs_delt = ofs + delt /\
                          dmap_get dmap b1 ofs = Some p.
  Proof.
    unfold dmap_get, PMap.get; intros.
    repeat match_case in H.
    - inv H. eapply tree_map_inject_over_mem_correct_backwards in Heqo; eauto.
      normal; eauto. simpl. rewrite H1, H2; auto.
  Qed.
  
  Lemma inject_access_map_correct_backwards:
    forall m2 mu perms b2 ofs_delt p,
      (inject_access_map m2 mu perms) !! b2 (ofs_delt) = Some p ->
      exists b1 delt ofs, mu b1 = Some (b2, delt) /\
                          ofs_delt = ofs + delt /\
                          perms !! b1 ofs = Some p.
  Proof.
    unfold PMap.get; intros. repeat match_case in H; try congruence.
    simpl in *.
    eapply tree_map_inject_over_mem_correct_backwards in Heqo; eauto.
    normal; eauto. rewrite H2; auto.
  Qed.
  
  Lemma inject_access_map_correct_forward:
    forall (mu:meminj) m2 b2 ofs delta b1 perms p,
      mu b1 = Some (b2, delta) ->
      isCanonical perms ->
      perms !! b1 ofs = Some p ->
      (forall ofs, Mem.perm_order''
                     ((getMaxPerm m2) !! b2 (ofs+delta)) (perms !! b1 ofs)) ->
      no_overlap mu perms ->
      (inject_access_map m2 mu perms) !! b2 (ofs + delta) = Some p.
  Proof.
    intros.
    unfold inject_access_map, tree_map_inject_over_mem,
    tree_map_inject_over_tree,PMap.get; simpl.
    rewrite PTree.gmap, PTree.gmap1; unfold option_map.
    destruct ((snd (Mem.mem_access m2)) ! b2) eqn:HH.
    2: { unfold PMap.get in H1.
         specialize (H2 ofs); rewrite getMaxPerm_correct in H2.
         unfold permission_at, PMap.get in H2. rewrite HH in H2.
         rewrite Clight_bounds.Mem_canonical_useful in H2.
         match_case in H1. rewrite H1 in H2; inv H2.
         rewrite H0 in H1. congruence. }
    eapply build_function_for_a_block_correct_forward; eauto.
    - eapply PTree.elements_correct.
      unfold PMap.get in *.
      match_case in H1; auto.
      rewrite H0 in H1; congruence.
    - unfold PMap.get in H1.
      match_case in H1.
      + eapply list_no_overlap_to_one; eauto.
        eapply list_perm_no_overlap; auto.
        eapply PTree.elements_correct. auto.
      + rewrite H0 in H1; congruence.
    - apply PTree.elements_keys_norepet.
  Qed.
  
  Definition virtueLP_inject m (mu:meminj):
    (Pair access_map) -> Pair access_map :=
    pair1 (inject_access_map m mu).

  
  Lemma inject_virtue_sub_map:
    forall (m1 m2 : mem)
      (mu : meminj)
      {A} (virtue1 : PTree.t (Z -> option A))
      perm1 perm2 Hlt1 Hlt2,
      Mem.inject mu (@restrPermMap perm1 m1 Hlt1 ) 
                 (@restrPermMap perm2 m2 Hlt2 ) ->
      sub_map virtue1 (snd (getMaxPerm m1)) ->
      sub_map (tree_map_inject_over_mem m2 mu virtue1)
              (snd (getMaxPerm m2)).
  Proof.
    intros m1 m2 mu AT virtue1 perm1 perm2 Hlt1 Hlt2 injmem A.
    pose proof (Mem.mi_inj _ _ _ injmem) as injmem'.
    clear injmem.
    rename injmem' into injmem.
    replace  (snd (getMaxPerm m2)) with
        (PTree.map (fun _ a => a)  (snd (getMaxPerm m2))) by eapply trivial_map.
      unfold tree_map_inject_over_mem, tree_map_inject_over_tree.
      pose proof (@strong_tree_leq_map') as HHH.
      specialize (HHH _ (Z -> option AT)
                      (fun (b : positive) _ =>
                         build_function_for_a_block mu b (PTree.elements virtue1))
                      (fun (_ : positive) a => a)
                      (snd (getMaxPerm m2))
                      fun_leq ).
      unfold sub_map.
      eapply HHH; eauto; try constructor.
      clear HHH.
      
      intros; simpl. intros p HH.        
      pose proof (PTree.elements_complete virtue1).
      remember (PTree.elements virtue1) as Velmts.
      clear HeqVelmts.
      induction Velmts as [|[b0 fb]]; try solve[inversion HH].
      simpl in HH.
      destruct (mu b0) as [[b1 delt]|] eqn:Hinj.
    - unfold merge_func in HH.

      destruct (PMap.elt_eq p0 b1); subst.
      destruct (fb (p-delt)%Z) eqn:Hfbp.
      + specialize (H0 b0 fb ltac:(left; auto)).
        clear HH.
        cbv beta zeta iota delta[fst] in A.
        pose proof (strong_tree_leq_spec
                      fun_leq
                      ltac:(simpl; auto)
                             virtue1 (snd (getMaxPerm m1)) A b0).
        rewrite H0 in H1.
        unfold fun_leq in H1.
        destruct ((snd (getMaxPerm m1)) ! b0) eqn:Heqn;
          try solve[inversion H1].
        specialize (H1 (p - delt)%Z ltac:(rewrite Hfbp; auto)).
        eapply injmem in Hinj.

        2: {
          
          clear IHVelmts Velmts Hinj.
          clear Hfbp A a b1 H.

          instantiate (2:= Max).
          instantiate (2:= (p - delt)%Z).
          instantiate (1:= Nonempty).
          unfold Mem.perm.
          pose proof restrPermMap_Max as H3.
          unfold permission_at in H3.
          rewrite H3; clear H3.
          unfold PMap.get.
          rewrite Heqn.
          
          destruct (o (p - delt)%Z); try solve[inversion H1].
          destruct p; try constructor.
        }

        
        unfold Mem.perm in Hinj.
        pose proof restrPermMap_Max as H2.
        unfold permission_at in H2.
        rewrite H2 in Hinj.
        unfold PMap.get in Hinj.
        rewrite H in Hinj.
        replace (p - delt + delt)%Z with p in Hinj by omega.
        destruct (a p); inversion Hinj; auto.

      + eapply IHVelmts in HH; auto.
        intros; eapply H0; right.
        auto.

      + eapply IHVelmts in HH; auto.
        intros; eapply H0.
        right; auto.

    - (* mu b0 = None *)
      eapply IHVelmts in HH; auto.
      intros; eapply H0.
      right; auto.
  Qed.


  
  Definition inject_virtue (m: mem) (mu: meminj) (angel:virtue):=
    Build_virtue
      (virtueThread_inject m mu (virtueThread angel))
      (virtueLP_inject m mu (virtueLP angel)).

  
      Lemma inject_is_empty_map:
        forall  m mu empty_perms
                (Hempty_map : is_empty_map empty_perms),
          is_empty_map (inject_access_map m mu empty_perms).
      Proof.
        intros ** b ofs.
        unfold inject_access_map,
        tree_map_inject_over_mem,
        tree_map_inject_over_tree.
        unfold PMap.get; simpl.
        rewrite PTree.gmap, PTree.gmap1.
        destruct ((snd (Mem.mem_access m)) ! b); simpl; auto.
        - 
          unfold build_function_for_a_block,merge_func.
          remember (PTree.elements (snd empty_perms)) as elemts eqn:HH.
          assert (forall b1 f, In (b1, f) elemts -> forall ofs, f ofs = None).
          { intros * Hin ofs0. subst; eapply PTree.elements_complete in Hin.
            specialize (Hempty_map b1 ofs0).
            unfold PMap.get in *; match_case in Hempty_map.  }
          clear Hempty_map HH. revert H.
          induction elemts.
          + simpl; auto.
          + simpl.
            intros.
            repeat match_case; subst; auto.
            * specialize (H p o0 ltac:(auto) ).
              rewrite H in Heqo0; try congruence.
            * eapply IHelemts. intros. eapply H; eauto.
            * eapply IHelemts. intros. eapply H; eauto.
            * eapply IHelemts. intros. eapply H; eauto.
      Qed.
      
      Lemma inject_empty_maps:
        forall  m mu empty_perms
           (Hempty_map : empty_doublemap empty_perms),
          empty_doublemap (virtueLP_inject m mu empty_perms).
      Proof. intros ??. solve_pair.
             eapply inject_is_empty_map.
      Qed.

      
      Lemma no_overla_dmap_mem:
        forall mu m dmap,
          (forall (b : positive) (ofs : Z),
              option_implication
                (dmap_get dmap b ofs)
                ((getMaxPerm m) !! b ofs)) ->
          Mem.meminj_no_overlap mu m ->
          dmap_no_overlap mu dmap.
      Proof.
        intros ** ? **.
        eapply H0; eauto.
        + specialize (H b1 ofs1).
          unfold Mem.perm; rewrite_getPerm.
          unfold option_implication in *.
          repeat match_case in H.
          constructor.
          unfold dmap_get in *.
          rewrite Heqo in H4.
          inversion H4.
        + specialize (H b2 ofs2).
          unfold Mem.perm; rewrite_getPerm.
          unfold option_implication in *.
          repeat match_case in H.
          constructor.
          unfold dmap_get in *.
          rewrite Heqo in H5.
          inv H5.
      Qed.

      
      Inductive injects (mu:meminj) (b:block): Prop:=
      | InjectsBlock: forall b2 delta, mu b = Some (b2, delta) -> injects mu b.
      Definition injects_map mu (m:access_map): Prop := forall b ofs p,
          m !! b ofs = Some p -> injects mu b.
      Definition injects_map_pair mu:= pair1_prop (injects_map mu).
      Hint Unfold injects_map_pair: pair.
      Definition injects_dmap mu (m:delta_map) := forall b ofs p,
          dmap_get m b ofs = Some p -> injects mu b.
      Definition injects_dmap_pair mu:= pair1_prop (injects_dmap mu).
      Hint Unfold injects_dmap_pair: pair.
      Lemma inject_virtue_sub_map_pair:
        forall (m1 m2 : mem)
          (mu : meminj)
          (angel : virtue)
          perm1 perm2 Hlt1 Hlt2,
          Mem.inject mu (@restrPermMap perm1 m1 Hlt1 ) 
                     (@restrPermMap perm2 m2 Hlt2 ) ->
          sub_map_pair (virtueThread angel) (snd (getMaxPerm m1)) ->
          sub_map_pair (virtueThread (inject_virtue m2 mu angel)) (snd (getMaxPerm m2)).
      Proof.
        intros.
        remember (snd (getMaxPerm m2)) as TEMP.
        destruct angel as (virtueT&?); destruct virtueT as (virtueT_A & virtueT_B).
        simpl; subst.
        constructor; eapply inject_virtue_sub_map; first [eapply H0|eassumption].
      Qed.

      
      Lemma inject_perm_inj_dmap':
        forall mu m1 m2 dmap
               (Hinj_dmap: injects_dmap mu dmap)
               (Himpl:
                  forall b1 b2 delta ofs o,
                    mu b1 = Some (b2, delta) ->
                    dmap_get dmap b1 ofs = Some o ->
                    option_implication dmap ! b1 (snd (getMaxPerm m2)) ! b2)
               (Hmi_inj:Mem.mem_inj mu m1 m2)
               (Hnon_over: dmap_no_overlap mu dmap),
          perm_inj_dmap
            mu dmap (tree_map_inject_over_mem m2 mu dmap).
      Proof.
        intros ** b1 ** .
        destruct (dmap_get dmap b1 ofs) eqn:Hdmap; try solve[inv H].
        specialize (Hinj_dmap _ _ _ Hdmap).
        inv Hinj_dmap. normal; eauto.
        erewrite tree_map_inject_over_mem_correct_forward; eauto.
      Qed.

      
      Lemma inject_perm_inj':
        forall mu m1 m2 perm
          (Hcanon: isCanonical perm)
          (Hinj_dmap: injects_map mu perm)
          (Himpl:
             forall b1 b2 delta ofs o,
               mu b1 = Some (b2, delta) ->
               perm !! b1 ofs = Some o ->
               option_implication (snd perm) ! b1 (snd (getMaxPerm m2)) ! b2)
          (Hmi_inj:Mem.mem_inj mu m1 m2)
          (Hnon_over: no_overlap mu perm),
          perm_inj
            mu perm (inject_access_map m2 mu perm).
      Proof.
        unfold inject_access_map; intros ** b1 **. 
        destruct (perm !! b1 ofs) eqn:Hdmap; try solve[inv H].
        specialize (Hinj_dmap _ _ _ Hdmap).
        inv Hinj_dmap. normal; eauto.
        
        exploit Himpl; eauto; intros HH.
        unfold option_implication in *.
        unfold PMap.get in *; simpl.
        repeat match_case in Hdmap.
        2:{ rewrite Hcanon in Hdmap; congruence. }
        exploit tree_map_inject_over_mem_correct_forward_perm; eauto.
        - unfold PMap.get; rewrite Heqo; auto.
        - match_case in HH. unfold option_implication; match_case.
      Qed.
      
      Lemma inject_perm_inj_dmap:
        forall mu m1 m2 dmap
          (Hinj_dmap: injects_dmap mu dmap)
          (Himpl: forall b ofs,
              option_implication
                (dmap_get dmap b ofs)
                ((getMaxPerm m1) !! b ofs))
          (Hmi_inj:Mem.inject mu m1 m2),
          perm_inj_dmap
            mu dmap (tree_map_inject_over_mem m2 mu dmap).
      Proof.
        intros.
        eapply inject_perm_inj_dmap'; intros; eauto.
        - eapply option_implication_injection_dmap; eauto.
          eapply Hmi_inj.
        - eapply Hmi_inj.
        - eapply no_overla_dmap_mem; auto.
          eapply Hmi_inj.
      Qed.

      
Lemma inject_perm_inj:
  forall mu m1 m2 perm
    (Hinj_dmap: injects_map mu perm)
    (Himpl: forall b ofs,
        option_implication
          (perm !! b ofs)
          ((getMaxPerm m1) !! b ofs))
    (Hmi_inj:Mem.inject mu m1 m2),
    perm_inj
      mu perm (inject_access_map m2 mu perm).
Proof.
  intros.
  eapply inject_perm_inj'; intros; eauto.
  - eapply option_impl_isCanon; eauto.
  - eapply option_implication_injection; eauto.
    + unfold isCanonical'. extensionality ofs0.
      eapply option_implication_fst in Himpl.
      instantiate(1:=ofs0) in Himpl.
      rewrite Max_isCanonical in Himpl.
      unfold option_implication in *.
      match_case in Himpl.
    + eapply Hmi_inj.
  - eapply Hmi_inj.
  - eapply no_overla_perm_mem; auto.
    eapply Hmi_inj.
Qed.


Lemma inject_dmap_preimage:
  forall mu m2 dmap,
    dmap_preimage
      mu dmap (tree_map_inject_over_mem m2 mu dmap).
Proof.
  unfold dmap_preimage; intros.
  unfold at_least_Some, option_implication in *.
  match_case in H.
  apply dmap_inject_correct_backwards in Heqo.
  normal; eauto.
Qed.
Lemma inject_preimage:
  forall mu m2 perm,
    perm_surj
      mu perm (inject_access_map m2 mu perm).
Proof.
  unfold perm_surj; intros.
  unfold at_least_Some, option_implication in *.
  match_case in H.
  eapply inject_access_map_correct_backwards in Heqo.
  normal; eauto.
Qed.


Lemma inject_perm_perfect_image_dmap:
  forall mu m1 m2 dmap
    (Hmi_inj:Mem.inject mu m1 m2)
    (Himpl: option_implication_dmap_access
              dmap (getMaxPerm m1))
    (Hinj_dmap: injects_dmap mu dmap),
    perm_perfect_image_dmap
      mu dmap (tree_map_inject_over_mem m2 mu dmap).
Proof.
  intros; constructor.
  - eapply inject_perm_inj_dmap; auto.
  - eapply inject_dmap_preimage.
Qed.


Lemma inject_perm_perfect_image:
  forall mu m1 m2 (m : access_map),
    Mem.inject mu m1 m2 ->
    injects_map mu m ->
    perm_perfect_image mu m (inject_access_map m2 mu m).
Proof.
  intros; constructor.
  - eapply inject_perm_inj; auto.
Admitted.



Lemma inject_virtue_perm_perfect_image_dmap:
  forall mu m1 m2 angel ,
    Mem.inject mu m1 m2 ->
    (option_implication_dmap_access_pair
       (virtueThread angel) (getMaxPerm m1)) ->
    injects_dmap_pair mu (virtueThread angel) ->
    perm_perfect_image_dmap_pair mu
                                 (virtueThread angel)
                                 (virtueThread (inject_virtue m2 mu angel)).
Proof.
  intros *. 
  replace (virtueThread (inject_virtue m2 mu angel)) with
      (virtueThread_inject m2 mu (virtueThread angel)) by reflexivity.
  remember (virtueThread angel) as virt. clear - virt; revert virt.
  solve_pair.
  eapply inject_perm_perfect_image_dmap.
Qed.


Lemma full_inject_dmap:
  forall f m dm,
    Events.injection_full f m ->
    dmap_valid m dm ->
    injects_dmap f dm.
Proof.
  intros ** ? **.
  eapply H0 in H1.
  eapply H in H1.
  destruct (f b) as [[? ?]|] eqn:HHH; try contradiction.
  econstructor; eauto.
Qed.


Lemma full_inject_dmap_pair:
  forall f m dm,
    Events.injection_full f m ->
    dmap_valid_pair m dm ->
    injects_dmap_pair f dm.
Proof. intros ??; solve_pair; eapply full_inject_dmap. Qed.


Lemma inject_virtue_perm_perfect_image:
  forall mu m1 m2 angel,
    Mem.inject mu m1 m2 ->
    injects_map_pair mu (virtueLP angel) ->
    perm_perfect_image_pair mu (virtueLP angel)
                            (virtueLP (inject_virtue m2 mu angel)).
Proof.
  intros mu m1 m2 angel.
  unfold inject_virtue; simpl.
  remember (virtueLP angel) as VLP; generalize VLP.
  solve_pair.

  pose proof inject_virtue_perm_perfect_image_dmap; eauto.

Admitted.



Record injects_angel mu angel:=
  { Hinj_map : injects_map_pair mu (virtueLP angel);
    Hinj_dmap : injects_dmap_pair mu (virtueThread angel)}.

Lemma inject_virtue_perm_perfect:
  forall f angel1 m1 m2,
    Mem.inject f m1 m2 ->
    injects_angel f angel1 ->
    option_implication_dmap_access_pair (virtueThread angel1) (getMaxPerm m1) ->
    perm_perfect_virtue f angel1 (inject_virtue m2 f angel1).
Proof.
  intros ? ? ? ? Hinj [? ?]; econstructor.
  - eapply inject_virtue_perm_perfect_image; eauto.
  - eapply inject_virtue_perm_perfect_image_dmap; eauto.
Qed.


Lemma full_inject_map:
  forall f m dm,
    Events.injection_full f m ->
    map_valid m dm ->
    injects_map f dm.
Proof.
  intros ** ? **.
  eapply H0 in H1.
  eapply H in H1.
  destruct (f b) as [[? ?]| ] eqn:HHH; try contradiction.
  econstructor; eauto.
Qed.
Lemma full_inject_map_pair:
  forall f m dm,
    Events.injection_full f m ->
    map_valid_pair m dm ->
    injects_map_pair f dm.
Proof.
  intros ??; solve_pair. eapply full_inject_map.
Qed.


Lemma full_injects_angel:
  forall mu m1 angel,
    Events.injection_full mu m1 -> 
    sub_map_virtue angel (getMaxPerm m1) ->
    injects_angel mu angel.
Proof.
  intros * Hfull Hsub_map.
  constructor.
  - eapply full_inject_map_pair; try eassumption.
    eapply sub_map_valid_pair, Hsub_map.
  - eapply full_inject_dmap_pair; try eassumption.
    apply join_dmap_valid_pair, Hsub_map.
Qed.


Lemma deltaMapLt2_inject:
  forall p1 p2 m1 m2 Hlt1 Hlt2 mu virtue,
    Mem.inject mu (@restrPermMap p1 m1 Hlt1) (@restrPermMap p2 m2 Hlt2) ->
    deltaMapLt2 virtue (getMaxPerm m1) ->
    deltaMapLt2 (tree_map_inject_over_mem m2 mu virtue) (getMaxPerm m2).
Proof.
Admitted.
Lemma deltaMapLt2_inject_pair:
  forall p1 p2 m1 m2 Hlt1 Hlt2 mu virtue,
    Mem.inject mu (@restrPermMap p1 m1 Hlt1) (@restrPermMap p2 m2 Hlt2) ->
    deltaMapLt2_pair1 virtue (getMaxPerm m1) ->
    deltaMapLt2_pair1 (virtueThread_inject m2 mu virtue) (getMaxPerm m2).
Proof.
  intros until mu. unfold virtueThread_inject.
  destruct virtue.
  solve_pair.
  split; eapply deltaMapLt2_inject.
Qed.


Lemma permMapLt_compute_inject_pair:
  forall mu p1 p2 m1 m2 Hlt1 Hlt2,
    Mem.inject mu (@restrPermMap p1 m1 Hlt1) (@restrPermMap p2 m2 Hlt2) ->
    forall a1 a2 b1 b2,
      permMapLt_pair (computeMap_pair a1 b1) (getMaxPerm m1) ->
      permMapLt_pair a2 (getMaxPerm m2) ->
      b2 = virtueThread_inject m2 mu b1 ->
      permMapLt_pair (computeMap_pair a2 b2) (getMaxPerm m2).
Proof.
  intros **.
  eapply permMapLt_computeMap_pair; eauto.
  subst b2; eapply deltaMapLt2_inject_pair;
    try eassumption.
  eapply permMapLt_computeMap_pair'.
  eassumption.
Qed.

End VirtueInject.
Hint Unfold injects_map_pair: pair.

