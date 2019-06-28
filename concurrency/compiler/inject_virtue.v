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
Require Import VST.concurrency.common.semantics. 
Require Import VST.concurrency.common.HybridMachine.
Require Import VST.concurrency.compiler.mem_equiv.
Require Import VST.concurrency.compiler.pair.
Require Import VST.concurrency.memsem_lemmas.


Section VirtueInject.
  (* Move to  permissions? *)
  Lemma at_least_Some_trivial:
    forall {A} x y, x = Some y -> @at_least_Some A x.
  Proof. intros; subst; constructor. Qed.
  
  Definition merge_func {A} (f1 f2:Z -> option A):
    (BinNums.Z -> option A):=
    fun ofs => if f1 ofs then f1 ofs else f2 ofs.

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

  Inductive opt_rel {A}  (r: relation A): relation (option A):=
  | SomeOrder:forall a b, r a b -> opt_rel r (Some a) (Some b)
  | NoneOrder: forall p, opt_rel r p None.
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

End VirtueInject.