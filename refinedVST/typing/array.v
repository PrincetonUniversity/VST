From iris.algebra Require Import list.
From VST.typing Require Export type.
(* From VST.typing Require Import programs singleton bytes int own.
From VST.typing Require Import type_options. *)
From VST.floyd Require Import aggregate_pred.
Import aggregate_pred.
From VST.floyd Require Export field_at.
Section array.

  Context `{!typeG OK_ty Σ} {cs : compspecs}.

  Lemma array_pred_shift_addr: forall {A}{d: Inhabitant A} (lo hi lo' hi' mv : Z) (P: Z -> A -> val -> mpred) (v: list A) (p p':address) (cty:Ctypes.type),
    lo - lo' = mv ->
    hi - hi' = mv ->
    p' = (p.1, p.2 + mv * expr.sizeof cty) ->
    (forall i i', lo <= i < hi -> i - i' = mv -> P i' (Znth (i' - lo') v) p' = P i (Znth (i - lo) v) p) ->
    array_pred lo' hi' P v p' = array_pred lo hi P v p.
  Proof.
    intros.
    unfold array_pred, floyd.aggregate_pred.array_pred.
    f_equal; first by f_equal; apply prop_ext; lia.
    replace (hi' - lo') with (hi - lo) by lia.
    destruct (zlt hi lo).
    - rewrite -> Z2Nat_neg by lia. reflexivity.
    - apply rangespec_shift; intros.
      rewrite (H2 i' i); try lia. done.
  Qed.

  Ltac unfold_mapsto := 
    rewrite /heap_mapsto_own_state_type /heap_mapsto_own_state /mapsto.

  Lemma value_fits_array_app s1 s2 s3 cty v1 v2 v:
    0 <= s1 ->
    0 <= s2 ->
    s3 = s1 + s2 ->
    v = v1 ++ v2 ->
    value_fits (tarray cty $ s1) v1 ->
    value_fits (tarray cty $ s2) v2 ->
    value_fits (tarray cty $ s3) v.
  Proof.
    intros ?? -> -> [hd1 hd2] [ts1 ts2].
    split.
    - rewrite /unfold_reptype /= in hd1 ts1.
      rewrite /unfold_reptype Zlength_app hd1 ts1 /=.
      rewrite -!Z2Nat_id' /=.
      lia.
    - rewrite Forall_app.
      split; done.
  Qed.

  Lemma array_split l l_1 (s s1 s2:Z) cty v v_hd v_tl :
    v = v_hd ++ v_tl ->
    1 <= s1 ->
    s1 = Zlength v_hd ->
    s2 = Zlength v_tl ->
    s = s1 + s2 ->
    l_1 = (l.1, l.2 + s1 * @expr.sizeof cs cty) ->
    l ↦|tarray cty s| v ⊣⊢
    l ↦|tarray cty s1| v_hd ∗
    l_1 ↦|tarray cty s2| v_tl.
  Proof.
    intros Hv ? Hs1 Hs2 Hs Hl.
    apply (pure_equiv _  _ (value_fits (tarray cty s) (v_hd++v_tl))).
    { rewrite Hv.
      apply data_at_rec_value_fits. }
    { iDestruct 1 as "(↦hd & ↦tl)".
      iPoseProof (data_at_rec_value_fits with "↦hd") as "%v_fits1".
      iPoseProof (data_at_rec_value_fits with "↦tl") as "%v_fits2".
      iPureIntro.
      eapply value_fits_array_app; [..|apply v_fits1|apply v_fits2].
      all: try done; try rep_lia.
    }
    intros [v_fits _].
    rewrite /mapsto data_at_rec_eq /=.
    rewrite (split_array_pred _ s1); try rep_lia.
    2: { rewrite Hv v_fits; lia. }
    
    rewrite data_at_rec_eq /unfold_reptype /=.
    assert (sublist 0 s1 v = v_hd) as Hsub1.
    { rewrite Hv Hs1 sublist0_app1; last rep_lia.
      rewrite sublist_same //.
    }
    assert (sublist s1 s v = v_tl) as Hsub2.
    { rewrite Hv sublist_app2; last rep_lia.
      rewrite Hs1 sublist_same //; rep_lia.
    }
    rewrite !Z.sub_0_r !Z.max_r; [|rep_lia..].
    rewrite Hsub1 Hsub2.
    f_equiv.
    rewrite [in X in _ ⊣⊢ X ]/data_at_rec /unfold_reptype /= .
    apply seplog_tactics.eq_equiv.
    rewrite !Z.max_r; [|rep_lia..].
    erewrite (array_pred_shift_addr s1 s 0 s2 s1 ); try lia; try done.
    intros i i' _ Hi.
    assert (i'=i-s1) as -> by lia.
    rewrite !mapsto_memory_block.at_offset_eq Hl.
    f_equal.
    - f_equal. lia.
    - rewrite /offset_val /= !ptrofs_add_repr.
      do 2 f_equal. lia.
  Qed.

  Lemma mapsto_layout_array_split l l_1 (s s1 s2:Z) cty :
    1 <= s1 ->
    0 <= s2 ->
    s = s1 + s2 ->
    l_1 = (l.1, l.2 + s1 * @expr.sizeof cs cty) ->
    l ↦[Own]|tarray cty s| ⊣⊢
    l ↦[Own]|tarray cty s1| ∗
    l_1 ↦[Own]|tarray cty s2|.
  Proof.
    intros ?? -> Hl.
    iSplit.
    - iDestruct 1 as (v) "↦".
      iPoseProof (data_at_rec_value_fits with "↦") as "%v_fits".
      destruct v_fits as [v_fits _].
      rewrite /unfold_reptype Z.max_r /= in v_fits; [|rep_lia].
      rewrite /heap_mapsto_own_state.
      rewrite (array_split _ _ _ _ _ _ _ (sublist 0 s1 v) (sublist s1 (s1+s2) v)) //.
      2: { rewrite sublist_rejoin; try rep_lia.
           - rewrite sublist_same //.
           - rewrite v_fits; rep_lia. }
      2: { rewrite Zlength_sublist; try rep_lia. rewrite v_fits; rep_lia. }
      2: { rewrite Zlength_sublist; try rep_lia. rewrite v_fits; rep_lia. }
      iDestruct "↦" as "[↦hd ↦tl]".
      rewrite Zlength_sublist; try rep_lia. 2: rewrite v_fits; rep_lia.
      assert (s1 + s2 - s1 = s2) as -> by lia.
      iSplitL "↦hd"; iExists _; done.
    - iDestruct 1 as "[[%v1 ↦hd] [%v2 ↦tl]]".
      iPoseProof (data_at_rec_value_fits with "↦hd") as "%v_fits1".
      iPoseProof (data_at_rec_value_fits with "↦tl") as "%v_fits2".
      destruct v_fits1 as [v_fits1 _].
      destruct v_fits2 as [v_fits2 _].
      rewrite /unfold_reptype !Z.max_r /= in v_fits1 v_fits2; [|rep_lia..].
      iExists (v1 ++ v2).
      rewrite /heap_mapsto_own_state (array_split _ _ _ _ _ _ (v1++v2) v1 v2); try done; try rep_lia.
      iFrame.
    Qed.

  (* maybe using field_compatible_cons_Tarray/field_compatible_shrink makes proof simpler? *)
  Lemma has_layout_loc_array_tl l l_1 cty (s:nat) :
    l_1 = (l.1, l.2 + @expr.sizeof cs cty)%Z →
    l `has_layout_loc` tarray cty (S s) →
    l_1 `has_layout_loc` tarray cty s.
  Proof.
    intros Hl_1 l_has_layout_loc.
    pose proof (sizeof_pos cty) as Hcty_size_pos.
    
    rewrite /has_layout_loc /field_compatible in l_has_layout_loc.
    destruct l_has_layout_loc as (? & ? & ? & ? & ?).
    rewrite /has_layout_loc /field_compatible Hl_1.
    destruct (adr2val l) eqn:?; try done.
    simpl in H1. rewrite /adr2val in Heqv. inv Heqv.
    split3; try done.
    split3; try done.
    - rewrite /= Z.max_r; [|lia].
      rewrite -ptrofs_add_repr /expr.sizeof.
      destruct (Ptrofs.unsigned_add_either (Ptrofs.repr l.2) 
                                            (Ptrofs.repr (sizeof cty))) as [-> | ->].
      + rewrite [Ptrofs.unsigned (Ptrofs.repr (sizeof cty))]Ptrofs.unsigned_repr; rep_lia.
      + rep_lia.
    - rewrite /SeparationLogic.align_compatible /=.
      rewrite -ptrofs_add_repr /expr.sizeof.
      rewrite /SeparationLogic.align_compatible /= in H2.
      pose proof (align_mem.align_compatible_rec_Tarray_inv _ _ _ _ _ H2).
      rewrite Ptrofs.unsigned_add_carry.
      rewrite /Ptrofs.add_carry.
      if_tac.
      + rewrite Ptrofs.unsigned_zero /= Z.mul_0_l Z.sub_0_r.
        rewrite [Ptrofs.unsigned (Ptrofs.repr (sizeof cty))]Ptrofs.unsigned_repr; last rep_lia.
        constructor. intros. rewrite -Z.add_assoc Zred_factor2. apply H4. lia.
      + rewrite [Ptrofs.unsigned (Ptrofs.repr (sizeof cty))]Ptrofs.unsigned_repr in H5; last rep_lia.
        rewrite Ptrofs.unsigned_zero Z.add_0_r in H5.
        assert ( Ptrofs.unsigned (Ptrofs.repr l.2) + sizeof cty < Ptrofs.modulus) by rep_lia.
        contradiction.
  Qed.

  Lemma has_layout_loc_array_hd l cty s :
    1 <= s →
    l `has_layout_loc` tarray cty s →
    l `has_layout_loc` cty.
  Proof.
    intros Hs l_has_layout_loc.
    pose proof (sizeof_pos cty) as Hcty_size_pos.
    
    rewrite /has_layout_loc /field_compatible in l_has_layout_loc.
    destruct l_has_layout_loc as (? & ? & ? & ? & ?).
    rewrite /has_layout_loc /field_compatible.
    destruct (adr2val l) eqn:?; try done.
    rewrite /= Z.max_r in H1; try lia. rewrite /adr2val in Heqv. inv Heqv.
    split3; try done.
    split3; try done.
    - rewrite /= /expr.sizeof.
      assert (Ptrofs.unsigned (Ptrofs.repr l.2) + sizeof cty <=
              Ptrofs.unsigned (Ptrofs.repr l.2) + sizeof cty * s); try rep_lia.
      apply Zplus_le_compat_l.
      destruct (decide (sizeof cty = 0)); try rep_lia.
      apply Z.le_mul_diag_r; lia.
    - rewrite /SeparationLogic.align_compatible /=.
      rewrite /SeparationLogic.align_compatible /= in H2.
      pose proof (align_mem.align_compatible_rec_Tarray_inv _ _ _ _ _ H2 0).      
      rewrite Z.mul_0_r Z.add_0_r in H4. apply H4. lia.
  Qed.

  Lemma singleton_array_eq l cty v:
    l ↦|tarray cty 1|[v] ⊣⊢ l↦|cty| v.
  Proof. 
    rewrite /mapsto /nested_field_offset /=.
    rewrite /data_at_rec /unfold_reptype /array_pred /floyd.aggregate_pred.array_pred /Znth /Zlength
            /mapsto_memory_block.at_offset /= bi.sep_emp.
    iSplit.
      - iDestruct 1 as "[_ ↦]".
        iStopProof.
        f_equiv.
        rewrite /adr2val /=.
        f_equiv.
        rewrite Z.mul_0_r ptrofs_add_repr_0_r //.
      - iIntros "?".
        iSplit; [done|].
        iStopProof.
        f_equiv.
        rewrite /adr2val /=.
        f_equiv.
        rewrite Z.mul_0_r ptrofs_add_repr_0_r //.
  Qed.

  Lemma mapsto_jmeq (cty1 cty2:Ctypes.type) v1 v2 l :
      cty1 = cty2 ->
      JMeq.JMeq v1 v2 ->
      l ↦|cty1|v1 ⊢ l ↦|cty2|v2.
  Proof.
    intros -> ->. done.
  Qed.

  (* maybe something like array_pred? *)
  Program Definition array (cty:Ctypes.type) (tys : list type) : type := {|
    ty_has_op_type cty_arr mt := (cty_arr = tarray cty (length tys) ∧ Forall (λ ty, ty.(ty_has_op_type) cty MCNone) tys)%type;
    ty_own β l := (
      <affine> ⌜l `has_layout_loc` (tarray cty (length tys))⌝ ∗
      ([∗ list] i ↦ ty ∈ tys,
        (l.1, l.2 + nested_field_offset (tarray cty (length tys)) [ArraySubsc i]) ◁ₗ{β} ty)
      )%I
    ;
    ty_own_val cty_arr v_rep :=
      (
        ∃ v_rep', <affine> ⌜JMeq.JMeq v_rep v_rep'⌝ ∗
        <affine> ⌜v_rep `has_layout_val` cty_arr⌝ ∗
        [∗ list] v';ty ∈ v_rep';tys, (v' ◁ᵥ|cty| ty))%I;
  |}.
  Next Obligation.
    iIntros (cty tys l E He) "($&Ha)".
    iApply big_sepL_fupd. iApply (big_sepL_impl with "Ha").
    iIntros "!#" (???) "a".
    by iApply ty_share.
   
  Qed.
  Next Obligation. by iIntros (cty tys cty_arr mt v [-> ?]) "(? & _)". Qed.
  Next Obligation. by iIntros (cty tys cty_arr mt v [-> ?]) "(% & -> & ? & _)". Qed.
  Next Obligation.
    move => cty tys cty_arr mt l [-> Hop_type]. iIntros "[%l_has_layout_loc H]".
    iInduction (tys) as [|ty tys] "IH" forall (Hop_type l l_has_layout_loc); csimpl.
    { iExists []. iSplitR => //. iExists _. iSplitR => //. iSplitR => //. }
    iDestruct "H" as "(tys_hd & tys_tl)".
    pose l_1:address := (l.1, l.2 + @expr.sizeof cs cty)%Z.
    rewrite Forall_cons in Hop_type. destruct Hop_type as [Hop_type_hd Hop_type_tl].
    iSpecialize ("IH" with "[]"); [done|].
    iDestruct ("IH" $! l_1 with "[] [tys_tl]") as "(%v_rep & ↦tl & % & % & % & tys_tl)"; iClear "IH".
    {
      clear -l_has_layout_loc.
      
      rewrite /= in l_has_layout_loc.
      apply (has_layout_loc_array_tl _ l_1) in l_has_layout_loc; done.
    }
    {
      iFrame.
      iApply (big_sepL_impl with "tys_tl").
      iIntros "!>" (i ty_i Hty_i) "?".
      rewrite /nested_field_offset /=.
      iStopProof. do 2 f_equiv. lia.
    }

    iDestruct (ty_deref with "tys_hd") as (v_hd) "[↦hd Hty]".
    { done. }
    iExists (v_hd::v_rep).
    iPoseProof (data_at_rec_value_fits with "↦tl") as "%v_tl_fits".
    destruct v_tl_fits as [v_tl_fits _]; rewrite /unfold_reptype Z.max_r /= in v_tl_fits; [|lia].
    iAssert (l ↦|tarray cty (S (length tys))|([v_hd] ++ v_rep)) with "[↦hd ↦tl]" as "↦".
    {
      rewrite (array_split l l_1 _ 1 (length tys) _ _ [v_hd] v_rep); try done; try rep_lia.
      - iFrame.
        rewrite singleton_array_eq.
        iStopProof.
        rewrite /mapsto /nested_field_offset /=. f_equiv.
        rewrite /adr2val /=.
        f_equiv.
        rewrite Z.mul_0_r Z.add_0_l Z.add_0_r //.
      - rewrite Z.mul_1_l //.
    }
    iPoseProof (data_at_rec_value_fits with "↦") as "%v_fits".
    rewrite /has_layout_val.
    iFrame.
    iExists _. do 2 iSplit =>//. iFrame. rewrite H. done.
  Qed.

  Next Obligation.
    move => cty tys cty_arr mt l v_rep [Hcty_eq Hop_type].
    revert v_rep. rewrite Hcty_eq => v_rep.
    iIntros (Hl) "↦ [% (<- & %Hv & tys)]".
    rename v_rep into v. clear v_rep'.
    iSplit => //.
    iInduction (tys) as [|ty tys] "IH" forall (cty_arr Hcty_eq l v Hop_type Hv Hl); csimpl in *.
    { rewrite /mapsto /data_at_rec /array_pred / floyd.aggregate_pred.array_pred /=.
      iDestruct (big_sepL2_nil_inv_r with "tys") as "->". done. }
    rewrite Forall_cons in Hop_type.
    destruct Hop_type as [Hop_type_hd Hop_type_tl].
    pose l_1:address := (l.1, l.2 + @expr.sizeof cs cty)%Z.
    apply (has_layout_loc_array_tl _ l_1) in Hl as Hl_tl;[|done].
    destruct v as [|v_hd v_tl]; [done|].
    rewrite /has_layout_val /= in Hv.
    destruct Hv as [Hv _].
    rewrite /unfold_reptype /= Zlength_cons Zpos_P_of_succ_nat /Z.succ Z.add_cancel_r in Hv.
    rewrite (array_split l l_1 _ 1 (length tys) _ _ [v_hd] v_tl); try done; try rep_lia.
    2: { rewrite Z.mul_1_l //. }
    iDestruct "↦" as "[↦hd ↦tl]".
    iDestruct "tys" as "[tys_hd tys_tl]".
    iPoseProof (data_at_rec_value_fits with "↦tl") as "%v_tl_fits".
    iDestruct ("IH" $! _ _ l_1 v_tl with "[//] [//] [//] ↦tl tys_tl") as "ty_own_tl"; iClear "IH".
    Unshelve. 3: done.
    rewrite singleton_array_eq.
    apply has_layout_loc_array_hd in Hl; [|lia].
    iDestruct (ty_ref with "[] ↦hd tys_hd") as "ty_own_hd"; try done.
    iSplitL "ty_own_hd".
    - iStopProof. f_equiv.
      destruct l; simpl; f_equiv.
      rewrite /nested_field_offset /nested_field_rec /=.
      lia.
    - iApply (big_sepL_impl with "ty_own_tl").
      iIntros "!>" (i ty_i Hty_i) "?".
      rewrite /nested_field_offset /=.
      iStopProof. do 2 f_equiv. lia.
  Qed.

  Global Instance array_le : Proper ((=) ==> Forall2 (⊑) ==> (⊑)) array.
  Proof.
    move => ? sl -> tys1 tys2 Htys. constructor.
    - move => β l; rewrite/ty_own/=.
       f_equiv; first by rewrite ->Htys.
      elim: Htys l => // ?????? IH l' /=. f_equiv.
      + f_equiv; done. 
      + rewrite /nested_field_offset /=  in IH.
        rewrite /nested_field_offset /=.
        
        rewrite big_sepL_proper /=.
        2: { intros.
        assert (l'.2 + (0 + expr.sizeof sl * S k) =
                (l'.2 + expr.sizeof sl) + (0 + expr.sizeof sl * k))%Z as -> by lia.
        apply seplog_tactics.eq_equiv. done.
        }

        rewrite [X in _ ⊢ X]big_sepL_proper /=.
        2: { intros.
        assert (l'.2 + (0 + expr.sizeof sl * S k) =
                (l'.2 + expr.sizeof sl) + (0 + expr.sizeof sl * k))%Z as -> by lia.
        apply seplog_tactics.eq_equiv. done.
        }
        simpl.
        apply (IH (l'.1, l'.2 + expr.sizeof sl)).
    - move => cty v; rewrite/ty_own_val/=.
      f_equiv. f_equiv. f_equiv. f_equiv.
      elim: Htys a => // ???? Hty Htys IH v_rep /=.
      destruct v_rep.
      + done.
      + rewrite !big_sepL2_cons. 
        f_equiv.
        ++ solve_proper.
        ++ apply IH.  
  Qed.
  Global Instance array_proper : Proper ((=) ==> Forall2 (≡) ==> (≡)) array.
  Proof. move => ??-> ?? Heq. apply type_le_equiv_list; [by apply array_le|done]. Qed.

  (* Global Instance array_loc_in_bounds ly β tys : LocInBounds (array ly tys) β (ly_size ly * length tys).
  Proof. constructor. iIntros (?) "(?&$&?)". Qed. *)

  Notation "l 'offset{' cty '}ₗ' path" := 
    (l.1, l.2 + nested_field_offset cty path) 
    (at level 50, format "l  'offset{' cty '}ₗ'  path", left associativity).
  
  Notation "l 'arr_ofs{' cty ',' size '}ₗ' n" := 
    (l offset{ (tarray cty size) }ₗ SUB n) 
    (at level 50, format "l  'arr_ofs{' cty ','  size '}ₗ' n", left associativity).

  Lemma offset_sub_S : ∀ (l : address) cty s (n : nat),
         l arr_ofs{cty, s}ₗ S n = l arr_ofs{cty, s}ₗ 1 arr_ofs{cty, s}ₗ n.
  Proof. intros.
    rewrite /nested_field_offset /=.
    f_equal.
    lia.
  Qed.

  (* TODO delete this when programs.v works *)
  Program Definition place (l : address) : type := {|
    ty_own β l' := (<affine> ⌜l = l'⌝)%I;
    ty_has_op_type _ _ := False%type;
    ty_own_val _ _ := emp;
  |}.
  Solve Obligations with try done.
  Next Obligation. by iIntros (????) "$". Qed.

  (* array has type `tarray cty (length tys)` *)
  Lemma array_get_type (i : nat) cty tys ty l β:
    tys !! i = Some ty →
    l ◁ₗ{β} array cty tys -∗
      (l arr_ofs{cty, length tys}ₗ i) ◁ₗ{β} ty ∗
       l ◁ₗ{β} array cty (<[ i := place (l arr_ofs{cty, length tys}ₗ i)]>tys).
  Proof.
    rewrite !/(ty_own (array _ _)) /= !length_insert.
    iIntros (Hi) "($&Ha)".
    iInduction (i) as [|i] "IH" forall (l tys Hi);
    destruct tys as [|ty' tys] => //; simpl in *; simplify_eq;
    iDestruct "Ha" as "[$ Ha]".
    { rewrite /place /=; iFrame. rewrite /ty_own //. }
    rewrite !offset_sub_S. setoid_rewrite offset_sub_S.
    iDestruct ("IH" with "[//] Ha") as "[Hb2 $]" => //.
  Qed.

  Lemma array_put_type (i : nat) cty tys ty l β:
    (l arr_ofs{cty, length tys}ₗ i) ◁ₗ{β} ty -∗ l ◁ₗ{β} array cty tys -∗ 
      l ◁ₗ{β} array cty (<[ i := ty ]>tys) ∗
    (* NOTE refinedc simply throws away the following term, but VST is linear and have to keep this *)
      ∃ ty', <affine> ⌜(i < length tys)%nat -> Some ty' = tys !! i⌝ ∗ (l arr_ofs{cty, length tys}ₗ i) ◁ₗ{β} ty'.
  Proof.
    intros.
    rewrite !/(ty_own (array _ _))/= !length_insert. iIntros "Hl ($&Ha)".
    destruct (decide (i < length tys)%nat) as [Hlt |].
    2:{ rewrite list_insert_ge => //; last by lia. by iFrame. }
    iInduction (i) as [|i] "IH" forall (l tys Hlt);
    destruct tys as [|ty' tys] => //; simpl in *; try lia.
    - iFrame. iDestruct "Ha" as "[? $]". by iFrame.
    - rewrite offset_sub_S.
      setoid_rewrite offset_sub_S.
      iDestruct "Ha" as "[$ Ha]".
      iDestruct ("IH" with "[] [Hl] Ha") as "[Hb2 ?]" => //; iClear "IH".
      { iPureIntro. lia. }
      setoid_rewrite <-Nat.succ_lt_mono.
      iFrame.
  Qed.

  (* Global Instance array_alloc_alive ly tys β P `{!TCExists (λ ty, AllocAlive ty β P) tys} :
    AllocAlive (array ly tys) β P.
  Proof.
    revert select (TCExists _ _).
    rewrite TCExists_Exists Exists_exists => -[x [/(elem_of_list_lookup_1 _ _) [i Hx] ?]].
    constructor. iIntros (l) "HP Hl".
    iDestruct (array_get_type with "Hl") as "[Hl _]"; [done|].
    iDestruct (alloc_alive_alive with "HP Hl") as "Hl".
    by iApply (alloc_alive_loc_mono with "Hl").
  Qed.

  Lemma subsume_array_alloc_alive A l ly tys β T :
    (⌜0 < length tys⌝ ∗ (∀ ty, ⌜tys !! 0%nat = Some ty⌝ -∗ l ◁ₗ{β} ty -∗ alloc_alive_loc l ∗ ∃ x, T x))
    ⊢ subsume (l ◁ₗ{β} array ly tys) (λ x : A, alloc_alive_loc l) T.
  Proof.
    iIntros "[% HT]". destruct tys => //=. iIntros "(%&?&[Hty Htys])".
    rewrite offset_loc_0. iDestruct ("HT" with "[//] Hty") as "[? [% ?]]".
    iExists _. iFrame.
  Qed.
  Definition subsume_array_alloc_alive_inst := [instance subsume_array_alloc_alive].
  Global Existing Instance subsume_array_alloc_alive_inst | 10. *)
  (*** array_ptr *)
  (* Program Definition array_ptr (ly : layout) (base : loc) (idx : Z) (len : nat) : type := {|
    ty_own β l := (
      ⌜l = base offset{ly}ₗ idx⌝ ∗
      ⌜l `has_layout_loc` ly⌝ ∗
      ⌜0 ≤ idx ≤ len⌝ ∗
      loc_in_bounds base (ly_size (mk_array_layout ly len))
    )%I;
    ty_has_op_type _ _ := False%type;
    ty_own_val _ := True%I;
  |}.
  Solve Obligations with try done.
  Next Obligation. iIntros (ly base idx len l E ?) "(%&%&$)". done. Qed.

  Global Instance array_ptr_loc_in_bounds ly base idx β len : LocInBounds (array_ptr ly base idx len) β ((len - Z.to_nat idx) * ly_size ly).
  Proof.
    constructor. iIntros (?) "(->&%&%&Hl)".
    iApply (loc_in_bounds_offset with "Hl") => /=; unfold addr in *; [done|lia|].
    rewrite /mk_array_layout{3}/ly_size/=. nia.
  Qed. *)
  (*** typing rules *)

  (* Lemma array_replicate_uninit_equiv l β ly n:
    layout_wf ly →
    l ◁ₗ{β} array ly (replicate n (uninit ly)) ⊣⊢ l ◁ₗ{β} uninit (mk_array_layout ly n).
  Proof.
    rewrite /ty_own/= => ?. iSplit.
    - iInduction n as [|n] "IH" forall (l) => /=; iIntros "(%&Hlib&Htys)".
      { iExists []. rewrite heap_mapsto_own_state_nil Nat.mul_0_r Forall_nil.
        iFrame "Hlib". iPureIntro. rewrite /has_layout_val/ly_size/=. naive_solver lia. }
      setoid_rewrite offset_loc_S. setoid_rewrite offset_loc_1. rewrite offset_loc_0.
      iDestruct "Htys" as "[Hty Htys]".
      iDestruct (loc_in_bounds_split_mul_S with "Hlib") as "[#Hlib1 Hlib2]".
      iDestruct ("IH" with "[Hlib2 Htys]") as (v2 Hv2 ? _) "Hv2".
      { iFrame. iPureIntro. revert select (layout_wf _). revert select (_ `has_layout_loc` _).
        rewrite /has_layout_loc /layout_wf /aligned_to. case_match => //. destruct l as [? a].
        move => /= [? ->] [? ->]. eexists. by rewrite -Z.mul_add_distr_r. }
      rewrite {2}/ty_own/=. iDestruct "Hty" as (v1 Hv1 Hl1 _) "Hv1".
      iExists (v1 ++ v2). rewrite heap_mapsto_own_state_app Hv1 /has_layout_val length_app Hv1 Hv2.
      iFrame. rewrite Forall_forall. iPureIntro. split_and! => //.
      rewrite {2 3}/ly_size/=. lia.
    - iDestruct 1 as (v Hv Hl _) "Hl". iSplit => //.
      iInduction n as [|n] "IH" forall (v l Hv Hl) => /=.
      { rewrite Nat.mul_0_r right_id.
        iApply loc_in_bounds_shorten; last by iApply heap_mapsto_own_state_loc_in_bounds. lia. }
      setoid_rewrite offset_loc_S. setoid_rewrite offset_loc_1. rewrite offset_loc_0.
      rewrite -(take_drop (ly.(ly_size)) v) heap_mapsto_own_state_app.
      iDestruct "Hl" as "[Hl Hr]". rewrite length_take_le ?Hv; last by repeat unfold ly_size => /=; lia.
      iDestruct (heap_mapsto_own_state_loc_in_bounds with "Hl") as "#Hbl".
      iDestruct (heap_mapsto_own_state_loc_in_bounds with "Hr") as "#Hbr".
      iDestruct ("IH" with "[] [] Hr") as "[Hb HH]".
      { iPureIntro. rewrite /has_layout_val length_drop Hv. repeat unfold ly_size => /=; lia. }
      { iPureIntro. by apply has_layout_loc_ly_mult_offset. }
      iSplitR.
      + iClear "IH". iApply loc_in_bounds_split_mul_S.
        rewrite length_take min_l; last first.
        { rewrite Hv. repeat unfold ly_size => /=; lia. }
        iFrame "Hbl". rewrite length_replicate length_drop Hv.
        destruct ly as [k?]. repeat unfold ly_size => /=.
        have ->: (k * n = k * S n - k)%nat by lia. done.
      + iSplitL "Hl"; last done. iExists _. iFrame. iPureIntro. rewrite Forall_forall. split_and! => //.
        rewrite /has_layout_val length_take_le ?Hv; repeat unfold ly_size => /=; lia.
  Qed. *)

  (* Lemma simplify_hyp_uninit_array ly l β n T:
    ⌜layout_wf ly⌝ ∗ (l ◁ₗ{β} array ly (replicate n (uninit ly)) -∗ T)
    ⊢ simplify_hyp (l ◁ₗ{β} uninit (mk_array_layout ly n)) T.
  Proof. iIntros "[% HT] Hl". iApply "HT". rewrite array_replicate_uninit_equiv // {1}/ly_size/=. Qed.
  Definition simplify_hyp_uninit_array_inst := [instance simplify_hyp_uninit_array with 50%N].
  Global Existing Instance simplify_hyp_uninit_array_inst.

  Lemma simplify_goal_uninit_array ly l β n T:
    ⌜layout_wf ly⌝ ∗ l ◁ₗ{β} array ly (replicate n (uninit ly)) ∗ T
    ⊢ simplify_goal (l ◁ₗ{β} uninit (mk_array_layout ly n)) T.
  Proof. iIntros "[% [? $]]". rewrite array_replicate_uninit_equiv //. Qed.
  Definition simplify_goal_uninit_array_inst := [instance simplify_goal_uninit_array with 50%N].
  Global Existing Instance simplify_goal_uninit_array_inst.

  (* TODO: generalize this rule, maybe similar to [subsume_array_uninit]? *)
  Lemma subsume_uninit_array_replicate A l β n (ly1 : layout) ly2 T:
    (∃ x, ⌜layout_wf ly2⌝ ∗ ⌜ly1 = mk_array_layout ly2 n⌝ ∗ T x)
    ⊢ subsume (l ◁ₗ{β} uninit ly1) (λ x : A, l ◁ₗ{β} array ly2 (replicate n (uninit ly2))) T.
  Proof. iIntros "(%&%&->&?) ?". iExists _. iFrame. by rewrite array_replicate_uninit_equiv. Qed.
  Definition subsume_uninit_array_replicate_inst := [instance subsume_uninit_array_replicate].
  Global Existing Instance subsume_uninit_array_replicate_inst.

  Lemma subsume_array_uninit A l β tys ly1 ly2 T:
    (l ◁ₗ{β} array ly2 tys -∗
      ⌜layout_wf ly2⌝ ∗ l ◁ₗ{β} array ly2 (replicate (length tys) (uninit ly2)) ∗
      ∃ x, ⌜ly1 x = mk_array_layout ly2 (length tys)⌝ ∗ T x)
    ⊢ subsume (l ◁ₗ{β} array ly2 tys) (λ x : A, l ◁ₗ{β} uninit (ly1 x)) T.
  Proof.
    iIntros "Hsub ?". iDestruct ("Hsub" with "[$]") as (?) "[? [% [%Heq ?]]]".
    iExists _. iFrame. by rewrite Heq array_replicate_uninit_equiv.
  Qed.
  Definition subsume_array_uninit_inst := [instance subsume_array_uninit].
  Global Existing Instance subsume_array_uninit_inst. *)
  
  Global Instance mpred_positive : BiPositive mpred.
  Proof.
    constructor. intros.
    ouPred.unseal.
  Admitted.

  
  Lemma subsume_array A cty_arr tys1 tys2 l β T:
    (∀ id,
       subsume (sep_list id type [] tys1 (λ i ty, (l arr_ofs{cty_arr, (length tys1)}ₗ i) ◁ₗ{β} ty))
         (λ x, sep_list id type [] (tys2 x) (λ i ty, (l arr_ofs{cty_arr, (length tys1)}ₗ i) ◁ₗ{β} ty)) T)
    ⊢ subsume (<affine> l ◁ₗ{β} array cty_arr tys1) (λ x : A, <affine> l ◁ₗ{β} array cty_arr (tys2 x)) T.
  Proof.
    unfold sep_list. iIntros "H H1".
    iDestruct ("H" $! {|sep_list_len := length tys1|} with "[H1]") as (?) "[[%Heq ?] ?]".
    { rewrite {1}/ty_own /=. iDestruct "H1" as "[% H1]".
      iSplit; [done|].
      admit. (* probably BiPositive implies pushing affine in to Hl *)
    }
    simpl in *. rewrite -Heq. iExists _. iFrame.
    rewrite /ty_own /=.
    rewrite -bi_positive.
  Admitted.

  (* TODO uncomment this when programs.v is done *)
  (* Definition subsume_array_inst := [instance subsume_array].
  Global Existing Instance subsume_array_inst. *)

  Lemma type_place_array l β ly1 it v tyv tys ly2 K T:
    (v ◁ᵥ tyv -∗ ∃ i, ⌜ly1 = ly2⌝ ∗ v ◁ᵥ i @ int it ∗ ⌜0 ≤ i⌝ ∗ ⌜i < length tys⌝ ∗
     ∀ ty, ⌜tys !! Z.to_nat i = Some ty⌝ -∗
      typed_place K (l offset{ly2}ₗ i) β ty (λ l2 β2 ty2 typ,
       T l2 β2 ty2 (λ t, array ly2 (<[Z.to_nat i := typ t]>tys))))
    ⊢ typed_place (BinOpPCtx (PtrOffsetOp ly1) (IntOp it) v tyv :: K) l β (array ly2 tys) T.
  Proof.
    iIntros "HT" (Φ) "(%&#Hb&Hl) HΦ" => /=. iIntros "Hv".
    iDestruct ("HT" with "Hv") as (i ->) "HP". unfold int; simpl_type.
    iDestruct ("HP") as (Hv) "HP".
    iDestruct "HP" as (? Hlen) "HP".
    have [|ty ?]:= lookup_lt_is_Some_2 tys (Z.to_nat i). 1: lia.
    iApply wp_ptr_offset => //; [by apply val_to_of_loc | | ].
    { iApply (loc_in_bounds_offset with "Hb"); simpl; [done| destruct l => /=; lia | destruct l => /=; nia]. }
    iIntros "!#". iExists _. iSplit => //.
    iDestruct (big_sepL_insert_acc with "Hl") as "[Hl Hc]" => //. rewrite Z2Nat.id//.
    iApply ("HP" $! ty with "[//] Hl"). iIntros (l' ty2 β2 typ R) "Hl' Htyp HT".
    iApply ("HΦ" with "Hl' [-HT] HT"). iIntros (ty') "Hl'".
    iMod ("Htyp" with "Hl'") as "[? $]".
    iSplitR => //. iSplitR; first by rewrite length_insert. by iApply "Hc".
  Qed.
  Definition type_place_array_inst := [instance type_place_array].
  Global Existing Instance type_place_array_inst.

  Lemma type_bin_op_offset_array l β ly it v tys i T:
    (* TODO: Should we make layout_wf ly part of array such that we don't need to require it here? *)
    ⌜layout_wf ly⌝ ∗ ⌜0 ≤ i ≤ length tys⌝ ∗ (l ◁ₗ{β} array ly tys -∗ T (val_of_loc (l offset{ly}ₗ i)) ((l offset{ly}ₗ i) @ &own (array_ptr ly l i (length tys))))
    ⊢ typed_bin_op v (v ◁ᵥ i @ int it) l (l ◁ₗ{β} array ly tys) (PtrOffsetOp ly) (IntOp it) PtrOp T.
  Proof.
    iIntros "[% [% HT]]". unfold int; simpl_type.
    iIntros "%Hv (%&#Hlib&Hl)" (Φ) "HΦ".
    iApply wp_ptr_offset => //; [by apply val_to_of_loc | | ].
    { iApply (loc_in_bounds_offset with "Hlib"); simpl; [done| destruct l => /=; lia | destruct l => /=; nia]. }
    iModIntro. iApply "HΦ"; [|iApply "HT"; iFrame; by iSplit].
    unfold frac_ptr; simpl_type. iSplit; [done|]. iSplit; [done|].
    iSplit; [| by iSplit].
    iPureIntro. by apply: has_layout_loc_offset_loc.
  Qed.
  Definition type_bin_op_offset_array_inst := [instance type_bin_op_offset_array].
  Global Existing Instance type_bin_op_offset_array_inst.

  Lemma type_bin_op_offset_array_ptr l β ly it v i idx (len : nat) base T:
    ⌜layout_wf ly⌝ ∗ ⌜0 ≤ idx + i ≤ len⌝ ∗ (l ◁ₗ{β} array_ptr ly base idx len -∗ T (val_of_loc (base offset{ly}ₗ (idx + i))) ((base offset{ly}ₗ (idx + i)) @ &own (array_ptr ly base (idx + i) len)))
    ⊢ typed_bin_op v (v ◁ᵥ i @ int it) l (l ◁ₗ{β} array_ptr ly base idx len) (PtrOffsetOp ly) (IntOp it) PtrOp T.
  Proof.
    iIntros "[% [% HT]]". unfold int; simpl_type.
    iIntros "%Hv (->&%&%&#Hlib)" (Φ) "HΦ".
    iApply wp_ptr_offset => //; [by apply val_to_of_loc | | ].
    { iApply (loc_in_bounds_offset with "Hlib"); simpl; unfold addr in *; [done|nia|].
      rewrite {3}/ly_size/=. nia. }
    rewrite offset_loc_offset_loc.
    iModIntro. iApply "HΦ"; [|iApply "HT"]; unfold frac_ptr; simpl_type; iFrame "Hlib"; iPureIntro; [|done].
    split_and! => //; try lia. rewrite -offset_loc_offset_loc.
    by apply has_layout_loc_offset_loc.
  Qed.
  Definition type_bin_op_offset_array_ptr_inst := [instance type_bin_op_offset_array_ptr].
  Global Existing Instance type_bin_op_offset_array_ptr_inst.

  Lemma type_bin_op_neg_offset_array_ptr l β ly it v i idx (len : nat) base T:
    ⌜layout_wf ly⌝ ∗ ⌜0 ≤ idx - i ≤ len⌝ ∗ (l ◁ₗ{β} array_ptr ly base idx len -∗ T (val_of_loc (base offset{ly}ₗ (idx - i))) ((base offset{ly}ₗ (idx - i)) @ &own (array_ptr ly base (idx - i) len)))
    ⊢ typed_bin_op v (v ◁ᵥ i @ int it) l (l ◁ₗ{β} array_ptr ly base idx len) (PtrNegOffsetOp ly) (IntOp it) PtrOp T.
  Proof.
    iIntros "[% [% HT]]". unfold int; simpl_type.
    iIntros "%Hv (->&%&%&#Hlib)" (Φ) "HΦ".
    iApply wp_ptr_neg_offset => //; [by apply val_to_of_loc | | ].
    { iApply (loc_in_bounds_offset with "Hlib"); simpl; unfold addr in *; [done|nia|].
      rewrite {3}/ly_size/=. nia. }
    rewrite offset_loc_offset_loc Z.add_opp_r.
    iModIntro. iApply "HΦ"; [|iApply "HT"]; unfold frac_ptr; simpl_type; iFrame "Hlib"; iPureIntro; [|done].
    split_and! => //; try lia. rewrite -Z.add_opp_r -offset_loc_offset_loc.
    by apply has_layout_loc_offset_loc.
  Qed.
  Definition type_bin_op_neg_offset_array_ptr_inst := [instance type_bin_op_neg_offset_array_ptr].
  Global Existing Instance type_bin_op_neg_offset_array_ptr_inst.

  Lemma type_bin_op_diff_array_ptr_array l1 β l2 ly idx (len : nat) tys T:
    (l1 ◁ₗ{β} array_ptr ly l2 idx len -∗
    l2 ◁ₗ{β} array ly tys -∗
    ⌜0 < ly.(ly_size)⌝ ∗
    ⌜0 < length tys⌝ ∗
    ⌜idx ≤ max_int ptrdiff_t⌝ ∗
    (alloc_alive_loc l2 ∗ True) ∧
    (T (i2v idx ptrdiff_t) (idx @ int ptrdiff_t)))
    ⊢ typed_bin_op l1 (l1 ◁ₗ{β} array_ptr ly l2 idx len) l2 (l2 ◁ₗ{β} array ly tys) (PtrDiffOp ly) PtrOp PtrOp T.
  Proof.
    iIntros "HT (->&%&%&#Hlib) Hl2" (Φ) "HΦ".
    iDestruct ("HT" with "[$Hlib//] Hl2") as (? ? ?) "HT".
    have /(val_of_Z_is_Some None) [vo Hvo] : idx ∈ ptrdiff_t. {
      split; [|done].
      rewrite /min_int/=/int_half_modulus/=/bits_per_int/bytes_per_int/=/bits_per_byte. lia.
    }
    rewrite /i2v Hvo/=.
    iApply wp_ptr_diff; [by apply: val_to_of_loc|by apply: val_to_of_loc| |done|done| | |].
    { rewrite /= Z.add_simpl_l Z.mul_comm Z.div_mul //. lia. }
    { iApply (loc_in_bounds_offset with "Hlib"); simpl; unfold addr in *; [done|nia|].
      rewrite {2}/ly_size/=. nia. }
    { iApply (loc_in_bounds_shorten with "Hlib"). lia. }
    iSplit. {
      iApply alloc_alive_loc_mono; [simpl; done|].
      iDestruct "HT" as "[[$ _] _]".
    }
    iDestruct "HT" as "[_ HT]".
    iModIntro. iApply "HΦ"; [|iApply "HT"].
    unfold int; simpl_type. iPureIntro. by apply: val_to_of_Z.
  Qed.
  Definition type_bin_op_diff_array_ptr_array_inst := [instance type_bin_op_diff_array_ptr_array].
  Global Existing Instance type_bin_op_diff_array_ptr_array_inst.

  Lemma subsume_array_ptr_alloc_alive A β l ly base idx len T:
    (alloc_alive_loc base ∗ ∃ x, T x)
    ⊢ subsume (l ◁ₗ{β} array_ptr ly base idx len) (λ x : A, alloc_alive_loc l) T.
  Proof.
    iIntros "[Halive [% ?]] (->&?)".
    iExists _. iFrame. by iApply (alloc_alive_loc_mono with "Halive").
  Qed.
  Definition subsume_array_ptr_alloc_alive_inst := [instance subsume_array_ptr_alloc_alive].
  Global Existing Instance subsume_array_ptr_alloc_alive_inst | 10.

  Lemma simpl_goal_array_ptr ly base idx1 idx2 len β T:
    ⌜idx1 = idx2⌝ ∗ ⌜(base offset{ly}ₗ idx1) `has_layout_loc` ly⌝ ∗ ⌜0 ≤ idx1 ≤ Z.of_nat len⌝ ∗
       loc_in_bounds base (ly_size (mk_array_layout ly len)) ∗ T
    ⊢ simplify_goal ((base offset{ly}ₗ idx1) ◁ₗ{β} array_ptr ly base idx2 len)  T.
  Proof. by iIntros "(->&%&%&$&$)". Qed.
  Definition simpl_goal_array_ptr_inst := [instance simpl_goal_array_ptr with 50%N].
  Global Existing Instance simpl_goal_array_ptr_inst.

  Lemma subsume_array_ptr A ly1 ly2 base1 base2 idx1 idx2 len1 len2 l β T:
    (∃ x, ⌜ly1 = ly2 x⌝ ∗ ⌜base1 = base2 x⌝ ∗ ⌜idx1 = idx2 x⌝ ∗ ⌜len1 = len2 x⌝ ∗ T x)
    ⊢ subsume (l ◁ₗ{β} array_ptr ly1 base1 idx1 len1)
        (λ x : A, l ◁ₗ{β} array_ptr (ly2 x) (base2 x) (idx2 x) (len2 x)) T.
  Proof. iIntros "(%&->&->&->&->&?) ?". iExists _. iFrame. Qed.
  Definition subsume_array_ptr_inst := [instance subsume_array_ptr].
  Global Existing Instance subsume_array_ptr_inst.

  (*
  TODO: The following rule easily leads to diverging if the hypothesis is simplified before it is introduced into the context.
  Lemma simplify_array_ptr_hyp_learn_loc l β ly base idx len T:
    (⌜l = base offset{ly}ₗ idx⌝ -∗ l ◁ₗ{β} array_ptr ly base idx len -∗ T
    ⊢ simplify_hyp (l ◁ₗ{β} array_ptr ly base idx len) T.
  Proof. iIntros "HT [% #Hlib]". iApply "HT" => //. by iSplit. Qed.
  Global Instance simplify_array_ptr_hyp_learn_loc_inst l β ly base idx len `{!TCUnless (TCFastDone (l = base offset{ly}ₗ idx))}:
    SimplifyHyp _ (Some 0%N) | 10 :=
    λ T, i2p (simplify_array_ptr_hyp_learn_loc l β ly base idx len T).
*)

  Lemma simplify_hyp_array_ptr ly l β base idx len T:
    (⌜l = (base offset{ly}ₗ idx)⌝ -∗
    ⌜(base offset{ly}ₗ idx) `has_layout_loc` ly⌝ -∗
    loc_in_bounds base (ly_size (mk_array_layout ly len)) -∗
    ∃ tys, base ◁ₗ{β} array ly tys ∗ ⌜0 ≤ idx < length tys⌝ ∗ (
      ∀ ty, ⌜tys !! Z.to_nat idx = Some ty⌝ -∗ base ◁ₗ{β} array ly (<[Z.to_nat idx := place l]>tys) -∗
        l ◁ₗ{β} ty -∗ T))
    ⊢ simplify_hyp (l ◁ₗ{β} array_ptr ly base idx len) T.
  Proof.
    iIntros "HT (->&%&%&?)".
    iDestruct ("HT" with "[//] [//] [$]") as (tys) "(Harray&%&HT)".
    have [|ty ?]:= lookup_lt_is_Some_2 tys (Z.to_nat idx). 1: lia.
    iDestruct (array_get_type (Z.to_nat idx) with "Harray") as "[Hty Harray]"; [done|].
    rewrite Z2Nat.id; [|lia].
    by iApply ("HT" with "[//] Harray Hty").
  Qed.
  Definition simplify_hyp_array_ptr_inst := [instance simplify_hyp_array_ptr with 50%N].
  Global Existing Instance simplify_hyp_array_ptr_inst | 50.
End array.

Notation "array< ty , tys >" := (array ty tys)
  (only printing, format "'array<' ty ,  tys '>'") : printing_sugar.
Global Typeclasses Opaque array.
Global Typeclasses Opaque array_ptr.
