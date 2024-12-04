(* ghost state for environments *)
Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import iris.algebra.excl.
Require Import VST.veric.mpred.
Require Import VST.veric.res_predicates.
Require Import VST.veric.Clight_seplog.

Definition env_state := (genviron * gmap nat (venviron * tenviron))%type.

Section env.

Context `{!envGS Σ}.

Definition env_auth (rho : env_state) := own(inG0 := envGS_inG) env_name
 (lib.gmap_view.gmap_view_auth (dfrac.DfracOwn 1) (to_agree <$> fst rho),
  ●{dfrac.DfracOwn 1} ((λ '(ve, te),
    let q := Qp.inv (pos_to_Qp (Pos.of_nat (size ve + size te))) in
    (to_agree q, (1%Qp, (Excl <$> ve : gmap _ (excl _), Excl <$> te : gmap _ (excl _))))) <$> snd rho)).

Definition env_to_environ (ρ : env_state) n : environ :=
  match (snd ρ !! n)%stdpp with Some (ve, te) => (fst ρ, ve, te)
  | None => (fst ρ, base.empty, base.empty) end.

Global Instance gmap_total `{Countable K} A : CmraTotal (iris.algebra.gmap.gmapR K A).
Proof. rewrite /CmraTotal /pcore /cmra_pcore /= /gmap.gmap_pcore_instance //. Qed.

Lemma Excl_fmap_incl : forall {A : ofe} (x y : option A), Excl <$> x ≼ Excl <$> y →
  match x with Some a => (x ≡ y)%stdpp | None => True end.
Proof.
  destruct x; last done; simpl.
  intros; destruct (Some_included_is_Some _ _ H) as (? & Heq).
  destruct y; inv Heq.
  by apply Excl_included in H as ->.
Qed.

Lemma stack_frag_e : forall ρ n q0 q ve te, env_auth ρ ∗ stack_frag n q0 q ve te ⊢
  ⌜let rho := env_to_environ ρ n in ve ⊆ ve_of rho ∧ te ⊆ te_of rho⌝.
Proof.
  intros; rewrite /env_auth /stack_frag.
  iIntros "(H1 & H2)"; iDestruct (own_valid_2 with "H1 H2") as %(_ & ((? & Heq & H)%gmap.singleton_included_l & _)%auth_both_valid_discrete); iPureIntro.
  rewrite lookup_fmap in Heq; rewrite /env_to_environ. destruct (snd ρ !! n)%stdpp as [(?, ?)|] eqn: Hn; rewrite !Hn in Heq |- *; inversion Heq as [?? HA |]; subst.
  rewrite -HA in H; clear Heq.
  apply Some_included in H as [(? & ? & Hv & Ht) | ?]; simpl in *.
  - apply (map_fmap_equiv_inj Excl), leibniz_equiv in Hv as ->; last apply Excl_inj.
    apply (map_fmap_equiv_inj Excl), leibniz_equiv in Ht as ->; last apply Excl_inj; done.
  - do 2 apply prod_included in H as (_ & H); apply prod_included in H as (Hv & Ht); simpl in *.
    rewrite !gmap.lookup_included in Hv Ht; split; intros i.
    + specialize (Hv i); rewrite !lookup_fmap in Hv.
      apply (Excl_fmap_incl(A := leibnizO _)) in Hv.
      destruct (ve !! i)%stdpp.
      * apply leibniz_equiv in Hv; rewrite -Hv //.
      * simpl; clear; destruct (_ !! _)%stdpp; done.
    + specialize (Ht i); rewrite !lookup_fmap in Ht.
      apply (Excl_fmap_incl(A := leibnizO _)) in Ht.
      destruct (te !! i)%stdpp.
      * apply leibniz_equiv in Ht; rewrite -Ht //.
      * simpl; clear; destruct (_ !! _)%stdpp; done.
Qed.

Lemma stack_frag_e_1 : forall ρ n q0 ve te, env_auth ρ ∗ stack_frag n q0 1%Qp ve te ⊢
  ⌜let rho := env_to_environ ρ n in ve = ve_of rho ∧ te = te_of rho⌝.
Proof.
  intros; rewrite /env_auth /stack_frag.
  iIntros "(H1 & H2)"; iDestruct (own_valid_2 with "H1 H2") as %(_ & (H & Hvalid)%auth_both_valid_discrete).
  apply gmap.singleton_included_exclusive_l in H; [| apply _ | done].
  rewrite lookup_fmap in H; rewrite /env_to_environ. destruct (snd ρ !! n)%stdpp as [(?, ?)|] eqn: Hn; rewrite !Hn in H |- *; inversion H as [?? HA |]; subst.
  destruct HA as (_ & _ & Hv & Ht); simpl in *.
  apply (map_fmap_equiv_inj Excl), leibniz_equiv in Hv as ->; last apply Excl_inj.
  apply (map_fmap_equiv_inj Excl), leibniz_equiv in Ht as ->; last apply Excl_inj; done.
Qed.

Lemma gvar_e : forall `{!heapGS Σ} id v rho, gvar id v ∗ env_auth rho ⊢ ⌜rho.1 !! id = Some v⌝.
Proof.
  intros; rewrite /gvar /env_auth.
  iIntros "(H1 & H2)"; iDestruct (own_valid_2 with "H2 H1") as %((? & _ & _ & Hid & _ & Hincl)%gmap_view.gmap_view_both_dfrac_valid_discrete_total & _).
  rewrite lookup_fmap in Hid; destruct (lookup _ _); inv Hid.
  apply to_agree_included_L in Hincl as ->; done.
Qed.

Lemma temp_e : forall id v rho n, temp id v n ∗ env_auth rho ⊢ ⌜te_of (env_to_environ rho n) !! id = Some v⌝.
Proof.
  intros; rewrite /temp /=.
  iIntros "((% & ?) & ?)"; iDestruct (stack_frag_e with "[$]") as %(_ & ?%map_singleton_subseteq_l); done.
Qed.

Lemma lvar_e : forall id t b rho n, lvar id t b n ∗ env_auth rho ⊢ ⌜ve_of (env_to_environ rho n) !! id = Some (b, t)⌝.
Proof.
  intros; rewrite /lvar /=.
  iIntros "((% & ?) & ?)"; iDestruct (stack_frag_e with "[$]") as %(?%map_singleton_subseteq_l & _); done.
Qed.

Definition set_temp (ρ : env_state) n i v := let '(ge, s) := ρ in
  match (s !! n)%stdpp with
  | Some (ve, te) => (ge, <[n := (ve, <[i := v]>te)]>s)
  | None => ρ end.

Lemma temp_update : forall ρ n i v v', env_auth ρ ∗ temp i v n ⊢ |==> env_auth (set_temp ρ n i v') ∗ temp i v' n.
Proof.
  intros.
  iIntros "(Hr & Hi)".
  iDestruct (temp_e with "[$Hr $Hi]") as %Hi.
  rewrite /env_to_environ in Hi.
  destruct (snd ρ !! n)%stdpp as [(?, te)|] eqn: Hn; rewrite Hn in Hi; last by rewrite lookup_empty in Hi.
  rewrite /temp /=.
  iDestruct "Hi" as (q) "Hi".
  iAssert (|==> env_auth (set_temp ρ n i v') ∗ stack_frag n q q ∅ {[i := v']}) with "[-]" as ">($ & $)"; last done.
  rewrite -own_op; iApply (own_update_2 with "Hr Hi").
  rewrite /set_temp.
  destruct ρ as (?, s); rewrite Hn /=.
  apply prod_update; first done.
  rewrite /= !fmap_insert.
  eapply auth_update, (gmap.singleton_local_update(A := fixed_fracR frameR)).
  { rewrite lookup_fmap Hn //. }
  apply prod_local_update; simpl.
  - rewrite map_size_insert_Some //.
  - repeat (apply prod_local_update; first done); simpl.
    eapply (gmap.singleton_local_update(A := exclR (leibnizO _))).
    { rewrite lookup_fmap Hi //. }
    apply exclusive_local_update; done.
Qed.

Lemma stack_frag_join : forall n q0 q0' q1 q2 ve1 ve2 te1 te2,
  stack_frag n q0 q1 ve1 te1 ∗ stack_frag n q0' q2 ve2 te2 ⊢ ⌜q0 = q0' ∧ ve1 ##ₘ ve2 ∧ te1 ##ₘ te2⌝ ∧ stack_frag n q0 (q1 + q2)%Qp (ve1 ∪ ve2) (te1 ∪ te2).
Proof.
  intros.
  rewrite /stack_frag -own_op -cmra.pair_op -auth_frag_op gmap.singleton_op -!cmra.pair_op.
  iIntros "H"; iDestruct (own_valid with "H") as %(_ & (Hq & _ & Hv & Ht)%auth_frag_valid_1%gmap.singleton_valid); simpl in *.
  apply to_agree_op_inv_L in Hq as ->; rewrite agree_idemp !map_fmap_union.
  assert (ve1 ##ₘ ve2).
  { intros i; specialize (Hv i); rewrite gmap.lookup_op !lookup_fmap in Hv.
    destruct (ve1 !! i)%stdpp, (ve2 !! i)%stdpp; done. }
  assert (te1 ##ₘ te2).
  { intros i; specialize (Ht i); rewrite gmap.lookup_op !lookup_fmap in Ht.
    destruct (te1 !! i)%stdpp, (te2 !! i)%stdpp; done. }
  rewrite !gmap.gmap_op_union; auto; by apply map_disjoint_fmap.
Qed.

Lemma stack_frag_split : forall n q0 q1 q2 ve1 ve2 te1 te2, ve1 ##ₘ ve2 → te1 ##ₘ te2 →
  stack_frag n q0 (q1 ⋅ q2) (ve1 ∪ ve2) (te1 ∪ te2) ⊢
  stack_frag n q0 q1 ve1 te1 ∗ stack_frag n q0 q2 ve2 te2.
Proof.
  intros.
  rewrite /stack_frag -own_op -cmra.pair_op -auth_frag_op gmap.singleton_op -!cmra.pair_op agree_idemp.
  rewrite !map_fmap_union !gmap.gmap_op_union; auto; by apply map_disjoint_fmap.
Qed.

Lemma lvars_equiv : forall ll lb n, length ll = length lb → list_norepet (map fst ll) →
  ([∗ list] '(i, t);b ∈ ll;lb, lvar i t b n) ⊣⊢ if decide (length ll = O) then emp else
  ∃ q : frac, stack_frag n q (pos_to_Qp (Pos.of_nat (length ll)) * q)%Qp (list_to_map (zip (map fst ll) (zip lb (map snd ll)))) ∅.
Proof.
  induction ll as [|(i, t)]; destruct lb; inversion 1; simpl; first done.
  intros Hno; inv Hno; rewrite IHll //.
  destruct (decide _).
  { rewrite e; destruct ll; last done; simpl.
    rewrite bi.sep_emp; do 2 f_equiv.
    rewrite Qp.mul_1_l //. }
  iSplit.
  - iIntros "((% & H) & Hrest)".
    iExists q; iDestruct "Hrest" as (q') "Hrest".
    iDestruct (stack_frag_join with "[$H $Hrest]") as ((<- & ? & _)) "H".
    rewrite -insert_union_singleton_l.
    replace (pos_to_Qp (Pos.of_nat (S (base.length ll)))) with (1 + pos_to_Qp (Pos.of_nat (base.length ll)))%Qp.
    rewrite Qp.mul_add_distr_r Qp.mul_1_l //.
    { rewrite pos_to_Qp_add pos_to_Qp_inj_iff Nat2Pos.inj_succ //.
      rewrite Pplus_one_succ_l //. }
  - iIntros "(% & H)".
    rewrite bi.sep_exist_r; iExists q.
    rewrite bi.sep_exist_l; iExists q.
    iApply stack_frag_split.
    { apply map_disjoint_singleton_l_2.
      rewrite not_elem_of_list_to_map_1 //.
      intros ((?, ?) & ? & ?%elem_of_zip_l%elem_of_list_In)%elem_of_list_fmap_2; simpl in *; congruence. }
    { done. }
    rewrite -insert_union_singleton_l.
    replace (pos_to_Qp (Pos.of_nat (S (length ll)))) with (1 + pos_to_Qp (Pos.of_nat (length ll)))%Qp.
    rewrite Qp.mul_add_distr_r Qp.mul_1_l //.
    * rewrite pos_to_Qp_add pos_to_Qp_inj_iff Nat2Pos.inj_succ //.
      rewrite Pplus_one_succ_l //.
Qed.

Lemma temps_equiv : forall lt lv n, length lt = length lv → list_norepet lt →
  ([∗ list] i;v ∈ lt;lv, temp i v n) ⊣⊢ if decide (length lt = O) then emp else
  ∃ q : frac, stack_frag n q (pos_to_Qp (Pos.of_nat (length lt)) * q)%Qp ∅ (list_to_map (zip lt lv)).
Proof.
  induction lt; destruct lv; inversion 1; simpl; first done.
  intros Hno; inv Hno; rewrite IHlt //.
  destruct (decide _).
  { rewrite e; destruct lt; last done; simpl.
    rewrite bi.sep_emp; do 2 f_equiv.
    rewrite Qp.mul_1_l //. }
  iSplit.
  - iIntros "((% & H) & Hrest)".
    iExists q; iDestruct "Hrest" as (q') "Hrest".
    iDestruct (stack_frag_join with "[$H $Hrest]") as ((<- & ? & _)) "H".
    rewrite -insert_union_singleton_l.
    replace (pos_to_Qp (Pos.of_nat (S (base.length lt)))) with (1 + pos_to_Qp (Pos.of_nat (base.length lt)))%Qp.
    rewrite Qp.mul_add_distr_r Qp.mul_1_l //.
    { rewrite pos_to_Qp_add pos_to_Qp_inj_iff Nat2Pos.inj_succ //.
      rewrite Pplus_one_succ_l //. }
  - iIntros "(% & H)".
    rewrite bi.sep_exist_r; iExists q.
    rewrite bi.sep_exist_l; iExists q.
    iApply stack_frag_split.
    { done. }
    { apply map_disjoint_singleton_l_2.
      rewrite not_elem_of_list_to_map_1 //.
      intros ((?, ?) & ? & ?%elem_of_zip_l%elem_of_list_In)%elem_of_list_fmap_2; simpl in *; congruence. }
    rewrite -insert_union_singleton_l.
    replace (pos_to_Qp (Pos.of_nat (S (length lt)))) with (1 + pos_to_Qp (Pos.of_nat (length lt)))%Qp.
    rewrite Qp.mul_add_distr_r Qp.mul_1_l //.
    * rewrite pos_to_Qp_add pos_to_Qp_inj_iff Nat2Pos.inj_succ //.
      rewrite Pplus_one_succ_l //.
Qed.

Lemma norepet_NoDup : forall {A} (l : list A), list_norepet l ↔ base.NoDup l.
Proof.
  induction l; split; inversion 1; constructor; subst.
  - rewrite elem_of_list_In //.
  - rewrite -IHl //.
  - rewrite -elem_of_list_In //.
  - rewrite IHl //.
Qed.

Definition alloc_vars ve te n (ρ : env_state) := (fst ρ, <[n := (ve, te)]>(snd ρ)).

Lemma env_to_environ_alloc : forall ve te n ρ, env_to_environ (alloc_vars ve te n ρ) n = (ρ.1, ve, te).
Proof.
  intros; rewrite /env_to_environ /alloc_vars lookup_insert //.
Qed.

Lemma env_alloc : forall ρ n ve te, (snd ρ !! n)%stdpp = None →
  env_auth ρ ⊢ |==> env_auth (ρ.1, <[n := (ve, te)]> ρ.2) ∗ stack_frag n (/ pos_to_Qp (Pos.of_nat (size ve + size te)))%Qp 1%Qp ve te.
Proof.
  intros.
  rewrite /env_auth /stack_frag -own_op; apply own_update.
  apply prod_update; simpl; first reflexivity.
  rewrite fmap_insert.
  apply auth_update_alloc, (gmap.alloc_singleton_local_update(A := fixed_fracR frameR)).
  * rewrite lookup_fmap H //.
  * split3; try done; simpl.
    split; intros i; rewrite /= lookup_fmap; destruct (_ !! i)%stdpp; done.
Qed.

Lemma env_to_environ_dealloc : forall n1 n2 ρ, n1 ≠ n2 → env_to_environ (ρ.1, delete n1 ρ.2) n2 = env_to_environ ρ n2.
Proof.
  intros; rewrite /env_to_environ /alloc_vars lookup_delete_ne //.
Qed.

(* note that this doesn't support deadvars -- forgetting variables isn't consistent
   with stackframe deallocation by frame-preserving update. Instead, we should hide
   undef temps and let ourselves set temps to undef. *)
Lemma env_dealloc : forall ρ n q ve te,
  env_auth ρ ∗ stack_frag n q 1%Qp ve te ⊢ |==> env_auth (ρ.1, delete n ρ.2).
Proof.
  intros.
  rewrite /env_auth /stack_frag -own_op; apply own_update.
  apply prod_update; simpl; first reflexivity.
  rewrite fmap_delete.
  apply auth_update_dealloc, (gmap.delete_singleton_local_update(A := fixed_fracR frameR)), _.
Qed.

End env.
