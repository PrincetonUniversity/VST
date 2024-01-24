Require Import VST.concurrency.conclib.
From iris_ora.algebra Require Import gmap frac_auth.
Require Import VST.atomics.SC_atomics.

Section AEHist.

Section gmap_frac.

Context K `{Countable K} (A : ofe).

Lemma gmap_excl_flat : forall n (x y : gmapUR K (exclR A)), ✓{n} y → x ≼ₒ{n} y → x ≡{n}≡ y.
Proof.
  intros ??? Hv Hord i; specialize (Hord i).
  hnf in Hord.
  destruct (x !! i)%stdpp eqn: Hx, (y !! i)%stdpp eqn: Hy; rewrite Hx Hy // in Hord |- *.
  - inv Hord; try done.
    by repeat constructor.
  - specialize (Hv i); rewrite Hy in Hv.
    specialize (Hord o).
    destruct o; try done.
    inv Hord.
Qed.

Canonical Structure gmap_frac_authR := frac_authR gmap_excl_flat.
Canonical Structure gmap_frac_authUR := frac_authUR gmap_excl_flat.

End gmap_frac.

(* These histories should be usable for any atomically accessed location. *)
Inductive AE_hist_el := AE (r : val) (w : val).

Fixpoint apply_hist a h :=
  match h with
  | [] => Some a
  | AE r w :: h' => if eq_dec r a then apply_hist w h' else None
  end.

Lemma apply_hist_app : forall h1 i h2, apply_hist i (h1 ++ h2) =
  match apply_hist i h1 with Some v => apply_hist v h2 | None => None end.
Proof.
  induction h1; auto; simpl; intros.
  destruct a.
  destruct (eq_dec r i); auto.
Qed.

End AEHist.

Notation hist := (gmap nat (excl AE_hist_el)).

Fixpoint list_to_hist (l : list AE_hist_el) n : hist :=
  match l with
  | [] => ∅
  | e :: rest => <[n := Excl e]> (list_to_hist rest (S n))
  end.

Lemma list_to_hist_lookup : forall l n i, (n <= i)%nat ->
  (list_to_hist l n !! i)%stdpp = option_map Excl (nth_error l (i - n)).
Proof.
  induction l; simpl; intros.
  - rewrite lookup_empty nth_error_nil //.
  - destruct (eq_dec n i).
    + subst; rewrite lookup_insert Nat.sub_diag //.
    + rewrite lookup_insert_ne //.
      destruct (i - n)%nat as [|n'] eqn: Hi; first lia.
      rewrite IHl /=; last lia.
      do 2 f_equal; lia.
Qed.

Lemma list_to_hist_insert : forall l n e,
  <[(n + length l)%nat := Excl e]>(list_to_hist l n) = list_to_hist (l ++ [e]) n.
Proof.
  induction l; simpl; intros.
  - rewrite Nat.add_0_r //.
  - rewrite insert_commute; last lia.
    replace (n + S _)%nat with (S n + length l)%nat by lia.
    rewrite IHl //.
Qed.

Definition hist_incl (h : hist) l := forall t e, (h !! t)%stdpp = Some (Excl e) -> nth_error l t = Some e.

Definition newer (l : hist) t := forall t', (l !! t')%stdpp <> None -> (t' < t)%nat.

Lemma hist_incl_lt : forall (h : hist) l (Hv : ✓ (h : gmapUR _ (exclR (leibnizO _)))),
  hist_incl h l -> newer h (length l).
Proof.
  unfold hist_incl; repeat intro.
  specialize (H t'); specialize (Hv t').
  destruct (h !! t')%stdpp as [e|] eqn: Ht'; [|contradiction].
  rewrite Ht' in Hv.
  destruct e; try done.
  by apply nth_error_Some; erewrite H.
Qed.

Section AE.

Context `{!VSTGS OK_ty Σ} `{!inG Σ (gmap_frac_authR nat (leibnizO AE_hist_el))}
  `{!atomic_int_impl}.

Definition ghost_ref h g := own g (●F (list_to_hist h O : gmapR _ (exclR (leibnizO _)))).
Definition ghost_hist q (h : gmap nat (excl AE_hist_el)) g := own g (◯F{q} (h : gmapR _ (exclR (leibnizO _)))).

Lemma hist_ref_incl : forall sh h h' p,
  ghost_hist sh h p ∗ ghost_ref h' p ⊢ ⌜hist_incl h h'⌝.
Proof.
  intros; iIntros "(Hh & Hr)".
  iPoseProof (own_valid_2 with "Hr Hh") as "H".
  rewrite frac_auth_agreeI.
  if_tac.
  - iDestruct "H" as "(%Hh & _)"; iPureIntro.
    apply leibniz_equiv in Hh as <-.
    intros ??.
    rewrite list_to_hist_lookup; last lia.
    destruct (nth_error _ _) eqn: E; inversion 1; subst.
    rewrite Nat.sub_0_r // in E.
  - iDestruct "H" as "(%Hh & _)"; iPureIntro.
    assert (forall i, cmra.included(A := cmra.optionR (iris.algebra.excl.exclR (leibnizO AE_hist_el)))
      (h !! i)%stdpp (list_to_hist h' 0 !! i)%stdpp) as Hincl.
    { rewrite -gmap.lookup_included //. }
    intros ?? Ht.
    specialize (Hincl t); rewrite Ht list_to_hist_lookup in Hincl; last lia.
    rewrite  Nat.sub_0_r in Hincl.
    destruct (nth_error h' t) eqn: Hnth.
    rewrite Excl_included in Hincl; rewrite Hincl //.
    { rewrite option_included in Hincl.
      destruct Hincl as [| (? & ? & ? & ? & ?)]; done. }
Qed.

Lemma hist_add' : forall sh h h' e p,
  ghost_hist sh h p ∗ ghost_ref h' p ⊢ |==>
  ghost_hist sh (<[length h' := Excl e]>h) p ∗ ghost_ref (h' ++ [e]) p.
Proof.
  intros; iIntros "(Hh & Hr)".
  iMod (own_update_2 with "Hr Hh") as "H".
  { apply (@frac_auth_update (iris.algebra.gmap.gmapR _ _) sh (list_to_hist h' 0:
      iris.algebra.gmap.gmapUR nat (iris.algebra.excl.exclR (leibnizO AE_hist_el)))).
    apply (gmap.alloc_local_update _ _ (length h') ((Excl e) : exclR (leibnizO _))); last done.
    rewrite list_to_hist_lookup; last lia.
    rewrite (proj2 (nth_error_None _ _)) //; lia. }
  iDestruct (own_op with "H") as "(Hr & $)".
  rewrite (list_to_hist_insert _ O) //.
Qed.

(* the lock invariant used to encode an atomic invariant *)
Definition AE_inv x g i (R : list AE_hist_el -d> val -d> mpred) := ∃ h v, ⌜apply_hist i h = Some v /\ tc_val tint v⌝ ∧
  (atomic_int_at Ews v x ∗ ghost_ref h g ∗ R h v).

#[export] Instance AE_inv_ne x g i : NonExpansive (AE_inv x g i).
Proof. solve_proper. Qed.

Lemma AE_inv_exclusive : forall x g i R, exclusive_mpred (AE_inv x g i R).
Proof.
  unfold AE_inv; intros.
  rewrite /exclusive_mpred; iIntros "((% & % & % & Ha & _) & (% & % & % & Hb & _))".
  iApply atomic_int_conflict; last iFrame; auto.
Qed.

Definition AE_loc sh p g i (R : list AE_hist_el -d> val -d> mpred) (h : hist) := inv (nroot .@ "AE") (AE_inv p g i R) ∗ ghost_hist sh h g.

#[export] Instance AE_loc_ne sh p g i n : Proper (dist n ==> eq ==> dist n) (AE_loc sh p g i).
Proof. solve_proper. Qed.

(* This predicate describes the valid pre- and postconditions for a given atomic invariant R. *)
Definition AE_spec i (P : hist -d> val -d> mpred) (R : list AE_hist_el -d> val -d> mpred) (Q : hist -d> val -d> mpred) := ∀ hc hx vc vx,
  ⌜apply_hist i hx = Some vx /\ hist_incl hc hx⌝ →
  ((▷R hx vx ∗ P hc vc) -∗ (|==> ▷R (hx ++ [AE vx vc]) vc ∗
    Q (<[length hx := Excl (AE vx vc)]>hc) vx)).

#[export] Instance AE_spec_ne i : NonExpansive3 (AE_spec i).
Proof. solve_proper. Qed.

Definition AE_type := ProdType (ProdType (ProdType
  (ConstType (Qp * val * gname * val * val * hist))
  (DiscreteFunType hist (DiscreteFunType val Mpred)))
  (DiscreteFunType (list AE_hist_el) (DiscreteFunType val Mpred)))
  (DiscreteFunType hist (DiscreteFunType val Mpred)).

(* specification of atomic exchange *)
Program Definition atomic_exchange_spec :=
  TYPE AE_type WITH lsh : Qp, tgt : val, g : gname,
    i : val, v : val, h : hist, P : hist -> val -> mpred, R : list AE_hist_el -> val -> mpred, Q : hist -> val -> mpred
  PRE [ tptr tint, tint ]
   PROP (tc_val tint v)
   PARAMS (tgt;  v) GLOBALS ()
   SEP (AE_loc lsh tgt g i R h; P h v; AE_spec i P R Q)
  POST [ tint ]
   ∃ t : nat, ∃ v' : val,
   PROP (tc_val tint v'; newer h t)
   LOCAL (temp ret_temp v')
   SEP (AE_loc lsh tgt g i R (<[t := Excl (AE v' v)]>h); Q (<[t := Excl (AE v' v)]>h) v').
Next Obligation.
Proof.
  intros ? ((((((((?, ?), ?), ?), ?), ?), ?), ?), ?) (((((?, ?), ?), ?), ?), ?) ((([=] & ?) & ?) & ?) rho; simpl in *; subst; simpl in *.
  solve_proper.
Qed.
Next Obligation.
Proof.
  intros ? ((((((((?, ?), ?), ?), ?), ?), ?), ?), ?) (((((?, ?), ?), ?), ?), ?) ((([=] & ?) & ?) & ?) rho; simpl in *; subst; simpl in *.
  solve_proper.
Qed.

(* to SC_atomics? *)
Axiom atomic_int_timeless : forall sh v p, Timeless (atomic_int_at sh v p).
#[export] Existing Instance atomic_int_timeless.

Lemma AE_sub : funspec_sub SC_atomics.atomic_exchange_spec atomic_exchange_spec.
Proof.
  split; first done.
  intros ((((((((q, p), g), i), v), h), P), R), Q) ?; simpl.
  iIntros "(% & (% & _) & % & H) !>"; iExists (p, v, ⊤, ∅,
    fun v' => ∃ t, ⌜tc_val tint v' /\ newer h t⌝ ∧ AE_loc q p g i R (<[t := Excl (AE v' v)]>h) ∗ Q (<[t := Excl (AE v' v)]>h) v'), emp.
  iSplit.
  - repeat (iSplit; first done).
    rewrite /SEPx /= /LOCALx /argsassert2assert /=; monPred.unseal.
    repeat (iSplit; first done).
    iDestruct "H" as "(_ & (#I & hist) & P & spec & _)".
    iSplit; last done.
    iInv "I" as "(% & % & HI)" "Hclose".
    rewrite bi.later_and; iDestruct "HI" as "(>(%Hh0 & %) & >Hp & >ref & R)".
    iApply fupd_mask_intro; first set_solver; iIntros "Hmask".
    iExists _, _; iFrame "Hp"; iSplit; first done.
    iIntros "Hp".
    iMod "Hmask" as "_".
    iDestruct (own_valid with "hist") as "#Hh".
    rewrite frac_auth_frag_validI ouPred.discrete_valid.
    iDestruct "Hh" as "(_ & %)".
    iDestruct (hist_ref_incl with "[$hist $ref]") as %?.
    iMod (hist_add' with "[$hist $ref]") as "(hist & ref)".
    rewrite /AE_spec.
    iMod ("spec" with "[%] [$P $R]") as "(R & Q)"; first done.
    iMod ("Hclose" with "[Hp ref R]") as "_".
    { rewrite /AE_inv; iNext.
      iExists _, _; iFrame; iPureIntro.
      repeat (split; auto).
      rewrite apply_hist_app Hh0 /=.
      apply eq_dec_refl. }
    iIntros "!>"; iExists _; iFrame.
    iSplit; last done.
    iPureIntro; split; auto.
    apply hist_incl_lt; done.
  - iPureIntro; intros.
    iIntros "(% & _ & % & _ & ? & H & _)"; simpl.
    iDestruct "H" as (t ?) "(? & ?)".
    iExists t, v'; iSplit.
    { simpl; iPureIntro; tauto. }
    iSplit; first done.
    simpl; iFrame.
Qed.

Search Op gmap.

Lemma AE_loc_join : forall sh1 sh2 p g i R h1 h2,
  AE_loc sh1 p g i R h1 ∗ AE_loc sh2 p g i R h2 ⊣⊢ AE_loc (sh1 ⋅ sh2) p g i R (@op _ (gmap.gmap_op_instance(A := exclR (leibnizO _))) h1 h2).
Proof.
  intros; rewrite /AE_loc.
  assert (ghost_hist (sh1 ⋅ sh2) (h1 ⋅ h2) g ⊣⊢ ghost_hist sh1 h1 g ∗ ghost_hist sh2 h2 g) as ->.
  { rewrite -own_op. rewrite /ghost_hist; f_equiv.
    rewrite frac_op.
    apply (@frac_auth_frag_op (gmapR _ (exclR (leibnizO _))) sh1 sh2 h1 h2). }
  iSplit.
  - iIntros "(($ & $) & (_ & $))".
  - iIntros "(#$ & $ & $)".
Qed.

End AE.

#[export] Hint Resolve AE_inv_exclusive : core.
