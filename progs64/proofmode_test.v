Require Import VST.veric.juicy_base.
Require Import VST.veric.mpred.
Require Import VST.veric.env.
Require Import VST.veric.lifting_expr.
Require Import VST.veric.lifting.
Require Import VST.veric.mapsto_memory_block.
Require Import VST.veric.Clight_seplog.
Require Import VST.veric.proofmode.
Require Import VST.progs64.swap.
Import Clight.
Import Ctypesdefs.

Definition fun_triple `{!VSTGS OK_ty Σ} OK_spec cs (P : list val → assert) f Q : Prop :=
  forall ge args, P args -∗ stackframe_of' cs f (args ++ repeat Vundef (length (fn_temps f))) -∗
    wp OK_spec (Build_genv ge cs) ⊤ f (fn_body f)
       (frame_ret_assert (function_body_ret_assert (fn_return f) Q) (∃ lv, stackframe_of' cs f lv)).

Section swap.

Context `{VSTGS OK_ty Σ}.

Theorem swap_correct Espec ge E f ix iy :
  ⊢ temp _x (Vint ix) ∗ temp _y (Vint iy) ∗ temp _tmp Vundef -∗
  wp Espec ge E f (fn_body f_swap)
    (normal_ret_assert (temp _x (Vint iy) ∗ temp _y (Vint ix) ∗ ∃ v, temp _tmp v)).
Proof.
  iIntros "(Hx & Hy & Htmp)".
  simpl.
  wp_set; wp_temp; simpl.
  wp_set; wp_temp; simpl.
  wp_set; wp_temp; simpl.
  iFrame.
Qed.

Theorem swap_fun Espec cs : fun_triple Espec cs (λ args, <affine> ⌜exists ix iy, args = [Vint ix; Vint iy]⌝) f_swap (λ _, emp).
Proof.
  iIntros (??) "(% & % & ->) S"; rewrite /stackframe_of' /=.
  iDestruct "S" as "(_ & ? & ? & ? & _)".
  wp_set; wp_temp; simpl.
  wp_set; wp_temp; simpl.
  wp_set; wp_temp; simpl.
  iSplit; first done.
  iExists [_; _; _]; simpl; iFrame.
Qed.

End swap.

Require Import VST.veric.make_compspecs. (* deduplicate *)
Require Import VST.veric.expr.
Require Import VST.veric.val_lemmas.
Require Import VST.floyd.mapsto_memory_block.
Require Import VST.floyd.nested_field_lemmas.
Require Import VST.floyd.field_at.
Require Import VST.progs64.append.
Transparent Archi.ptr64.

Section append.

Context `{VSTGS OK_ty Σ}.

#[local] Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Definition t_struct_list := Tstruct _list noattr.

Fixpoint listrep (sh: share)
            (contents: list val) (x: val) : assert :=
 match contents with
 | h::hs =>
              ∃ y:val,
                ⎡data_at sh t_struct_list (h,y) x⎤ ∗ listrep sh hs y
 | nil => ⌜x = nullval⌝ ∧ emp
 end.

Lemma listrep_isptr : forall sh l x, listrep sh l x ⊢ ⌜val_lemmas.is_pointer_or_null x⌝.
Proof.
  intros; destruct l; simpl.
  - by iIntros "(-> & _)".
  - iIntros "(% & H & _)".
    rewrite data_at_isptr.
    iDestruct "H" as "(% & _)"; destruct x; auto.
Qed.

Transparent peq.
#[global] Arguments Pos.add : simpl nomatch.
#[global] Arguments Pos.mul : simpl nomatch.
#[global] Arguments Z.mul : simpl nomatch.
#[global] Arguments Z.add : simpl nomatch.
#[global] Arguments Z.div _ _ /.

Definition list_body sh h y x :=
  mapsto sh tint x h ∗ spacer sh 4 8 x ∗
  mapsto sh (tptr t_struct_list) (offset_val 8 x) y.

Lemma list_unfold : forall sh (h y x : val), data_at sh t_struct_list (h,y) x =
  (⌜field_compatible t_struct_list [] x⌝ ∧ list_body sh h y x).
Proof.
  intros.
  rewrite /data_at /field_at /at_offset /=.
  apply andp_prop_eq1; first apply field_compatible_dec; intros Hcompat.
  rewrite functional_base.isptr_offset_val_zero; last by destruct Hcompat.
  rewrite data_at_rec_lemmas.data_at_rec_eq /=.
  rewrite /fieldlist.field_offset_next /= /withspacer /at_offset /=.
  rewrite functional_base.isptr_offset_val_zero; last by destruct Hcompat.
  rewrite data_at_rec_lemmas.data_at_rec_eq /= -log_normalize.sep_assoc //.
Qed.

Theorem append_spec Espec lx ly : fun_triple Espec cenv_cs (λ args, ∃ x y, <affine> ⌜args = [x; y]⌝ ∗ listrep Ews lx x ∗ listrep Ews ly y)
  f_append (λ r, ∃ z, <affine> ⌜r = Some z⌝ ∗ listrep Ews (lx ++ ly) z).
Proof.
  iIntros (??) "(% & % & -> & Hx & Hy) S"; rewrite /stackframe_of' /=.
  set (cenv := _ : composite_env).
  iDestruct "S" as "(_ & Htx & Hty & Ht & Hu & _)".
  wp_if.
  wp_binop.
  wp_temp.
  destruct lx; simpl.
  - iDestruct "Hx" as "(-> & _)".
    wp_cast.
    iNext; iSplit; first done; simpl.
    wp_return.
    iDestruct (listrep_isptr with "Hy") as %?.
    wp_temp.
    simpl.
    iSplitL "Hy"; last by iExists [_; _; _; _]; iFrame.
    rewrite /= /bind_ret /=.
    by iFrame.
  - iDestruct "Hx" as "(%tl & Hx & Htl)".
    rewrite data_at_isptr; iDestruct "Hx" as "(% & Hx)".
    destruct x; try contradiction.
    wp_cast.
    { simpl.
      rewrite /sc_cmp /= /sc_cmp_ptr /=.
      iApply valid_pointer_weak; iApply (data_at_valid_ptr with "Hx"); auto; simpl; lia. }
    iNext; iSplit; first done; simpl.
    wp_set; wp_temp; simpl.
    rewrite list_unfold; iDestruct "Hx" as "(% & Hhd1 & Hspace & Htl1)".
    wp_set.
    iDestruct (listrep_isptr with "Htl") as %?.
    wp_field. wp_deref. wp_temp.
    { split; last intros ->; auto. }
    reshape_seq.
    iAssert (∃ t u a l', <affine> ⌜field_compatible t_struct_list [] t⌝ ∗ temp _t t ∗ temp _u u ∗
      ⎡list_body Ews a u t⎤ ∗ listrep Ews l' u ∗
      (listrep Ews (a :: l' ++ ly) t -∗ listrep Ews (v :: lx ++ ly) (Vptr b i))) with "[Ht Hu Hhd1 Hspace Htl1 Htl]"
      as "(% & % & % & % & %Ht & Ht & Hu & Ht1 & Hl' & Hpre)".
    { iFrame. simpl offset_val; iFrame; auto. }
    iInduction l' as [|h' l'] "IH" forall (t u a Ht); simpl; wp_loop.
    + iDestruct "Hl'" as "(-> & _)".
      wp_if; wp_binop; wp_temp.
      wp_cast.
      iNext; iSplit; first done; simpl.
      wp_break; simpl.
      iDestruct (listrep_isptr with "Hy") as %Hy.
      wp_store; wp_temp.
      { intros ?; simpl; done. }
      iDestruct "Ht1" as "(Ht1 & ? & ?)".
      destruct t; try (destruct Ht; contradiction).
      wp_field. wp_deref. wp_temp.
      wp_return. wp_temp; simpl.
      iSplitR "Htx Hty Ht Hu"; last by iExists [_; _; _; _]; iFrame.
      rewrite /= /bind_ret /=.
      iSplit; first done; iExists _; iSplit; first done.
      iApply "Hpre"; iFrame.
      rewrite list_unfold; by iFrame.
    + iDestruct "Hl'" as "(%tl' & Hh' & Hl')".
      rewrite data_at_isptr; iDestruct "Hh'" as "(% & Hh')".
      destruct u; try contradiction.
      wp_if; wp_binop; wp_temp.
      wp_cast.
      { simpl.
        rewrite /sc_cmp /= /sc_cmp_ptr /=.
        iApply valid_pointer_weak; iApply (data_at_valid_ptr with "Hh'"); auto; simpl; lia. }
      iNext; iSplit; first done; simpl.
      wp_skip; simpl.
      wp_set; wp_temp; simpl.
      rewrite list_unfold; iDestruct "Hh'" as "(% & Hhd1 & Hspace & Htl1)".
      wp_set.
      iDestruct (listrep_isptr with "Hl'") as %?.
      wp_field. wp_deref. wp_temp.
      { split; last intros ->; auto. }
      wp_skip; simpl.
      iApply ("IH" with "[//] Hy [$] [$] [$] [$] [$] Hl'").
      iIntros "H"; iApply "Hpre"; iFrame.
      rewrite list_unfold; by iFrame.
Qed.

End append.

Require Import VST.floyd.functional_base.
Require Import VST.progs64.test.

Section test.

Context `{VSTGS OK_ty Σ}.

#[local] Instance test_CompSpecs : compspecs. make_compspecs prog. Defined.

Hypothesis malloc_spec : forall Espec ge E f x v t, ∀ Φ,
  temp x v -∗
  (∀ p, temp x p -∗ ⎡mapsto_ Tsh t p⎤ -∗ tycontext.RA_normal Φ) -∗
  wp Espec ge E f (Scall (Some x) (Evar _malloc (Tfunction [tulong] (tptr tvoid) cc_default)) [Esizeof t tulong]) Φ.

Theorem test_spec Espec : fun_triple Espec cenv_cs (λ args, <affine> ⌜args = []⌝)
  f_main (λ r, ⌜r = Some (Vint (Int.repr 10))⌝).
Proof.
  iIntros (??) "-> S"; rewrite /stackframe_of' /=.
  set (cenv := _ : composite_env).
  iDestruct "S" as "((Hp & _) & Hx & Hq & Ht1 & _)".
  iDestruct "Hp" as "(% & % & Hp & Hdata)"; simpl.
  assert (align_compatible (tptr tint) (Vptr b Ptrofs.zero)) as Halign.
  { econstructor; eauto. apply Z.divide_0_r. }
  iAssert ⎡mapsto_ Tsh (tptr tint) (Vptr b Ptrofs.zero)⎤ with "[Hdata]" as "Hdata".
  { rewrite -memory_block_mapsto_ //. }
  wp_set.
  wp_apply (malloc_spec with "Ht1").
  iIntros (p1) "Ht1 Hp1"; simpl.
  iDestruct (mapsto__local_facts with "Hp1") as %Hp1.
  destruct p1; try contradiction.
  wp_store; wp_temp.
  wp_field; wp_var.
  wp_store; wp_temp.
  wp_deref. wp_field; wp_var.
  wp_set; wp_addrof; wp_var.
  iAssert (∃ n : nat, <affine> ⌜0 < n < Int.max_signed⌝ ∗ temp _x (Vint (Int.repr (Z.of_nat n))) ∗
    ⎡mapsto Tsh tint (Vptr b0 i) (Vint (Int.repr (10 - Z.of_nat n)))⎤) with "[Hx Hp1]"
    as (n) "(%Hn & Hx & Hp1)".
  { iExists 5%nat; iFrame; auto. }
  iApply wp_seq.
  iLöb as "IH" forall (n Hn).
  wp_loop; wp_skip; simpl.
  wp_store; wp_binop.
  wp_deref.
  wp_field; wp_deref; wp_temp.
  wp_deref. wp_field.
  wp_deref; wp_temp.
  wp_set; wp_binop; wp_temp.
  rewrite coqlib3.sub_repr !reptype_lemmas.ptrofs_add_repr_0_r.
  wp_if; wp_binop; wp_temp.
  iNext; iSplit; first done.
  simpl.
  rewrite /Int.lt !Int.signed_repr; [if_tac; simpl | rep_lia..].
  - wp_skip; simpl.
    wp_skip; simpl.
    replace (Z.of_nat n - 1) with (Z.of_nat (n - 1)) by lia.
    iApply ("IH" with "[%] [$] [$] [$] [$] [$]"); first by lia.
    rewrite coqlib3.add_repr.
    replace (10 - Z.of_nat n + 1) with (10 - Z.of_nat (n - 1)) by lia.
    done.
  - wp_break; simpl.
    wp_return; wp_deref.
    wp_field; wp_var.
    iSplitR "Hp Hdata Hx Hq Ht1"; last (iExists [_; _; _]; simpl; iFrame).
    rewrite /= /bind_ret /=.
    iPureIntro.
    rewrite coqlib3.add_repr.
    assert (n = 1%nat) as -> by rep_lia; auto.
    { iSplit; first done.
      change (Ctypes.sizeof _) with (sizeof (tptr tint)).
      rewrite memory_block_mapsto_ //.
      by iApply mapsto_mapsto_. }
Qed.

End test.
