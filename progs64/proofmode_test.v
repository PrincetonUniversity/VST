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
  rewrite data_at_rec_lemmas.data_at_rec_eq /= -sep_assoc //.
Qed.

Theorem append_spec Espec lx ly : fun_triple Espec cenv_cs (λ args, ∃ x y, <affine> ⌜args = [x; y]⌝ ∗ listrep Ews lx x ∗ listrep Ews ly y)
  f_append (λ r, ∃ z, <affine> ⌜r = Some z⌝ ∗ listrep Ews (lx ++ ly) z).
Proof.
  iIntros (??) "(% & % & -> & Hx & Hy) S"; rewrite /stackframe_of' /=.
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
    wp_set. wp_load.
    iDestruct (listrep_isptr with "Htl") as %?.
    wp_field. wp_deref. wp_temp.
    { by intros ->. }
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
      iSplit.
      { iPureIntro; intros ?; simpl; done. }
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
      wp_set. wp_load.
      iDestruct (listrep_isptr with "Hl'") as %?.
      wp_field. wp_deref. wp_temp.
      { by intros ->. }
      wp_skip; simpl.
      iApply ("IH" with "[//] Hy [$] [$] [$] [$] [$] Hl'").
      iIntros "H"; iApply "Hpre"; iFrame.
      rewrite list_unfold; by iFrame.
Qed.

End append.
