Require Import VST.floyd.proofauto.
Require Import fastpile.
Require spec_fastpile.
Require spec_fastpile_concrete.

Lemma sub_Pile_new: 
  funspec_sub (snd spec_fastpile_concrete.Pile_new_spec)
                     (snd spec_fastpile.Pile_new_spec).
Proof.
do_funspec_sub.
rename w into gv; clear H.
Exists gv emp. entailer!.
intros tau ? ?.
unfold spec_fastpile_concrete.countrep, spec_fastpile.pilerep.
unfold spec_fastpile_concrete.count_freeable, spec_fastpile.pile_freeable.
Intros s'. Exists (eval_id ret_temp tau) 0.
entailer!. rewrite H3 by lia.
apply derives_refl.
Qed.

Lemma sub_Pile_add: 
  funspec_sub (snd spec_fastpile_concrete.Pile_add_spec)
                     (snd spec_fastpile.Pile_add_spec).
Proof.
do_funspec_sub. destruct w as [[[p n] sigma] gv]; clear H. simpl. normalize.
Exists (p,n, spec_fastpile.sumlist sigma,gv) emp. normalize.
simpl in *. subst. entailer!.
- unfold spec_fastpile.pilerep, spec_fastpile_concrete.countrep.
  intros. Intros s. Exists s. entailer!.
  apply H6. simpl in H9. lia.
- clear - H2. unfold spec_fastpile.pilerep, spec_fastpile_concrete.countrep.
  Intros s; Exists s. entailer!.
  assert (0 <= spec_fastpile.sumlist sigma). {
    clear - H2; induction sigma; simpl. lia.
    inv H2. specialize (IHsigma H3). lia.
  }
  split; auto.
Qed.

Lemma sub_Pile_count: 
  funspec_sub (snd spec_fastpile_concrete.Pile_count_spec)
                     (snd spec_fastpile.Pile_count_spec).
Proof.
do_funspec_sub. destruct w as [p sigma]; clear H. simpl. normalize.
Exists (p, spec_fastpile.sumlist sigma) emp. normalize. entailer!.
- unfold spec_fastpile.pilerep, spec_fastpile_concrete.countrep.
  intros tau ? ?. Intros s. Exists s.
  specialize (H3 H0). specialize (H7 H0). entailer!.
- unfold spec_fastpile.pilerep, spec_fastpile_concrete.countrep.
  Intros s; Exists s. entailer!.
Qed.

Lemma sub_Pile_free: 
  funspec_sub (snd spec_fastpile_concrete.Pile_free_spec)
                     (snd spec_fastpile.Pile_free_spec).
Proof.
do_funspec_sub. destruct w as [[p sigma] gv]. clear H; simpl; normalize.
Exists (p, spec_fastpile.sumlist sigma, gv) emp. normalize. entailer!.
unfold spec_fastpile.pilerep, spec_fastpile_concrete.countrep.
unfold spec_fastpile_concrete.count_freeable, spec_fastpile.pile_freeable.
Intros s; Exists s. entailer!.
+ simpl in H2.
  assert (0 <= spec_fastpile.sumlist sigma). {
    clear - H0; induction sigma; simpl. lia.
    inv H0. specialize (IHsigma H3). lia.
  }
  split; auto.
+ apply derives_refl.
Qed.
