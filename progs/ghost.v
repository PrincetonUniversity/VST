(* This probably doesn't belong in progs. Talk to Santiago about where it should go. *)
Require Import floyd.proofauto.
Require Export msl.predicates_sl.

Class PCM (A : Type) :=
  { join : A -> A -> A -> Prop; (*initial : A -> Prop;*)
    join_comm : forall a b c, join a b c -> join b a c;
    join_assoc : forall a b c d e, join a b c -> join c d e ->
                 exists c', join b d c' /\ join a c' e }.
Section Ghost.

Context {CS : compspecs}.

Section PCM.

Context `{M : PCM}.

(* This is an overapproximation of IRIS's concept of view shift. *)
Definition view_shift A B := forall (Espec : OracleKind) D P Q R C P',
  semax D (PROPx P (LOCALx Q (SEPx (B :: R)))) C P' ->
  semax D (PROPx P (LOCALx Q (SEPx (A :: R)))) C P'.

Axiom view_shift_super_non_expansive : forall n P Q, compcert_rmaps.RML.R.approx n (!!view_shift P Q) =
  compcert_rmaps.RML.R.approx n (!!view_shift (compcert_rmaps.RML.R.approx n P) (compcert_rmaps.RML.R.approx n Q)).

Definition joins a b := exists c, join a b c.

Definition update a b := forall c, joins a c -> joins b c.

(* General PCM-based ghost state *)
Parameter ghost : forall (g : A) (p : val), mpred.

(*Axiom new_ghost : forall t v p (g : A), initial g ->
  view_shift (data_at Tsh t v p) (ghost Tsh g p * data_at Tsh t v p).*)

Axiom ghost_join : forall g1 g2 g p, join g1 g2 g -> ghost g1 p * ghost g2 p = ghost g p.
Axiom ghost_conflict : forall g1 g2 p, ghost g1 p * ghost g2 p |-- !!joins g1 g2.
Axiom ghost_update : forall g g' p, update g g' -> view_shift (ghost g p) (ghost g' p).
Axiom ghost_inj : forall p g1 g2 r1 r2 r
  (Hp1 : predicates_hered.app_pred (ghost g1 p) r1)
  (Hp1 : predicates_hered.app_pred (ghost g2 p) r2)
  (Hr1 : sepalg.join_sub r1 r) (Hr2 : sepalg.join_sub r2 r),
  r1 = r2 /\ g1 = g2.

Lemma ex_ghost_precise : forall p, precise (EX g : A, ghost g p).
Proof.
  intros ???? (? & ?) (? & ?) ??.
  eapply ghost_inj; eauto.
Qed.

Corollary ghost_precise : forall g p, precise (ghost g p).
Proof.
  intros.
  eapply derives_precise, ex_ghost_precise.
  intros ??; exists g; eauto.
Qed.

End PCM.

(* In general, when can we say that a ghost resource is precise? *)

Instance Prod_PCM {A B} (MA : PCM A) (MB : PCM B) : PCM (A * B) :=
  { join a b c := join (fst a) (fst b) (fst c) /\ join (snd a) (snd b) (snd c)(*;
    initial a := initial (fst a) /\ initial (snd a)*) }.
Proof.
  - intros ??? (? & ?); split; apply join_comm; auto.
  - intros ????? (? & ?) (HA & HB).
    eapply join_assoc in HA; eauto.
    eapply join_assoc in HB; eauto.
    destruct HA as (c'a & ? & ?), HB as (c'b & ? & ?); exists (c'a, c'b); split; split; auto.
Defined.

(* Instances of ghost state *)
Section GVar.

Context {A : Type}.

Lemma join_Bot : forall a b, sepalg.join a b Share.bot -> a = Share.bot /\ b = Share.bot.
Proof.
  intros ?? (? & ?).
  apply lub_bot_e; auto.
Qed.

Global Instance Var_PCM : PCM (share * A) := { join a b c := sepalg.join (fst a) (fst b) (fst c) /\
  (fst a = Share.bot /\ c = b \/ fst b = Share.bot /\ c = a \/ snd a = snd b /\ snd b = snd c) }.
Proof.
  - intros ??? (? & Hcase); split; [apply sepalg.join_comm; auto|].
    destruct Hcase as [? | [? | (-> & ?)]]; auto.
  - intros ????? (? & Hcase1) (Hj2 & Hcase2).
    eapply sepalg.join_assoc in Hj2; eauto.
    destruct Hj2 as (sh & Hj1' & Hj2').
    destruct Hcase2 as [(Hbot & ?) | [(Hbot & ?) | (? & He)]]; subst.
    + rewrite Hbot in H; apply join_Bot in H; destruct H as (Ha & Hb); rewrite Ha in *.
      assert (fst d = sh).
      { eapply sepalg.join_eq; eauto. }
      exists (sh, snd d); split; split; auto; destruct d; subst; auto.
    + rewrite Hbot in *; assert (fst b = sh).
      { eapply sepalg.join_eq; eauto. }
      exists (sh, snd b); split; split; auto; destruct b; subst; auto.
    + destruct Hcase1 as [(Hbot & ?) | [(Hbot & ?) | (? & ?)]]; subst.
      * exists (sh, snd b); split; split; auto; destruct b; subst; auto.
        rewrite Hbot in *; assert (fst e = sh).
        { eapply sepalg.join_eq; eauto. }
        destruct e; subst; simpl in *.
        rewrite He in *; auto.
      * exists (sh, snd d); split; split; auto.
        rewrite Hbot in *; assert (fst d = sh).
        { eapply sepalg.join_eq; eauto. }
        destruct d; auto.
      * rewrite <- He.
        exists (sh, snd d); split; split; auto; destruct d; simpl in *; subst; auto.
        replace (snd a) with (snd b) in *; auto.
Defined.

Lemma joins_id : forall a b, sepalg.joins (fst a) (fst b) -> snd a = snd b -> joins a b.
Proof.
  intros ?? (sh & ?) ?.
  exists (sh, snd a); simpl; auto.
Qed.

Definition ghost_var (sh : share) (v : A) p := ghost (sh, v) p.

Lemma ghost_var_share_join : forall sh1 sh2 sh v p, sepalg.join sh1 sh2 sh ->
  ghost_var sh1 v p * ghost_var sh2 v p = ghost_var sh v p.
Proof.
  intros; apply ghost_join; simpl; auto.
Qed.

Lemma unreadable_bot : ~readable_share Share.bot.
Proof.
  unfold readable_share, nonempty_share, sepalg.nonidentity.
  rewrite Share.glb_bot; auto.
Qed.

Lemma ghost_var_inj : forall sh1 sh2 v1 v2 p, readable_share sh1 -> readable_share sh2 ->
  ghost_var sh1 v1 p * ghost_var sh2 v2 p |-- !!(v1 = v2).
Proof.
  intros.
  eapply derives_trans; [apply ghost_conflict|].
  apply prop_left; intros (? & ? & [(? & ?) | [(? & ?) | (? & ?)]]); simpl in *; subst;
    try (exploit unreadable_bot; eauto; contradiction).
  apply prop_right; auto.
Qed.

Lemma join_Tsh : forall a b, sepalg.join Tsh a b -> b = Tsh /\ a = Share.bot.
Proof.
  intros ?? (? & ?).
  rewrite Share.glb_commute, Share.glb_top in H; subst; split; auto.
  apply Share.lub_bot.
Qed.

Lemma ghost_var_update : forall v p v', view_shift (ghost_var Tsh v p) (ghost_var Tsh v' p).
Proof.
  intros; apply ghost_update; intros ? (? & ? & Hcase); simpl in *.
  apply join_Tsh in H; destruct H as (? & Hbot).
  exists (Tsh, v'); simpl; split; auto.
  rewrite Hbot; auto.
Qed.

Lemma ghost_var_precise : forall sh p, precise (EX v : A, ghost_var sh v p).
Proof.
  intros; eapply derives_precise, ex_ghost_precise.
  intros ? (x & ?); exists (sh, x); eauto.
Qed.

Lemma ghost_var_precise' : forall sh v p, precise (ghost_var sh v p).
Proof.
  intros; apply derives_precise with (Q := EX v : A, ghost_var sh v p);
    [exists v; auto | apply ghost_var_precise].
Qed.

End GVar.

Section GHist.

(* Ghost histories in the style of Nanevsky *)
Variable hist_el : Type.

Definition hist_part := list (nat * hist_el).

(* We want to split a history into two parts: a reference part that is always complete,
   and a splittable part that can be shared among clients. *)
Instance reference_PCM : PCM (option (list hist_el)) :=
  { join a b c := a = c /\ b = None \/ b = c /\ a = None }.
Proof.
  - intros ??? [(? & ?) | (? & ?)]; subst; auto.
  - intros ????? [(? & ?) | (? & ?)] [(? & ?) | (? & ?)]; subst; eexists; split; eauto.
Defined.

Require Import Sorting.Permutation.

Definition disjoint (h1 h2 : hist_part) := forall n e, In (n, e) h1 -> forall e', ~In (n, e') h2.

Lemma disjoint_nil : forall l, disjoint l [].
Proof.
  repeat intro; contradiction.
Qed.
Hint Resolve disjoint_nil.

Lemma disjoint_comm : forall a b, disjoint a b -> disjoint b a.
Proof.
  intros ?? Hdisj ?? Hin ? Hin'.
  eapply Hdisj; eauto.
Qed.

Lemma disjoint_app : forall a b c, disjoint (a ++ b) c <-> disjoint a c /\ disjoint b c.
Proof.
  split.
  - intro; split; repeat intro; eapply H; eauto; rewrite in_app; eauto.
  - intros (Ha & Hb) ?????.
    rewrite in_app in H; destruct H; [eapply Ha | eapply Hb]; eauto.
Qed.

Require Import Morphisms.

Global Instance Permutation_disjoint :
  Proper (@Permutation _ ==> @Permutation _ ==> iff) disjoint.
Proof.
  intros ?? Hp1 ?? Hp2.
  split; intro Hdisj; repeat intro.
  - eapply Hdisj; [rewrite Hp1 | rewrite Hp2]; eauto.
  - eapply Hdisj; [rewrite <- Hp1 | rewrite <- Hp2]; eauto.
Qed.

Instance map_PCM : PCM hist_part := { join a b c := disjoint a b /\ Permutation (a ++ b) c }.
Proof.
  - intros ??? (Hdisj & ?); split.
    + apply disjoint_comm; auto.
    + etransitivity; [|eauto].
      apply Permutation_app_comm.
  - intros ????? (Hd1 & Hc) (Hd2 & He).
    rewrite <- Hc, disjoint_app in Hd2; destruct Hd2 as (Hd2 & Hd3).
    exists (b ++ d); repeat split; auto.
    + apply disjoint_comm; rewrite disjoint_app; split; apply disjoint_comm; auto.
    + etransitivity; [|eauto].
      rewrite app_assoc; apply Permutation_app_tail; auto.
Defined.

Definition hist_incl h (h' : list hist_el) := forall x y, In (x, y) h -> nth_error h' x = Some y.

Lemma hist_incl_lt : forall h h', hist_incl h h' -> Forall (fun x => fst x < length h')%nat h.
Proof.
  intros.
  rewrite Forall_forall; intros (?, ?) Hin.
  specialize (H _ _ Hin).
  simpl; rewrite <- nth_error_Some, H; discriminate.
Qed.

Global Instance hist_PCM : PCM (hist_part * option (list hist_el)) :=
 { join a b c := @join _ map_PCM (fst a) (fst b) (fst c) /\ @join _ reference_PCM (snd a) (snd b) (snd c) /\
                 match snd c with Some h => hist_incl (fst c) h | None => True end }.
Proof.
  - intros ??? (? & ? & ?).
    split; [|split; auto]; apply join_comm; auto.
  - intros ????? (Hj1a & Hj1b & Hi1) (Hj2a & Hj2b & Hi2).
    eapply join_assoc in Hj2a; eauto.
    eapply join_assoc in Hj2b; eauto.
    destruct Hj2a as (c'a & (? & Hj2a) & (? & Hj3a)), Hj2b as (c'b & Hj2b & Hj3b).
    exists (c'a, c'b); repeat split; auto; simpl; intros.
    destruct Hj3b as [(? & ->) | (-> & ?)]; auto.
    destruct (snd e) eqn: He; auto.
    repeat intro; apply Hi2.
    rewrite <- Hj3a, in_app; auto.
Defined.

Lemma hist_add : forall (h : hist_part) h' e p,
  view_shift (ghost (h, Some h') p) (ghost (h ++ [(length h', e)], Some (h' ++ [e])) p).
Proof.
  intros; apply ghost_update.
  intros (?, ?) (? & (Hdisj & Hperm) & [(<- & ?) | (? & ?)] & Hh'); try discriminate; simpl in *; subst.
  exists (h ++ h0 ++ [(length h', e)], Some (h' ++ [e])); repeat split; simpl; auto.
  - intros ?? Hin ?.
    rewrite in_app in Hin; destruct Hin as [? | [X | ?]]; [eapply Hdisj; eauto | inv X | contradiction].
    intro; specialize (Hh' (length h') e'); exploit Hh'.
    { rewrite <- Hperm, in_app; auto. }
    intro Hnth; eapply lt_irrefl.
    rewrite <- nth_error_Some, Hnth; discriminate.
  - rewrite <- app_assoc; apply Permutation_app_head, Permutation_app_comm.
  - intros ?? Hin; rewrite app_assoc, in_app in Hin.
    destruct Hin as [Hin | [X | ?]]; [| inv X | contradiction].
    + rewrite Hperm in Hin; specialize (Hh' _ _ Hin).
      rewrite nth_error_app1; auto.
      rewrite <- nth_error_Some, Hh'; discriminate.
    + rewrite nth_error_app2, minus_diag; auto.
Qed.

Lemma hist_sep_join : forall (h1 : hist_part) (h2 : list hist_el), hist_incl h1 h2 ->
  join (h1, None) ([], Some h2) (h1, Some h2).
Proof.
  intros; repeat split; simpl; auto.
  rewrite app_nil_r; auto.
Qed.

End GHist.

Section AEHist.

(* These histories should be usable for any atomically accessed location. *)
Inductive AE_hist_el := AE (r : val) (w : val).

Fixpoint apply_hist a h :=
  match h with
  | [] => Some a
  | AE r w :: h' => if eq_dec r a then apply_hist w h' else None
  end.

Arguments eq_dec _ _ _ _ : simpl never.

Lemma apply_hist_app : forall h1 i h2, apply_hist i (h1 ++ h2) =
  match apply_hist i h1 with Some v => apply_hist v h2 | None => None end.
Proof.
  induction h1; auto; simpl; intros.
  destruct a.
  destruct (eq_dec r i); auto.
Qed.

Definition AE_hist := hist_part AE_hist_el.

End AEHist.

End Ghost.

Hint Resolve disjoint_nil.
Hint Resolve ghost_var_precise ghost_var_precise'.
