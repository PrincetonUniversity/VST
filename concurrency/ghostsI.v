Require Import VST.veric.compcert_rmaps.
Require Export VST.concurrency.ghosts.
Require Import VST.concurrency.conclib.
Require Import VST.veric.bi.
Require Import VST.msl.sepalg.
Import List.

(* Lemmas about ghost state, proved with Iris bupd *)

Instance unfash_persistent P : Persistent (alg_seplog.unfash P).
Proof.
  change unfash with (@subtypes.unfash rmap _ _).
  constructor; intros ??; hnf.
  unfold bi_persistently; simpl.
  unfold unfash in *; simpl in *.
  rewrite level_core; auto.
Qed.

Section ghost.

Context {RA: Ghost}.

Lemma own_alloc_strong : forall P (a : G) (pp : preds), ghost_seplog.pred_infinite P -> valid a ->
  emp |-- (|==> EX g : own.gname, !!(P g) && own g a pp)%I.
Proof.
  exact own_alloc_strong.
Qed.

Lemma own_alloc : forall (a : G) (pp : preds), valid a -> emp%I |-- (|==> EX g : own.gname, own g a pp)%I.
Proof.
  exact own_alloc.
Qed.

Global Instance own_dealloc g a pp : Affine (own g a pp).
Proof.
  unfold Affine.
  apply own_dealloc.
Qed.

Lemma own_update : forall g a b pp, fp_update a b -> own g a pp |-- (|==> own g b pp)%I.
Proof.
  exact own_update.
Qed.

Lemma own_update_ND : forall g a B pp, fp_update_ND a B -> own g a pp |-- (|==> EX b : G, !! B b && own g b pp)%I.
Proof.
  exact own_update_ND.
Qed.

Lemma own_list_alloc : forall la lp, Forall valid la -> length lp = length la ->
  emp |-- (|==> (EX lg : _, !!(Zlength lg = Zlength la) &&
    iter_sepcon (fun '(g, a, p) => own g a p) (combine (combine lg la) lp)))%I.
Proof.
  exact own_list_alloc.
Qed.

Corollary own_list_alloc' : forall a pp i, 0 <= i -> valid a ->
  emp |-- (|==> (EX lg : _, !!(Zlength lg = i) && iter_sepcon (fun g => own g a pp) lg))%I.
Proof.
  exact own_list_alloc'.
Qed.

Lemma own_list_dealloc : forall {A} f (l : list A),
  (forall b, exists g a pp, f b |-- own g a pp) ->
  iter_sepcon f l |-- (emp)%I.
Proof.
  intros; apply own_list_dealloc; auto.
Qed.

Lemma own_list_dealloc' : forall {A} g a p (l : list A),
  iter_sepcon (fun x => own (g x) (a x) (p x)) l |-- (emp)%I.
Proof.
  intros; apply own_list_dealloc'.
Qed.

Lemma core_persistent : forall g a p, a = core a -> Persistent (own g a p).
Proof.
  intros; unfold Persistent.
  constructor.
  intros ??; unfold bi_persistently; simpl.
  apply own.own_core; auto.
Qed.

End ghost.

Lemma exclusive_update : forall {A} (v v' : A) p, excl p v |-- (|==> excl p v')%I.
Proof.
  intros; apply exclusive_update.
Qed.

Section Snapshot.

Context `{ORD : PCM_order}.

Lemma master_update : forall v v' p, ord v v' -> ghost_master Tsh v p |-- (|==> ghost_master Tsh v' p)%I.
Proof.
  exact master_update.
Qed.

Lemma make_snap : forall (sh : share) v p, ghost_master sh v p |-- (|==> ghost_snap v p * ghost_master sh v p)%I.
Proof.
  exact make_snap.
Qed.

Lemma ghost_snap_forget : forall v1 v2 p, ord v1 v2 -> ghost_snap v2 p |-- (|==> ghost_snap v1 p)%I.
Proof.
  exact ghost_snap_forget.
Qed.

Lemma ghost_snap_choose : forall v1 v2 p, ghost_snap v1 p * ghost_snap v2 p |-- (|==> ghost_snap v1 p)%I.
Proof.
  exact ghost_snap_choose.
Qed.

Lemma snap_master_update1 : forall v1 v2 p v', ord v2 v' ->
  ghost_snap v1 p * ghost_master1 v2 p |-- (|==> ghost_snap v' p * ghost_master1 v' p)%I.
Proof.
  exact snap_master_update1.
Qed.

Global Instance snap_persistent v p : Persistent (ghost_snap v p).
Proof.
  apply core_persistent; auto.
Qed.

End Snapshot.

Section Reference.

Context {P : Ghost}.

Lemma part_ref_update : forall g sh a r a' r' pp
  (Ha' : forall b, join a b r -> join a' b r' /\ (a = r -> a' = r')),
  own(RA := ref_PCM P) g (Some (sh, a), Some r) pp |-- (|==>
  own(RA := ref_PCM P) g (Some (sh, a'), Some r') pp)%I.
Proof.
  exact part_ref_update.
Qed.

Lemma ref_add : forall g sh a r b a' r' pp
  (Ha : join a b a') (Hr : join r b r'),
  own(RA := ref_PCM P) g (Some (sh, a), Some r) pp |-- (|==>
  own(RA := ref_PCM P) g (Some (sh, a'), Some r') pp)%I.
Proof.
  exact ref_add.
Qed.

End Reference.

Section GVar.

Context {A : Type}.

Notation ghost_var := (@ghost_var A).

Lemma ghost_var_update : forall v p v', ghost_var Tsh v p |-- (|==> ghost_var Tsh v' p)%I.
Proof.
  exact ghost_var_update.
Qed.

End GVar.

Section PVar.

Lemma snap_master_update' : forall (v1 v2 : nat) p v', (v2 <= v')%nat ->
  ghost_snap v1 p * ghost_master1 v2 p |-- (|==> ghost_snap v' p * ghost_master1 v' p)%I.
Proof.
  intros; apply snap_master_update1; auto.
Qed.

End PVar.

Section Reference.

Context {P : Ghost}.

Lemma ref_update : forall g a r a',
  ghost_part_ref Tsh a r g |-- (|==> ghost_part_ref Tsh a' a' g)%I.
Proof.
  exact ref_update.
Qed.

End Reference.

Section GHist.

(* Ghost histories in the style of Nanevsky *)
Context {hist_el : Type}.

Notation hist_part := (nat -> option hist_el).

Lemma hist_add : forall (sh : share) (h h' : hist_part) e p t' (Hfresh : h' t' = None),
  ghost_hist_ref sh h h' p |-- (|==> ghost_hist_ref sh (map_upd h t' e) (map_upd h' t' e) p)%I.
Proof.
  exact hist_add.
Qed.

Notation ghost_hist := (@ghost_hist hist_el).

Lemma hist_add' : forall sh h h' e p, sh <> Share.bot ->
  ghost_hist sh h p * ghost_ref h' p |-- (|==>
  ghost_hist sh (map_upd h (length h') e) p * ghost_ref (h' ++ [e]) p)%I.
Proof.
  exact hist_add'.
Qed.

End GHist.

(* speed up destructs of the form [% H] *)
#[(*export, after Coq 8.13*)global] Existing Instance class_instances.into_sep_and_persistent_l.
