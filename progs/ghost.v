(* This probably doesn't belong in progs. Talk to Santiago about where it should go. *)
Require Import floyd.proofauto.
Require Export msl.predicates_sl.

Class PCM (A : Type) :=
  { join : A -> A -> A -> Prop; (*initial : A -> Prop;*)
    join_comm : forall a b c, join a b c -> join b a c;
    join_assoc : forall a b c d e, join a b c -> join c d e ->
                 exists c', join b d c' /\ join a c' e }.
Section Ghost.

Context {CS : compspecs} {Espec : OracleKind}.

Section PCM.

Context `{M : PCM}.

(* This is an overapproximation of IRIS's concept of view shift. *)
Definition view_shift A B := forall D P Q R C P',
  semax D (PROPx P (LOCALx Q (SEPx (B :: R)))) C P' ->
  semax D (PROPx P (LOCALx Q (SEPx (A :: R)))) C P'.

Definition joins a b := exists c, join a b c.

Definition update a b := forall c, joins a c -> joins b c.

(* General PCM-based ghost state *)
Parameter ghost : forall (g : A) (p : val), mpred.

(*Axiom new_ghost : forall t v p (g : A), initial g ->
  view_shift (data_at Tsh t v p) (ghost Tsh g p * data_at Tsh t v p).*)

Axiom ghost_join : forall g1 g2 g p, join g1 g2 g -> ghost g1 p * ghost g2 p = ghost g p.
Axiom ghost_conflict : forall g1 g2 p, ghost g1 p * ghost g2 p |-- !!joins g1 g2.
Axiom ghost_update : forall g g' p, update g g' -> view_shift (ghost g p) (ghost g' p).

End PCM.

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

Global Instance Share_PCM : PCM share := { join := sepalg.join }.
Proof.
  - intros; apply sepalg.join_comm; auto.
  - intros ?????? Hj2; eapply sepalg.join_assoc in Hj2; eauto.
    destruct Hj2; eauto.
Defined.

Global Instance Val_PCM : PCM (sigT reptype) := { join a b c := a = b /\ b = c(*; initial a := True*) }.
Proof.
  - intros ??? (? & ?); subst; auto.
  - intros ????? (? & ?) (? & ?); subst; eauto.
Defined.

Definition ghost_var (sh : share) t v p := ghost (sh, existT reptype t v) p.

Lemma ghost_var_inj : forall sh1 sh2 t v1 v2 p,
  ghost_var sh1 t v1 p * ghost_var sh2 t v2 p |-- !!(v1 = v2).
Proof.
  intros.
  eapply derives_trans; [apply ghost_conflict|].
  apply prop_left; intros (? & ? & ? & ?); apply prop_right.
  apply Eqdep.EqdepTheory.inj_pair2; auto.
Qed.

Axiom ghost_var_precise : forall sh t p, precise (EX v : reptype t, ghost_var sh t v p).

End GVar.

Section GHist.

(* Ghost histories in the style of Nanevsky *)
Variables data hist_el : Type.

Definition hist := nat -> option hist_el.
Definition empty_hist : hist := fun _ => None.

(* We want to split a history into two parts: a reference part that is always complete,
   and a splittable part that can be shared among clients. *)
Instance reference_PCM : PCM hist := { join a b c := a = c /\ b = empty_hist \/ b = c /\ a = empty_hist }.
Proof.
  - intros ??? [(? & ?) | (? & ?)]; subst; auto.
  - intros ????? [(? & ?) | (? & ?)] [(? & ?) | (? & ?)]; subst; eexists; split; eauto.
Defined.

Instance map_PCM : PCM hist := { join a b c :=
  forall x, match a x with Some y => b x = None /\ c x = Some y | None => c x = b x end }.
Proof.
  - intros.
    specialize (H x).
    destruct (a x), (b x); auto; destruct H; auto; discriminate.
  - intros ????? Hc He.
    exists (fun x => match b x with Some y => Some y | None => d x end).
    split; intro; specialize (Hc x); specialize (He x); destruct (a x), (b x), (c x);
      repeat match goal with H : _ /\ _ |- _ => destruct H end;
      repeat match goal with H : Some _ = Some _ |- _ => inv H end; auto; discriminate.
Defined.

Global Instance hist_PCM : PCM (hist * hist) := { join a b c := @join _ map_PCM (fst a) (fst b) (fst c) /\
  @join _ reference_PCM (snd a) (snd b) (snd c) /\
  (snd c = empty_hist \/ forall x y, (fst c) x = Some y -> (snd c) x = Some y) }.
Proof.
  - intros ??? (? & ? & ?).
    split; [|split; auto]; apply join_comm; auto.
  - intros ????? (Hj1a & Hj1b & Hi1) (Hj2a & Hj2b & Hi2).
    eapply join_assoc in Hj2a; eauto.
    eapply join_assoc in Hj2b; eauto.
    destruct Hj2a as (c'a & Hj2a & Hj3a), Hj2b as (c'b & Hj2b & Hj3b).
    exists (c'a, c'b); repeat split; auto; simpl; intros.
    destruct Hj3b as [(? & ->) | (-> & ?)]; auto.
    destruct Hi2 as [|He]; auto.
    destruct Hj2b as [(Hb & ?) | (Hd & ?)].
    + rewrite <- Hb; destruct Hj1b as [(? & ->) | (? & ?)]; auto.
      replace (snd c) with (snd b) in Hi1; auto.
      destruct Hi1 as [-> | Hc]; auto.
      right; intros.
      specialize (Hj1a x); specialize (Hj2a x); specialize (Hj3a x).
      destruct (fst a x); [destruct Hj3a as (Hc' & ?); rewrite Hc' in *; discriminate|].
      replace (snd b) with (snd e); apply He; rewrite Hj3a; auto.
    + right; intros.
      specialize (Hj2a x); specialize (Hj3a x).
      destruct (fst a x); [destruct Hj3a as (Hc' & ?); rewrite Hc' in *; discriminate|].
      apply He; rewrite <- Hj3a in *; auto.
Defined.

(* Timestamped ops instead of inner share? *)
(* How should histories combine? Do we need a VerCors-style process algebra? *)
(* We can have histories split and combine normally now, but as long as the RHS (lock part)
   doesn't split, it should know that it has a complete history. *)

Axiom ghost_inj' : forall sh i p h1 h2 r1 r2 r
  (Hp1 : predicates_hered.app_pred (ghost sh i (Tsh, h1) p) r1)
  (Hp1 : predicates_hered.app_pred (ghost sh i (Tsh, h2) p) r2)
  (Hr1 : sepalg.join_sub r1 r) (Hr2 : sepalg.join_sub r2 r),
  r1 = r2 /\ h1 = h2.

Axiom ghost_share_join : forall sh1 sh2 i sh h1 h2 p, sepalg.join sh1 sh2 Tsh -> list_incl h1 h2 ->
  ghost sh1 i (sh, h1) p * ghost sh2 i (Tsh, h2) p = ghost Tsh i (Tsh, h2) p.
Axiom hist_share_join : forall sh sh1 sh2 i sh' h1 h2 p, sepalg.join sh1 sh2 sh' ->
  ghost i sh (sh1, h1) p * ghost i sh (sh2, h2) p = EX h' : hist, !!(interleave [h1; h2] h') && ghost i sh (sh', h') p.
Axiom hist_add : forall i h e p, apply_hist i (e :: h) <> None ->
  view_shift (ghost Tsh i (Tsh, h) p) (ghost Tsh i (Tsh, e :: h) p).
Axiom ghost_inj : forall sh1 sh2 i sh h1 h2 p, ghost sh1 i (sh, h1) p * ghost sh2 i (Tsh, h2) p
  |-- !!(list_incl h1 h2).
Axiom ghost_inj_Tsh : forall sh1 sh2 i h1 h2 p, ghost sh1 i (Tsh, h1) p * ghost sh2 i (Tsh, h2) p
  |-- !!(h1 = h2).
(* Should this be an axiom? *)
Axiom ghost_feasible : forall sh i h p, ghost sh i (Tsh, h) p |-- !!(apply_hist i h <> None).

End GHist.

Section AEHist.

(* These histories should be usable for any atomically accessed location. *)
Inductive hist_el := AE (r : val) (w : val).

Fixpoint apply_hist a h :=
  match h with
  | [] => Some a
  | AE r w :: h' => match apply_hist a h' with Some a' => if eq_dec a' r then Some w else None | _ => None end
  end.

End AEHist.

End Ghost.