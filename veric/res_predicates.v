From iris.proofmode Require Export tactics.
Require Import compcert.cfrontend.Ctypes.
From iris_ora.algebra Require Import gmap.
From iris_ora.logic Require Export logic.
From VST.veric Require Import shares address_conflict.
From VST.msl Require Export shares.
From VST.veric Require Export base Memory algebras dshare gen_heap invariants.
Export Values.
Export -(notations) Maps.

(* We can't import compcert.lib.Maps' notations because they conflict with stdpp's,
   and actually the ! notation conflicts with rewrite's ! as well. Matching stdpp's lookup notation
   instead, with an extra ! per lookup. *)
Declare Scope maps.
Delimit Scope maps with maps.
Notation "a !! b" := (Maps.PTree.get b a) (at level 20) : maps.
Notation "a !!! b" := (Maps.PMap.get b a) (at level 20) : maps.
Open Scope maps.
Local Open Scope Z_scope.

Inductive resource :=
| VAL (v : memval)
| LK (i z : Z)
| FUN.
(* Other information, like lock invariants and funspecs, should be stored in invariants,
   not in the heap. *)

Definition nonlock (r: resource) : Prop :=
 match r with
 | LK _ _ => False
 | _ => True
 end.

Global Notation "l ↦ dq v" := (mapsto l dq v)
  (at level 20, dq custom dfrac at level 1, format "l  ↦ dq  v") : bi_scope.
Global Notation "l ↦p v" := (mapsto_pure l v)
  (at level 20, format "l  ↦p  v") : bi_scope.

Open Scope bi_scope.

Section heap.

Context {Σ : gFunctors}.
Context {HGS : gen_heapGS address resource Σ} {WGS : wsatGS Σ}.

Notation mpred := (iProp Σ).

Definition spec : Type :=  forall (sh: share) (l: address), mpred.

Ltac do_map_arg :=
match goal with |- ?a = ?b =>
  match a with context [map ?x _] =>
    match b with context [map ?y _] => replace y with x; auto end end end.

(*Lemma nonlock_join: forall r1 r2 r,
  nonlock r1 ->
  nonlock r2 ->
  join r1 r2 r ->
  nonlock r.
Proof.
  intros.
  destruct r1, r2; inv H1; auto.
Qed.*)

Definition nonlockat (l: address): mpred := ∀ dq r, l ↦{dq} r → ⌜nonlock r⌝.

Definition shareat (l: address) (sh: share): mpred :=
  if readable_share_dec sh then (∃r, l ↦{#sh} r)%I else mapsto_no l sh.

(*Lemma yesat_join_diff:
  forall pp pp' k k' sh sh' l w, k <> k' -> 
                  yesat pp k sh l w -> yesat pp' k' sh' l w -> False.
Proof.
unfold yesat, yesat_raw; intros.
destruct H0 as [p ?]. destruct H1 as [p' ?].
simpl in *; inversion2 H0 H1.
contradiction H; auto.
Qed.

Lemma yesat_raw_join:
  forall pp k (sh1 sh2 sh3: Share.t) rsh1 rsh2 rsh3 l phi1 phi2 phi3,
   join sh1 sh2 sh3 ->
   yesat_raw pp k sh1 rsh1 l phi1 ->
   yesat_raw pp k sh2 rsh2 l phi2 ->
   join phi1 phi2 phi3 ->
   yesat_raw pp k sh3 rsh3 l phi3.
Proof.
unfold yesat_raw;
intros until 1; rename H into HR; intros.
simpl in H,H0|-*.
assert (level phi2 = level phi3) by (apply join_level in H1; intuition).
rewrite H2 in *; clear H2.
assert (level phi1 = level phi3) by  (apply join_level in H1; intuition).
rewrite H2 in *; clear H2.
generalize (resource_at_join _ _ _ l H1); clear H1.
revert H H0.
case_eq (phi1 @ l); intros; try discriminate.
inv H0.
revert H1 H2; case_eq (phi2 @ l); intros; try discriminate.
inv H1.
inv H2.
inv H0.
pose proof (join_eq HR RJ). subst sh5. clear RJ.
repeat proof_irr. auto.
Qed.

Lemma nonunit_join: forall A {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{CA: Disj_alg A} (x y z: A),
  nonunit x -> join x y z -> nonunit z.
Proof.
intros.
intro; intro.
apply unit_identity in H1.
apply split_identity in H0; auto.
apply nonunit_nonidentity in H.
contradiction.
Qed.

Lemma yesat_join:
  forall pp k sh1 sh2 sh3 l m1 m2 m3,
   join sh1 sh2 sh3 ->   
   yesat pp k sh1 l m1 ->
   yesat pp k sh2 l m2 ->
   join m1 m2 m3 ->
   yesat pp k sh3 l m3.
Proof.
intros.
destruct H0 as [p1 ?].
destruct H1 as [p2 ?].
assert (p3: readable_share sh3).
eapply join_readable1; eauto.
exists p3.
eapply yesat_raw_join with (phi1 := m1); eauto.
Qed.

Definition spec_parametric (Q: address -> spec) : Prop :=
   forall l l', exists pp, exists ok,
             forall sh m,
           Q l sh l' m = 
            (exists p, exists k, ok k /\ m @ l' = 
                 YES sh p k (preds_fmap (approx (level m)) (approx (level m)) pp)).

Lemma YES_ext:
  forall sh sh' rsh rsh' k p, sh=sh' -> YES sh rsh k p = YES sh' rsh' k p.
Proof.
intros. subst. f_equal. apply proof_irr.
Qed.*)

(****** Specific specs  ****************)

Definition VALspec : spec :=
       fun (sh: share) (l: address) => ∃v, l ↦{#sh} VAL v.

Definition VALspec_range (n: Z) : spec :=
     fun (sh: Share.t) (l: address) => [∗ list] i ∈ seq 0 (Z.to_nat n), VALspec sh (adr_add l (Z.of_nat i)).

Definition nonlock_permission_bytes (sh: share) (a: address) (n: Z) : mpred :=
  [∗ list] i ∈ seq 0 (Z.to_nat n), if readable_share_dec sh then ∃ r, ⌜nonlock r⌝ ∧ adr_add a (Z.of_nat i) ↦{#sh} r
                                   else mapsto_no (adr_add a (Z.of_nat i)) sh.

Definition nthbyte (n: Z) (l: list memval) : memval :=
     nth (Z.to_nat n) l Undef.

Definition address_mapsto (ch: memory_chunk) (v: val) : spec :=
        fun (sh: Share.t) (l: address) =>
           ∃ bl: list memval, 
               ⌜length bl = size_chunk_nat ch  /\ decode_val ch bl = v /\ (align_chunk ch | snd l)⌝ ∧
               [∗ list] i↦b ∈ bl, adr_add l (Z.of_nat i) ↦{#sh} (VAL b).

Lemma add_and : forall {PROP : bi} (P Q : PROP), (P ⊢ Q) -> (P ⊢ P ∧ Q).
Proof.
  auto.
Qed.

Lemma address_mapsto_align: forall ch v sh l,
  address_mapsto ch v sh l ⊣⊢ address_mapsto ch v sh l ∧ ⌜(align_chunk ch | snd l)⌝.
Proof.
  intros.
  iSplit.
  - iApply add_and.
    unfold address_mapsto.
    by iIntros "H"; iDestruct "H" as (bl) "((% & % & %) & ?)".
  - by iIntros "[? _]".
Qed.

(*Lemma mapsto_fun: forall l sh sh' v v', mapsto l sh v ∧ mapsto l sh' v' ⊢ ⌜v=v'⌝.
Proof.
  intros; unfold mapsto.
  iIntros "?".
  iApply ghost_map_elem_agree.
  Search ghost_map_elem.

Lemma address_mapsto_fun:
  forall ch sh sh' l v v',
          (address_mapsto ch v sh l ∗ True) ∧ (address_mapsto ch v' sh' l ∗ True) ⊢ ⌜v=v'⌝.
Proof.
intros.
iIntros "[H1 ?]".
intros m [? ?]. unfold prop.
destruct H as [m1 [m2 [J [[bl [[Hlen [? _]] ?]] _]]]].
destruct H0 as [m1' [m2' [J' [[bl' [[Hlen' [? _]] ?]] _]]]].
subst.
assert (forall i, nth_error bl i = nth_error bl' i).
intro i; specialize(H1 (fst l, snd l + Z_of_nat i)); specialize( H2 (fst l, snd l + Z_of_nat i)).
unfold jam in *.
destruct l as [b z].
simpl in *.
if_tac in H1.
destruct H as [_ ?].
replace (z + Z_of_nat i - z) with (Z_of_nat i) in * by lia.
assert ((i < length bl)%nat).
rewrite Hlen.
rewrite size_chunk_conv in H.
lia.
rewrite <- Hlen' in Hlen.
rewrite Nat2Z.id in *.
destruct H1; destruct H2.
unfold yesat_raw in *.
repeat rewrite preds_fmap_NoneP in *.
assert (H5: nth i bl Undef = nth i bl' Undef).
apply (resource_at_join _ _ _ (b,z + Z_of_nat i)) in J.
apply (resource_at_join _ _ _ (b,z + Z_of_nat i)) in J'.
rewrite H1 in J; rewrite H2 in J'; clear H1 H2.
inv J; inv J'; try congruence.
clear - Hlen H0 H5.
revert bl bl' Hlen H0 H5; induction i; destruct bl; destruct bl'; simpl; intros; auto; try lia.
apply IHi; auto.
lia.
assert (~ (i < length bl)%nat).
contradict H.
split; auto.
rewrite Hlen in H.
rewrite size_chunk_conv.
lia.
assert (i >= length bl)%nat by lia.
destruct (nth_error_length i bl).
rewrite H5; auto.
destruct (nth_error_length i bl').
rewrite H7; auto.
lia.
clear - H.
assert (bl=bl'); [| subst; auto].
revert bl' H; induction bl; destruct bl'; intros; auto.
specialize (H 0%nat); simpl in H. inv H.
specialize (H 0%nat); simpl in H. inv H.
f_equal.
specialize (H 0%nat); simpl in H. inv H. auto.
apply IHbl.
intro.
specialize( H (S i)).
simpl in H.
auto.
simpl; auto.
Qed.*)

(* Read-only locations can't be deallocated, but might be appropriate for e.g. global variables. *)
Definition address_mapsto_readonly (ch: memory_chunk) (v: val) :=
        fun (l: address) =>
           ∃ bl: list memval, 
               ⌜length bl = size_chunk_nat ch  /\ decode_val ch bl = v /\ (align_chunk ch | snd l)⌝ ∧
               [∗ list] i↦b ∈ bl, adr_add l (Z.of_nat i) ↦□ (VAL b).

Definition LKN := nroot .@ "LK".

Definition LKspec lock_size (R: mpred) : spec :=
   fun (sh: Share.t) (l: address) =>
    [∗ list] i ∈ seq 0 (Z.to_nat lock_size), adr_add l (Z.of_nat i) ↦{#sh} LK lock_size (Z.of_nat i) ∗
      inv (LKN .@ l) R.

Definition Trueat (l: address) : mpred := True.

(*Lemma address_mapsto_old_parametric: forall ch v, 
   spec_parametric (fun l sh l' => yesat NoneP (VAL (nthbyte (snd l' - snd l) (encode_val ch v))) sh l').
Proof.
intros.
exists NoneP. exists (fun k => k= VAL (nthbyte (snd l' - snd l) (encode_val ch v))).
intros.
unfold yesat.
apply exists_ext; intro p.
unfold yesat_raw.
simpl.
apply prop_ext; split; intros.
econstructor; split; [reflexivity | ].
rewrite H; f_equal.

simpl.
eauto.
destruct H as [k [? ?]].
subst; auto.
Qed.

Lemma VALspec_parametric: 
  spec_parametric (fun l sh l' => ∃ v: memval,  yesat NoneP (VAL v) sh l').
Proof.
intros.
exists NoneP.
exists (fun k => exists v, k=VAL v).
intros.
unfold yesat.
apply prop_ext; split; intros.
destruct H as [v [p ?]].
exists p.
exists (VAL v).
split; eauto.
destruct H as [p [k [[v ?] ?]]].
subst.
exists v.
exists p.
auto.
Qed.

Lemma LKspec_parametric lock_size: forall R: iProp Σ,
  spec_parametric (fun l sh l' => yesat (SomeP Mpred (fun _ => R)) (LK lock_size (snd l' - snd l)) sh l').
Proof.
intros.
unfold jam.
intro; intros.
simpl.
exists (SomeP Mpred (fun _ => R)).
exists (fun k => k = LK lock_size (snd l' - snd l)).
intros.
apply exists_ext; intro p.
apply prop_ext; split; intros.
rewrite H.
econstructor.  split; eauto.

destruct H as [k [? ?]].
subst; auto.
Qed.*)

Definition val2address (v: val) : option address := 
  match v with Vptr b ofs => Some (b, Ptrofs.signed ofs) | _ => None end.

(*Lemma VALspec_readable:
  forall l sh w,  (VALspec sh l * True) %pred w -> readable l w.
(* The converse is not quite true, because "readable" does constraint to NoneP *)
Proof.
unfold VALspec, readable;
intros.
destruct H as [w1 [w2 [? [? _]]]].
specialize (H0 l).
unfold jam in H0.
hnf in H0|-*; rewrite if_true in H0 by auto.
destruct H0 as [v [p ?]].
unfold yesat_raw in H0.
generalize (resource_at_join _ _ _ l H); rewrite H0; intro Hx.
inv Hx; auto.
Qed.*)


(* NOT TRUE, because of CompCert_AV.valid problems.
Lemma jam_con: forall A (S: A -> Prop) P Q,
     allp (jam S P Q) ⊢ allp (jam S P (fun _ => emp)) * (allp (jam S (fun _ => emp) Q)).
*)

Lemma address_mapsto_VALspec:
  forall ch v sh l i, 0 <= i < size_chunk ch ->
        address_mapsto ch v sh l ⊢ VALspec sh (adr_add l i) ∗ True.
Proof.
intros.
rewrite /address_mapsto /VALspec; iIntros "H".
iDestruct "H" as (bl) "[% H]".
rewrite bi.sep_exist_r.
iExists (nthbyte i bl).
rewrite size_chunk_conv in H.
rewrite big_sepL_lookup_acc.
rewrite -> (Z2Nat.id i) by tauto.
iDestruct "H" as "[$ $]".
{ rewrite /nthbyte nth_lookup.
  destruct (lookup_lt_is_Some_2 bl (Z.to_nat i)) as [? ->]; [lia | done]. }
Qed.

(*Lemma address_mapsto_exists:
  forall ch v sh (rsh: readable_share sh) loc w0
      (RESERVE: forall l', adr_range loc (size_chunk ch) l' -> w0 @ l' = NO Share.bot bot_unreadable),
      (align_chunk ch | snd loc) ->
      exists w, address_mapsto ch (decode_val ch (encode_val ch v)) sh loc w 
                    /\ core w = core w0.
Proof.
intros. rename H into Halign.
unfold address_mapsto.
pose (f l' := if adr_range_dec loc (size_chunk ch) l'
                     then YES sh rsh (VAL (nthbyte (snd l' - snd loc) (encode_val ch v))) NoneP
                     else core w0 @ l').
pose proof I.
destruct (make_rmap f (ghost_of w0) (level w0)) as [phi [? ?]].
extensionality l; unfold f, compose; simpl.
if_tac; simpl; auto.
rewrite <- level_core.
apply resource_at_approx.
{ apply ghost_of_approx. }
exists phi.
split.
+ exists (encode_val ch v).
  split.
  split; auto.
  apply encode_val_length.
  intro l'.
  unfold jam.
  hnf.
  unfold yesat, yesat_raw, noat.
  unfold app_pred, proj1_sig. destruct H1; rewrite H1; clear H H1.
  unfold f; clear f.
  if_tac.
  exists rsh.
  f_equal.
  rewrite <- core_resource_at.
  apply core_identity.
+ apply rmap_ext. do 2 rewrite level_core. auto.
  intro l; specialize (RESERVE l).
  rewrite <- core_resource_at. destruct H1. rewrite H1. unfold f.
  if_tac.
  rewrite core_YES.
  rewrite <- core_resource_at. rewrite RESERVE; auto.
  rewrite core_NO; auto.
  rewrite <- core_resource_at; rewrite core_idem; auto.
  { rewrite <- core_ghost_of.
    destruct H1 as [_ ->].
    rewrite core_ghost_of; auto. }
Qed.*)

(*  NOT TRUE, because readable doesn't constraint NoneP ...
Lemma readable_VAL:
 forall w l, readable l (w_m w) <-> exists sh, (VALspec sh l * True) w.

*)

Lemma VALspec1: forall sh l, VALspec_range 1 sh l ⊣⊢ VALspec sh l.
Proof.
unfold VALspec_range; intros; simpl.
rewrite right_id.
unfold adr_add; destruct l.
by rewrite Z.add_0_r.
Qed.

Lemma VALspec_range_exp_address_mapsto:
  forall ch sh l,
    (align_chunk ch | snd l) ->
    VALspec_range (size_chunk ch) sh l ⊢ ∃ v: val, address_mapsto ch v sh l.
Proof.
  intros.
  unfold VALspec_range, VALspec, address_mapsto.
  trans (∃ (bl : list memval), ⌜length bl = size_chunk_nat ch ∧ (align_chunk ch | l.2)⌝
   ∧ ([∗ list] i↦b ∈ bl, adr_add l (Z.of_nat i) ↦{#sh} (VAL b))).
  2: { iIntros "H"; iDestruct "H" as (bl [??]) "H"; iExists (decode_val ch bl), bl; auto. }
  rewrite size_chunk_conv Nat2Z.id.
  forget (size_chunk_nat ch) as n.
  induction n.
  - simpl; iIntros "_".
    by iExists nil; simpl.
  - rewrite seq_S big_sepL_app /=.
    iIntros "(H & Hv & _)".
    iDestruct "Hv" as (v) "Hv".
    iDestruct (IHn with "H") as (bl [??]) "H"; subst.
    iExists (bl ++ [v]); iSplit.
    { rewrite app_length /=; iPureIntro; split; auto; lia. }
    rewrite big_sepL_app /= Nat.add_0_r; iFrame.
Qed.

Lemma big_sepL_seq : forall {A} `{Inhabited A} l (f : nat -> A -> mpred),
  equiv ([∗ list] k↦y ∈ l, f k y) ([∗ list] i ∈ seq 0 (length l), f i (nth i l inhabitant)).
Proof.
  intros; remember (rev l) as l'; revert dependent l; induction l'; intros.
  { by destruct l; [|apply app_cons_not_nil in Heql']. }
  apply (f_equal (@rev _)) in Heql'; rewrite rev_involutive in Heql'; subst; simpl.
  rewrite app_length seq_app !big_opL_app IHl'; last by rewrite rev_involutive.
  simpl; rewrite nth_middle Nat.add_0_r.
  rewrite -(big_opL_ext (fun _ y => f y (nth y (rev l' ++ [a]) inhabitant))); first done.
  intros ??[-> ?]%lookup_seq.
  rewrite app_nth1 //.
Qed.

Global Instance memval_inhabited : Inhabited memval := { inhabitant := Undef }.

Lemma address_mapsto_VALspec_range:
  forall ch v sh l,
        address_mapsto ch v sh l ⊢ VALspec_range (size_chunk ch) sh l.
Proof.
intros.
unfold address_mapsto, VALspec_range.
iIntros "H"; iDestruct "H" as (bl (? & ? & ?)) "H".
rewrite size_chunk_conv Nat2Z.id -H big_sepL_seq.
iApply (big_sepL_mono with "H").
by intros; iIntros "?"; iExists _.
Qed.

(*
Lemma VALspec_range_bytes_readable:
  forall n sh loc m, VALspec_range n sh loc m -> bytes_readable loc n m.
Proof.
intros; intro; intros.
specialize (H (adr_add loc i)).
hnf in H.
rewrite if_true in H.
destruct H as [v [p ?]].
hnf in H.
red. red. red.
rewrite H; auto.
destruct loc; split; unfold adr_add; auto.
simpl. lia.
Qed.

Lemma VALspec_range_bytes_writable:
  forall n sh loc m, writable_share sh -> VALspec_range n sh loc m -> bytes_writable loc n m.
Proof.
intros; intro; intros.
specialize (H0 (adr_add loc i)).
hnf in H0.
rewrite if_true in H0.
destruct H0 as [v [p ?]].
hnf in H0.
do 3 red.
rewrite H0; auto with extensionality.
destruct loc; split; unfold adr_add; auto.
simpl. lia.
Qed.

Lemma yesat_join_sub:
  forall pp k l sh m m',
          join_sub m m' ->
          yesat pp k sh l m ->
         exists sh', yesat pp k sh' l m'.
Proof.
intros.
unfold yesat_raw in H0.
destruct H0.
generalize (resource_at_join_sub _ _ l H); rewrite H0; intro.
assert (level m = level m').
destruct H; apply join_level in H; intuition.
destruct H1.
destruct x0; case_eq (m' @ l); intros; rewrite H3 in H1; inv H1.
do 2 econstructor. unfold yesat_raw. simpl. rewrite <- H2.  eapply H3.
exists sh1.
unfold yesat. simpl.
exists r0.
rewrite <- H2. rewrite H3.
subst; f_equal; auto.
Qed.*)

(*Lemma emp_no : emp = (ALL l, noat l).
Proof.
  apply pred_ext.
  - intros ? (? & ? & Hord) ?; simpl.
    apply rmap_order in Hord as (_ & <- & _).
    apply resource_at_identity; auto.
  - intros ??; exists (id_core a); split; [apply id_core_identity|].
    rewrite rmap_order, id_core_level, id_core_resource, id_core_ghost.
    split; auto; split; [|eexists; constructor].
    extensionality l; specialize (H l).
    rewrite <- core_resource_at; symmetry; apply identity_core; auto.
Qed.*)

Lemma VALspec_range_0: forall sh loc, VALspec_range 0 sh loc ⊣⊢ emp.
Proof.
  done.
Qed.

Lemma nonlock_permission_bytes_0: forall sh a, nonlock_permission_bytes sh a 0 ⊣⊢ emp.
Proof.
  done.
Qed.

(*Lemma nonlock_permission_bytes_valid : forall sh a n, n > 0 -> nonlock_permission_bytes sh a n ⊢ ⌜✓ sh⌝.
Proof.
  intros; rewrite /nonlock_permission_bytes.
  destruct (Z.to_nat n) eqn: Hn; first lia.
  simpl; iIntros "H"; if_tac; first by iPureIntro; intros ->; contradiction bot_unreadable.
  by iDestruct "H" as "[H _]"; iDestruct (mapsto_no_valid with "H") as %[??].
Qed.*)

(*Lemma nonlock_permission_bytes_not_nonunit: forall p n,
  nonlock_permission_bytes Share.bot p n ⊢ emp.
Proof.
  intros.
  rewrite /nonlock_permission_bytes /shareat.
  assert (sh = Share.bot).
  {
    destruct (dec_share_identity sh).
    + apply identity_share_bot; auto.
    + apply nonidentity_nonunit in n0; tauto.
  }
  subst.
  intros ? ?. simpl in H0.
  rewrite emp_no; intros l; simpl.
  specialize (H0 l); if_tac in H0; auto.
  destruct H0 as [H0 _]; unfold resource_share in H0.
  destruct (a @ l); inv H0.
  + apply NO_identity. 
  + contradiction (bot_unreadable r).
Qed.

Lemma is_resource_pred_YES_VAL sh:
  is_resource_pred
    (fun l' => ∃  v: memval, yesat NoneP (VAL v) sh l')
    (fun r _ n => (exists b0 rsh, r = YES sh rsh (VAL b0)
        (SomeP (ConstType unit) (fun _ => tt)))).
Proof. hnf; intros. reflexivity. Qed.

Lemma is_resource_pred_YES_VAL' sh v:
  is_resource_pred
    (fun l' => yesat NoneP (VAL (v l')) sh l')
    (fun r l n => (exists rsh, r = YES sh rsh (VAL (v l))
        (SomeP (ConstType unit) (fun _ => tt)))).
Proof. hnf; intros. reflexivity. Qed.

Lemma is_resource_pred_nonlock_shareat sh:
  is_resource_pred
    (fun i : address => shareat i sh ∧ nonlockat i)
    (fun r _ _ => resource_share r = Some sh /\ nonlock r).
Proof. hnf; intros. reflexivity. Qed.*)

Lemma VALspec_range_split2:
  forall (n m r: Z) (sh: Share.t) (b: block) (ofs: Z),
    r = n + m -> n >= 0 -> m >= 0 ->
    VALspec_range r sh (b, ofs) ⊣⊢
    VALspec_range n sh (b, ofs) ∗ VALspec_range m sh (b, ofs + n).
Proof.
  intros; subst.
  unfold VALspec_range.
  rewrite -> Z2Nat.inj_add, seq_app by lia.
  rewrite big_sepL_app Nat.add_0_l.
  rewrite -{2}(Nat.add_0_r (Z.to_nat n)) -fmap_add_seq big_sepL_fmap.
  setoid_rewrite Nat2Z.inj_add; rewrite Z2Nat.id; last lia.
  unfold adr_add; simpl.
  by iSplit; iIntros "[$ H]"; iApply (big_sepL_mono with "H"); intros ???; rewrite Z.add_assoc.
Qed.

Lemma nonlock_permission_bytes_split2:
  forall (n m r: Z) (sh: Share.t) (b: block) (ofs: Z),
    r = n + m -> n >= 0 -> m >= 0 ->
    nonlock_permission_bytes sh (b, ofs) r ⊣⊢
    nonlock_permission_bytes sh (b, ofs) n ∗
    nonlock_permission_bytes sh (b, ofs + n) m.
Proof.
  intros; subst.
  unfold nonlock_permission_bytes.
  rewrite -> Z2Nat.inj_add, seq_app by lia.
  rewrite big_sepL_app Nat.add_0_l.
  rewrite -{2}(Nat.add_0_r (Z.to_nat n)) -fmap_add_seq big_sepL_fmap.
  unfold adr_add; simpl.
  by iSplit; iIntros "[$ H]"; iApply (big_sepL_mono with "H"); intros ???;
    rewrite ?Nat2Z.inj_add Z2Nat.id; try lia; rewrite Z.add_assoc.
Qed.

Lemma VALspec_range_VALspec:
  forall (n : Z) (v : val) (sh : Share.t) (l : address) (i : Z),
       0 <= i < n ->
       VALspec_range n sh l
       ⊢ VALspec sh (adr_add l i) ∗ True.
Proof.
  intros.
  unfold VALspec_range.
  rewrite (big_sepL_lookup_acc).
  rewrite -> (Z2Nat.id i) by tauto.
  by iIntros "[$ $]".
  { rewrite lookup_seq_lt; [done | lia]. }
Qed.

Lemma share_joins_self: forall sh: share, sepalg.joins sh sh -> sh = Share.bot.
Proof.
  intros ? [? ?%sepalg.join_self].
  by apply identity_share_bot.
Qed.

Lemma share_op_self: forall sh, (✓ (Share sh ⋅ Share sh))%stdpp -> sh = Share.bot.
Proof.
  intros ? (? & ? & ? & [=] & [=] & ? & J)%share_valid2_joins; subst.
  pose proof (identity_share_bot _ (sepalg.join_self J)) as ->.
  done.
Qed.

Lemma self_unreadable : forall sh, ~readable_dfrac (DfracOwn (Share sh) ⋅ DfracOwn (Share sh)).
Proof.
  intros; simpl.
  destruct (Share sh ⋅ Share sh) eqn: J; rewrite J; auto.
  apply share_op_join in J as (? & ? & [=] & [=] & J); subst.
  pose proof (identity_share_bot _ (sepalg.join_self J)) as ->.
  apply bot_identity in J as <-.
  apply bot_unreadable.
Qed.

Lemma VALspec_range_overlap': forall sh p1 p2 n1 n2,
  adr_range p1 n1 p2 ->
  n2 > 0 ->
  VALspec_range n1 sh p1 ∗ VALspec_range n2 sh p2 ⊢ False.
Proof.
  intros.
  iIntros "[H1 H2]".
  destruct p1 as (?, ofs1), p2 as (?, ofs2), H; subst.
  unfold VALspec_range.
  rewrite (big_sepL_lookup_acc _ _ _ (Z.to_nat (ofs2 - ofs1))).
  rewrite (big_sepL_lookup_acc _ (seq _ (Z.to_nat n2)) _ O).
  iDestruct "H1" as "[H1 _]"; iDestruct "H2" as "[H2 _]".
  unfold VALspec.
  iDestruct "H1" as (v1) "H1"; iDestruct "H2" as (v2) "H2".
  rewrite /adr_add /=.
  rewrite Z2Nat.id; last lia.
  rewrite Zplus_minus Z.add_0_r.
  iDestruct (mapsto_valid_2 with "H1 H2") as %(? & []%self_unreadable & _).
  { rewrite lookup_seq_lt; [done | lia]. }
  { rewrite lookup_seq_lt; [done | lia]. }
Qed.

Lemma address_mapsto_overlap':
  forall sh ch1 v1 ch2 v2 a1 a2,
     adr_range a1 (size_chunk ch1) a2 ->
     address_mapsto ch1 v1 sh a1 ∗ address_mapsto ch2 v2 sh a2 ⊢ False.
Proof.
  intros.
  etrans; last apply VALspec_range_overlap'.
  + apply bi.sep_mono; apply address_mapsto_VALspec_range.
  + auto.
  + apply size_chunk_pos.
Qed.

Lemma VALspec_range_overlap: forall sh l1 n1 l2 n2,
  range_overlap l1 n1 l2 n2 ->
  VALspec_range n1 sh l1 ∗ VALspec_range n2 sh l2 ⊢ False.
Proof.
  intros.
  pose proof range_overlap_non_zero _ _ _ _ H.
  apply range_overlap_spec in H; try tauto.
  destruct H.
  + apply VALspec_range_overlap'; tauto.
  + rewrite comm.
    apply VALspec_range_overlap'; tauto.
Qed.

Lemma address_mapsto_overlap: forall sh l1 ch1 v1 l2 ch2 v2,
  range_overlap l1 (size_chunk ch1) l2 (size_chunk ch2) ->
  address_mapsto ch1 v1 sh l1 ∗ address_mapsto ch2 v2 sh l2 ⊢ False.
Proof.
  intros.
  apply range_overlap_spec in H; try apply size_chunk_pos.
  destruct H.
  + apply address_mapsto_overlap'; auto.
  + rewrite comm.
    apply address_mapsto_overlap'; auto.
Qed.

Lemma nonlock_permission_bytes_overlap:
  forall sh n1 n2 p1 p2,
  sh ≠ Share.bot ->
  range_overlap p1 n1 p2 n2 ->
  nonlock_permission_bytes sh p1 n1 ∗ nonlock_permission_bytes sh p2 n2 ⊢ False.
Proof.
  intros ?????? ((?, ?) & Hadr1 & Hadr2).
  destruct p1 as (?, ofs1), p2 as (?, ofs2), Hadr1, Hadr2; subst.
  iIntros "[H1 H2]".
  unfold nonlock_permission_bytes.
  rewrite (big_sepL_lookup_acc _ _ _ (Z.to_nat (z - ofs1))).
  rewrite (big_sepL_lookup_acc _ (seq _ (Z.to_nat n2)) _ (Z.to_nat (z - ofs2))).
  iDestruct "H1" as "[H1 _]"; iDestruct "H2" as "[H2 _]".
  destruct (readable_share_dec _).
  - iDestruct "H1" as "(% & % & H1)"; iDestruct "H2" as "(% & % & H2)".
    rewrite /adr_add /=.
    rewrite !Z2Nat.id; try lia.
    rewrite !Zplus_minus.
    iDestruct (mapsto_valid_2 with "H1 H2") as %(? & []%self_unreadable & ?).
  - rewrite /adr_add /=.
    rewrite !Z2Nat.id; try lia.
    rewrite !Zplus_minus.
    iDestruct (mapsto_no_valid_2 with "H1 H2") as %[?%share_op_self ?]; done.
  - rewrite lookup_seq_lt; [done | lia].
  - rewrite lookup_seq_lt; [done | lia].
Qed.

(*Lemma address_mapsto_value_cohere':
  forall ch v1 v2 sh1 sh2 a r
 (Hmaps1 : address_mapsto ch v1 sh1 a r)
 (Hmaps2 : address_mapsto ch v2 sh2 a r), v1=v2.
Proof.
 intros.
 destruct Hmaps1 as [b1 [[Hlen1 [? ?]] Hall1]].
 destruct Hmaps2 as [b2 [[Hlen2 [? ?]] Hall2]].
 assert (b1 = b2); [ | subst; auto].
 clear - Hlen1 Hlen2 Hall1 Hall2.
 rewrite size_chunk_conv in *.
 forget (size_chunk_nat ch) as n. clear ch.
 assert (forall i, nth_error b1 i = nth_error b2 i).
 intro.
 destruct a as [b z].
 specialize (Hall1 (b, (z+Z.of_nat i))).
 specialize (Hall2 (b, (z+Z.of_nat i))).
 hnf in Hall1,Hall2. if_tac in Hall1. destruct H as [_ [_ ?]].
 destruct Hall1 as (? & Hall1), Hall2 as (? & Hall2). simpl in Hall1, Hall2.
 rewrite Hall1 in Hall2; inversion Hall2.
 replace (z + Z.of_nat i - z) with (Z.of_nat i) in H2 by lia.
 rewrite Nat2Z.id in H2.
 rewrite coqlib4.nth_error_nth with (z:=Undef) by lia.
 rewrite coqlib4.nth_error_nth with (z:=Undef) by lia.
 f_equal; auto.
 assert (~(i<n)%nat).
 contradict H. split; auto. lia.
 transitivity (@None memval); [ | symmetry];
 apply nth_error_length; lia.
 clear - H Hlen1 Hlen2.
 revert b1 b2 Hlen1 Hlen2 H.
 induction n; destruct b1,b2; intros; auto; inv Hlen1; inv Hlen2.
 f_equal.
 specialize (H O). simpl in H. inv H; auto.
 apply IHn; auto.
 intro i; specialize (H (S i)); apply H.
Qed.*)

Lemma mapsto_value_cohere: forall l sh1 sh2 r1 r2, mapsto l sh1 r1 ∗ mapsto l sh2 r2 ⊢ ⌜r1 = r2⌝.
Proof.
  intros; iIntros "[H1 H2]".
  by iDestruct (mapsto_valid_2 with "H1 H2") as %[? Heq]; inversion Heq.
Qed.

Lemma list_snoc : forall {A} (l : list A), length l <> O -> exists l1 a, l = l1 ++ [a].
Proof.
  induction l; first done.
  destruct l.
  - exists nil; eauto.
  - destruct IHl as (? & ? & ->); first done.
    exists (a :: x); eauto.
Qed.

Lemma mapsto_list_value_cohere: forall a sh1 sh2 b1 b2 (Hlen: length b1 = length b2),
  (([∗ list] i↦b ∈ b1, mapsto (adr_add a (Z.of_nat i)) sh1 (VAL b)) ∗
    [∗ list] i↦b ∈ b2, mapsto (adr_add a (Z.of_nat i)) sh2 (VAL b)) ⊢
  ⌜b1 = b2⌝.
Proof.
  intros until b1; remember (rev b1) as b1'; revert dependent b1; induction b1'; simpl; intros.
  - destruct b1; last by apply app_cons_not_nil in Heqb1'.
    symmetry in Hlen; apply nil_length_inv in Hlen as ->; auto.
  - apply (f_equal (@rev _)) in Heqb1'; rewrite rev_involutive in Heqb1'; subst; simpl in *.
    rewrite app_length /= in Hlen; destruct (list_snoc b2) as (b2' & ? & ->); first lia.
    rewrite !big_opL_app /= !Nat.add_0_r.
    assert (length (rev b1') = length b2') as Hlen' by (rewrite app_length /= in Hlen; lia); rewrite Hlen'.
    iIntros "[(H1 & Hv1 & _) (H2 & Hv2 & _)]".
    iDestruct (mapsto_value_cohere with "[$Hv1 $Hv2]") as %[=]; subst.
    by iDestruct (IHb1' with "[$H1 $H2]") as %->; first by rewrite rev_involutive.
Qed.

Lemma address_mapsto_value_cohere:
  forall ch v1 v2 sh1 sh2 a,
 address_mapsto ch v1 sh1 a ∗ address_mapsto ch v2 sh2 a ⊢ ⌜v1=v2⌝.
Proof.
  intros.
  iIntros "[H1 H2]".
  rewrite /address_mapsto.
  iDestruct "H1" as (b1 (Hl1 & ? & ?)) "H1".
  iDestruct "H2" as (b2 (Hl2 & ? & ?)) "H2"; subst.
  rewrite -Hl2 in Hl1; by iDestruct (mapsto_list_value_cohere with "[$H1 $H2]") as %->.
Qed.

(*Definition almost_empty rm: Prop :=
  forall loc sh psh k P, rm @ loc = YES sh psh k P -> forall val, ~ k = VAL val.

Definition no_locks phi :=
  forall addr sh sh' z z' P,
phi @ addr <> YES sh sh' (LK z z') P.*)

End heap.

#[export] Hint Resolve VALspec_range_0: normalize.
