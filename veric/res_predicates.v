From iris.proofmode Require Export tactics.
Require Import compcert.cfrontend.Ctypes.
From iris_ora.algebra Require Import gmap.
From iris_ora.logic Require Export logic.
From VST.veric Require Import shares address_conflict.
From VST.msl Require Export shares.
From VST.veric Require Export base Memory algebras juicy_view gen_heap fancy_updates.
Export Values.

Local Open Scope Z_scope.


(** Environment Definitions **)
(* We need these here so we can define the resource in memory for a function pointer. *)

(** GENERAL KV-Maps **)

Set Implicit Arguments.

Module Map. Section map.
Context (B : Type).

Definition t := positive -> option B.

Definition get (h: t) (a:positive) : option B := h a.

Definition set (a:positive) (v: B) (h: t) : t :=
  fun i => if ident_eq i a then Some v else h i.

Definition remove (a: positive) (h: t) : t :=
  fun i => if ident_eq i a then None else h i.

Definition empty : t := fun _ => None.

(** MAP Axioms **)

Lemma gss h x v : get (set x v h) x = Some v.
unfold get, set; if_tac; intuition.
Qed.

Lemma gso h x y v : x<>y -> get (set x v h) y = get h y.
unfold get, set; intros; if_tac; intuition; subst; contradiction.
Qed.

Lemma grs h x : get (remove x h) x = None.
unfold get, remove; intros; if_tac; intuition.
Qed.

Lemma gro h x y : x<>y -> get (remove x h) y = get h y.
unfold get, remove; intros; if_tac; intuition; subst; contradiction.
Qed.

Lemma ext h h' : (forall x, get h x = get h' x) -> h=h'.
Proof.
intros. extensionality x. apply H.
Qed.

Lemma override (a: positive) (b b' : B) h : set a b' (set a b h) = set a b' h.
Proof.
apply ext; intros; unfold get, set; if_tac; intuition. Qed.

Lemma gsspec:
    forall (i j: positive) (x: B) (m: t),
    get (set j x m) i = if ident_eq i j then Some x else get m i.
Proof.
intros. unfold get; unfold set; if_tac; intuition.
Qed.

Lemma override_same : forall id t (x:B), get t id = Some x -> set id x t = t.
Proof.
intros. unfold set. unfold get in H.  apply ext. intros. unfold get.
if_tac; subst; auto.
Qed.

End map.

End Map.

Unset Implicit Arguments.

Global Instance EqDec_calling_convention: EqDec calling_convention.
Proof.
  hnf. decide equality.
  destruct cc_structret, cc_structret0; subst; try tauto; right; congruence.
  destruct cc_unproto, cc_unproto0;  subst; try tauto; right; congruence.
  destruct cc_vararg, cc_vararg0; subst; try tauto.
  destruct (zeq z0 z); subst; [left|right]; congruence.
  right; congruence.
  right; congruence.
Qed.

Section FUNSPEC.

Definition genviron := Map.t block.

Definition venviron := Map.t (block * type).

Definition tenviron := Map.t val.

Inductive environ : Type :=
 mkEnviron: forall (ge: genviron) (ve: venviron) (te: tenviron), environ.

Definition ge_of (rho: environ) : genviron :=
  match rho with mkEnviron ge ve te => ge end.

Definition ve_of (rho: environ) : venviron :=
  match rho with mkEnviron ge ve te => ve end.

Definition te_of (rho: environ) : tenviron :=
  match rho with mkEnviron ge ve te => te end.

Definition any_environ : environ :=
  mkEnviron (fun _ => None)  (Map.empty _) (Map.empty _).

Definition argsEnviron:Type := genviron * (list val).

Global Instance EqDec_type: EqDec type := type_eq.

Definition funsig := (list (ident*type) * type)%type. (* argument and result signature *)

Definition typesig := (list type * type)%type. (*funsig without the identifiers*)

Definition typesig_of_funsig (f:funsig):typesig := (map snd (fst f), snd f).

End FUNSPEC.

Section heap.

Context {Σ : gFunctors}.

Notation mpred := (iProp Σ).

Inductive resource' :=
| VAL (v : memval)
| LK (i z : Z) (R : mpred)
| FUN (sig : typesig) (cc : calling_convention) (A : Type) (P : A -> argsEnviron -> mpred) (Q : A -> environ -> mpred).
(* Will we run into universe issues with higher-order A's? Hopefully not! *)

Definition perm_of_res (r: option (dfrac * resource')) :=
  match r with
  | Some (dq, VAL _) => perm_of_dfrac dq
  | Some (DfracOwn sh, _) => if eq_dec sh Share.bot then None else Some Nonempty
  | Some (DfracDiscarded, _) | Some (DfracBoth _, _) => Some Readable
  | _ => None
  end.

Lemma perm_of_sh_None: forall sh, perm_of_sh sh = None -> sh = Share.bot.
Proof.
  intros ?.
  unfold perm_of_sh.
  if_tac; if_tac; try discriminate.
  if_tac; done.
Qed.

Global Program Instance resource'_ops : resource_ops (leibnizO resource') := { perm_of_res := perm_of_res; memval_of r := match snd r with VAL v => Some v | _ => None end }.
Next Obligation.
Proof.
  discriminate.
Qed.
Next Obligation.
Proof.
  discriminate.
Qed.
Next Obligation.
Proof.
  reflexivity.
Qed.
Next Obligation.
Proof.
  intros ???? Hd.
  destruct r.
  - destruct d1, d2; apply perm_of_dfrac_mono; auto.
  - destruct Hd as [d0 ->%leibniz_equiv].
    destruct d1, d0; simpl; try if_tac; simpl; try if_tac; try constructor; try contradiction; try (destruct H; contradiction).
  - destruct Hd as [d0 ->%leibniz_equiv].
    destruct d1, d0; simpl; try if_tac; simpl; try if_tac; try constructor; try contradiction; try (destruct H; contradiction).
Qed.
Next Obligation.
Proof.
  intros ???? H; hnf in H; subst; auto.
Qed.
Next Obligation.
Proof.
  destruct r as [(?, ?)|]; simpl; auto.
  destruct d, o; simpl; try if_tac; try constructor; try apply perm_order''_None; try apply perm_order''_refl; try done.
  - destruct (perm_of_sh s) eqn: Hs; simpl; try constructor.
    by apply perm_of_sh_None in Hs.
  - destruct (perm_of_sh s) eqn: Hs; simpl; try constructor.
    by apply perm_of_sh_None in Hs.
Qed.
Next Obligation.
Proof.
  simpl; intros.
  destruct r; inv H; done.
Qed.
Next Obligation.
Proof.
  simpl; intros.
  hnf in H0; subst; done.
Qed.

(* collect up all the ghost state required for the logic *)
Class heapGS := HeapGS {
  heapGS_wsatGS :> wsatGS Σ;
  heapGS_gen_heapGS :> gen_heapGS resource' Σ
}.

Context {HGS : heapGS}.

Local Notation resource := resource'.

Definition spec : Type :=  forall (sh: share) (l: address), mpred.

Ltac do_map_arg :=
match goal with |- ?a = ?b =>
  match a with context [map ?x _] =>
    match b with context [map ?y _] => replace y with x; auto end end end.

(* In VST, we do a lot of reasoning directly on rmaps instead of mpreds. How much of that can we avoid? *)
Definition resR_to_resource : optionR (prodR dfracR (agreeR (leibnizO resource))) -> option (dfrac * resource) :=
  option_map (fun '(q, a) => (q, (hd (VAL Undef) (agree_car a)))).

(*Definition heap_inG := resource_map.resource_map_inG(ghost_mapG := gen_heapGpreS_heap(gen_heapGpreS := gen_heap_inG)).
Definition resource_at (m : rmap) (l : address) : option (dfrac * resource) :=
  (option_map (ora_transport (eq_sym (inG_prf(inG := heap_inG)))) (option_map own.inG_fold ((m (inG_id heap_inG)) !! (gen_heap_name (heapGS_gen_heapGS)))))
    ≫= (fun v => resR_to_resource (view_frag_proj v !! l)).
Infix "@" := resource_at (at level 50, no associativity).*)

(*Lemma ord_resource_at : forall n r1 r2, r1 ≼ₒ{n} r2 -> resource_at r1 ≼ₒ{n} resource_at r2.
Proof.
  intros; rewrite /resource_at.
  extensionality l.
  specialize (H (inG_id heap_inG) (gen_heap_name (heapGS_gen_heapGS))).
  destruct (_ !! _), (_ !! _); try done; simpl in *.
  - assert (ora_transport (eq_sym inG_prf) (own.inG_fold o) ≼ₒ{n} 
    ora_transport (eq_sym inG_prf) (own.inG_fold o0)) as [_ Hord'] by admit.
    specialize (Hord' l).
    destruct (_ !! _) as [(?, ?)|], (_ !! _) as [(?, ?)|]; try done; simpl in *.
    + destruct Hord' as [??].
      hnf in H0. admit. (* not necessarily -- we can add discarded fracs, though that won't affect juicy coherence *)
    + hnf in Hord'. admit. (* ditto *)
  - (* The heap could be absent entirely on the LHS, and contain only discarded fracs on the RHS *)
Abort.*)

Definition nonlock (r: resource) : Prop :=
 match r with
 | LK _ _ _ => False
 | _ => True
 end.

(*Lemma nonlock_join: forall r1 r2 r,
  nonlock r1 ->
  nonlock r2 ->
  join r1 r2 r ->
  nonlock r.
Proof.
  intros.
  destruct r1, r2; inv H1; auto.
Qed.*)

Notation "l ↦ dq v" := (mapsto (V:=resource) l dq v)
  (at level 20, dq custom dfrac at level 1, format "l  ↦ dq  v") : bi_scope.

Definition nonlockat (l: address): mpred := ∃ dq r, ⌜nonlock r⌝ ∧ l ↦{dq} r.

Definition shareat (l: address) (sh: share): mpred := ∃r, l ↦{#sh} r.

Program Definition jam {B} {S': B -> Prop} (S: forall l, {S' l}+{~ S' l} ) (P Q: B -> bi) : B -> bi :=
  fun (l: B) => if S l then P l else Q l.

Lemma jam_true: forall B (S': B -> Prop) S P Q loc, S' loc -> @jam B S' S P Q loc = P loc.
Proof.
intros.
unfold jam.
rewrite if_true; auto.
Qed.

Lemma jam_false: forall B (S': B -> Prop) S P Q loc, ~ S' loc -> @jam B S' S P Q loc = Q loc.
Proof.
intros.
unfold jam.
rewrite if_false; auto.
Qed.

(*Lemma boxy_jam:  forall (m: modality) A (S': A -> Prop) S P Q,
      (forall (x: A), boxy m (P x)) ->
      (forall x, boxy m (Q x)) ->
      forall x, boxy m (@jam rmap _ _ _ _ _ _ _ A S' S P Q x).
Proof.
  intros.
   unfold boxy in *.
   apply pred_ext; intros w ?.
   unfold jam in *.
   simpl in *; if_tac. rewrite <- H . simpl. apply H1.
   rewrite <- H0; simpl; apply H1.
   simpl in *; if_tac.
    rewrite <- H in H1; auto.
   rewrite <- H0 in H1; auto.
Qed.

Definition extensible_jam: forall A (S': A -> Prop) S (P Q: A -> mpred),
      (forall (x: A), boxy extendM (P x)) ->
      (forall x, boxy extendM (Q x)) ->
      forall x, boxy extendM  (@jam _ _ _ _ _ _ _ _ _ S' S P Q x).
Proof.
  apply boxy_jam; auto.
Qed.*)

Definition jam_vacuous:
  forall B S S' P Q, (forall x:B, ~ S x) -> @jam B S S' P Q = Q.
Proof.
intros.
extensionality l.
unfold jam.
rewrite if_false; auto.
Qed.

(*Lemma make_sub_rmap: forall w (P: address -> Prop) (P_DEC: forall l, {P l} + {~ P l}),
  (forall l sh k, P l -> res_option (w @ l) = Some (sh, k) -> isVAL k \/ isFUN k) ->
  {w' | level w' = level w /\ resource_at w' =
       (fun l => if P_DEC l then w @ l else core (w @ l)) /\ ghost_of w' = ghost_of w}.
Proof.
  intros.
  apply remake_rmap.
  intros.
    if_tac; [left; eauto |].
    destruct (w @ l) eqn:?H; rewrite ?core_NO, ?core_YES, ?core_PURE; simpl; auto.
    left.
    exists w; split; auto.
    apply ghost_of_approx.
Qed.

Lemma make_sub_rmap_core: forall w (P: address -> Prop) (P_DEC: forall l, {P l} + {~ P l}),
  (forall l sh k, P l -> res_option (w @ l) = Some (sh, k) -> isVAL k \/ isFUN k) ->
  {w' | level w' = level w /\ resource_at w' =
       (fun l => if P_DEC l then w @ l else core (w @ l)) /\ ghost_of w' = core (ghost_of w)}.
Proof.
  intros.
  apply remake_rmap.
  intros.
    if_tac; [left; eauto |].
    destruct (w @ l) eqn:?H; rewrite ?core_NO, ?core_YES, ?core_PURE; simpl; auto.
    left.
    exists w; split; auto.
    apply ghost_fmap_core.
Qed.*)

(*Definition is_resource_pred (p: address -> iProp Σ) (q: resource -> address -> nat -> Prop) :=
  forall l w, (p l) w = q (w @ l) l (level w).

Definition resource_stable (p: address -> iProp Σ) :=
  forall l w w', w @ l = w' @ l -> level w = level w' -> (p l) w = (p l) w'.

Lemma is_resource_pred_resource_stable: forall {p},
  (exists q, is_resource_pred p q) -> resource_stable p.
Proof.
  unfold is_resource_pred, resource_stable.
  intros.
  destruct H as [q ?]; rewrite !H.
  rewrite H0; auto.
Qed.

(* This is about splitting one segment into two segments. *)
Lemma allp_jam_split2: forall (P Q R: address -> Prop) (p q r: address -> iProp Σ)
  (P_DEC: forall l, {P l} + {~ P l})
  (Q_DEC: forall l, {Q l} + {~ Q l})
  (R_DEC: forall l, {R l} + {~ R l}),
  (exists resp, is_resource_pred p resp) ->
  (exists resp, is_resource_pred q resp) ->
  (exists resp, is_resource_pred r resp) ->
  Ensemble_join Q R P ->
  (forall l, Q l -> p l = q l) ->
  (forall l, R l -> p l = r l) ->
  (forall l m sh k, P l -> (p l) m -> res_option (m @ l) = Some (sh, k) -> isVAL k \/ isFUN k) ->
  allp (jam P_DEC p noat) =
  (allp (jam Q_DEC q noat)) * (allp (jam R_DEC r noat)).
Proof.
  intros until R_DEC.
  intros ST_P ST_Q ST_R.
  intros [] ? ? ?.
  apply pred_ext; intros w; simpl; intros.
  + destruct (make_sub_rmap_core w Q Q_DEC) as [w1 [? ?]].
    {
      intros. eapply H3; [| | eauto].
      + firstorder.
      + specialize (H4 l); if_tac in H4; [auto | firstorder].
    }
    destruct (make_sub_rmap w R R_DEC) as [w2 [? ?]].
    {
      intros. eapply H3; [| | eauto].
      + firstorder.
      + specialize (H4 l); if_tac in H4; [auto | firstorder].
    }
    exists w1, w2.
    split3; auto.
    - apply resource_at_join2; try congruence.
      intro l.
      destruct H6, H8.
      rewrite H6, H8.
      pose proof core_unit (w @ l).
      destruct (Q_DEC l), (R_DEC l).
      * firstorder.
      * apply join_comm; auto.
      * auto.
      * specialize (H4 l).
        rewrite if_false in H4 by firstorder.
        rewrite identity_core by auto.
        apply core_duplicable.
      * destruct H6 as [_ ->], H8 as [_ ->].
        apply core_unit.
    - intros l.
      specialize (H4 l).
      if_tac.
      * rewrite <- H1 by auto.
        rewrite if_true in H4 by firstorder.
        erewrite <- (is_resource_pred_resource_stable ST_P); [eauto | | auto].
        destruct H6; rewrite H6, if_true by auto; auto.
      * destruct H6; rewrite H6, if_false by auto.
        apply core_identity.
    - intros l.
      specialize (H4 l).
      if_tac.
      * rewrite <- H2 by auto.
        rewrite if_true in H4 by firstorder.
        erewrite <- (is_resource_pred_resource_stable ST_P); [eauto | | auto].
        destruct H8; rewrite H8, if_true by auto; auto.
      * destruct H8; rewrite H8, if_false by auto.
        apply core_identity.
  + destruct H4 as [y [z [? [H5 H6]]]].
    specialize (H5 b); specialize (H6 b).
    if_tac.
    - if_tac in H5; if_tac in H6.
      * firstorder.
      * rewrite H1 by auto.
        erewrite (is_resource_pred_resource_stable ST_Q); [eauto | | apply join_level in H4; symmetry; tauto].
        apply resource_at_join with (loc := b) in H4.
        apply join_comm, H6 in H4.
        auto.
      * rewrite H2 by auto; auto.
        erewrite (is_resource_pred_resource_stable ST_R); [eauto | | apply join_level in H4; symmetry; tauto].
        apply resource_at_join with (loc := b) in H4.
        apply H5 in H4.
        auto.
      * firstorder.
    - rewrite if_false in H5 by firstorder.
      rewrite if_false in H6 by firstorder.
      apply resource_at_join with (loc := b) in H4.
      apply H5 in H4; rewrite <- H4; auto.
Qed.


Lemma allp_jam_overlap: forall (P Q: address -> Prop) (p q: address -> iProp Σ)
  (P_DEC: forall l, {P l} + {~ P l})
  (Q_DEC: forall l, {Q l} + {~ Q l}),
  (exists resp, is_resource_pred p resp) ->
  (exists resp, is_resource_pred q resp) ->
  (forall l w1 w2, p l w1 -> q l w2 -> joins w1 w2 -> False) ->
  (exists l, P l /\ Q l) ->
  allp (jam P_DEC p noat) * allp (jam Q_DEC q noat) ⊢ False.
Proof.
  intros.
  intro w; simpl; intros.
  destruct H3 as [w1 [w2 [? [? ?]]]].
  destruct H2 as [l ?].
  specialize (H4 l).
  specialize (H5 l).
  rewrite if_true in H4, H5 by tauto.
  apply (H1 l w1 w2); auto.
  eauto.
Qed.

Lemma yesat_join_diff:
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

Global Open Scope bi_scope.

Definition VALspec : spec :=
       fun (sh: share) (l: address) => ∃v, l ↦{#sh} VAL v.

Definition VALspec_range (n: Z) : spec :=
     fun (sh: Share.t) (l: address) => [∗ list] i ∈ seq 0 (Z.to_nat n), VALspec sh (adr_add l (Z.of_nat i)).

Definition nonlock_permission_bytes (sh: share) (a: address) (n: Z) : mpred :=
  [∗ list] i ∈ seq 0 (Z.to_nat n), ∃r, ⌜nonlock r⌝ ∧ adr_add a (Z.of_nat i) ↦{#sh} r.

Definition nthbyte (n: Z) (l: list memval) : memval :=
     nth (Z.to_nat n) l Undef.

(*(*  Unfortunately address_mapsto_old, while a more elegant definition than
   address_mapsto, is not quite right.  For example, it doesn't uniquely determine v *)
Definition address_mapsto_old (ch: memory_chunk) (v: val) : spec :=
        fun (sh: Share.t) (l: address)  => 
             allp (jam (adr_range_dec l (size_chunk ch)) 
                              (fun l' => yesat NoneP (VAL (nthbyte (snd l' - snd l) (encode_val ch v))) sh l')
                           noat).*)

Definition address_mapsto (ch: memory_chunk) (v: val) : spec :=
        fun (sh: Share.t) (l: address) =>
           ∃ bl: list memval, 
               ⌜length bl = size_chunk_nat ch  /\ decode_val ch bl = v /\ (align_chunk ch | snd l)⌝ ∧
               [∗ list] i ∈ seq 0 (size_chunk_nat ch), adr_add l (Z.of_nat i) ↦{#sh} (VAL (nthbyte (Z.of_nat i) bl)).

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
               [∗ list] i ∈ seq 0 (size_chunk_nat ch), adr_add l (Z.of_nat i) ↦□ (VAL (nthbyte (Z.of_nat i) bl)).

Definition LKspec lock_size (R: mpred) : spec :=
   fun (sh: Share.t) (l: address)  =>
    [∗ list] i ∈ seq 0 (Z.to_nat lock_size), adr_add l (Z.of_nat i) ↦{#sh} LK lock_size (Z.of_nat i) R.

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
{ rewrite lookup_seq_lt; [done | lia]. }
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
   ∧ ([∗ list] i ∈ seq 0 (size_chunk_nat ch), adr_add l (Z.of_nat i) ↦{#sh}
                                                (VAL (nthbyte (Z.of_nat i) bl)))).
  2: { iIntros "H"; iDestruct "H" as (bl [??]) "H"; iExists (decode_val ch bl), bl; auto. }
  rewrite size_chunk_conv Nat2Z.id.
  forget (size_chunk_nat ch) as n.
  induction n.
  - simpl; iIntros "_".
    by iExists nil.
  - rewrite seq_S big_sepL_app /=.
    iIntros "(H & Hv & _)".
    iDestruct "Hv" as (v) "Hv".
    iDestruct (IHn with "H") as (bl [??]) "H"; subst.
    iExists (bl ++ [v]); iSplit.
    { rewrite app_length /=; iPureIntro; split; auto; lia. }
    rewrite big_sepL_app /=.
    rewrite /nthbyte app_nth2; last lia.
    rewrite Nat2Z.id minus_diag /=.
    iFrame.
    iApply (big_sepL_mono with "H").
    intros ???%lookup_seq.
    by rewrite app_nth1; last lia.
Qed.

Lemma address_mapsto_VALspec_range:
  forall ch v sh l,
        address_mapsto ch v sh l ⊢ VALspec_range (size_chunk ch) sh l.
Proof.
intros.
unfold address_mapsto, VALspec_range.
iIntros "H"; iDestruct "H" as (bl (? & ? & ?)) "H".
rewrite size_chunk_conv Nat2Z.id.
iApply (big_sepL_mono with "H").
by intros; iIntros "?"; iExists _.
Qed.

(*Lemma approx_eq_i:
  forall (P Q: iProp Σ) (w: rmap),
      (|> ! (P <=> Q)) w -> approx (level w) P = approx (level w) Q.
Proof.
intros.
apply pred_ext'; extensionality m'.
unfold approx.
apply and_ext'; auto; intros.
destruct (level_later_fash _ _ H0) as [m1 [? ?]].
specialize (H _ H1).
specialize (H m').
spec H.
rewrite H2; auto.
destruct H; apply prop_ext. intuition eauto.
Qed.

Lemma level_later {A} `{H : ageable A}: forall {w: A} {n': nat},
         laterR (level w) n' ->
       exists w', laterR w w' /\ n' = level w'.
Proof.
intros.
remember (level w) as n.
revert w Heqn; induction H0; intros; subst.
case_eq (age1 w); intros.
exists a; split. constructor; auto.
symmetry; unfold age in H0; simpl in H0.
  unfold natAge1 in H0; simpl in H0. revert H0; case_eq (level w); intros; inv H2.
  apply age_level in H1. congruence. rewrite age1_level0 in H1.
   rewrite H1 in H0. inv H0.
 specialize (IHclos_trans1 _ (refl_equal _)).
  destruct IHclos_trans1 as [w2 [? ?]].
  subst.
  specialize (IHclos_trans2 _ (refl_equal _)).
  destruct IHclos_trans2 as [w3 [? ?]].
  subst.
  exists w3; split; auto. econstructor 2; eauto.
Qed.

(* TODO: resume this lemma. *)
(*
Lemma fun_assert_contractive:
   forall fml cc (A: TypeTree)
     (P Q: iProp Σ -> forall ts, dependent_type_functor_rec ts (AssertTrue A) (iProp Σ)) v,
      (forall ts x rho, nonexpansive (fun R => P R ts x rho)) ->
      (forall ts x rho, nonexpansive (fun R => Q R ts x rho)) ->
      contractive (fun R : iProp Σ => fun_assert fml cc A (P R) (Q R) v).
Proof.
  intros.
  (*
  assert (H': forall xvl: A * environ, nonexpansive (fun R => P R (fst xvl) (snd xvl)))
    by auto; clear H; rename H' into H.
  assert (H': forall xvl: A * environ, nonexpansive (fun R => Q R (fst xvl) (snd xvl)))
    by auto; clear H0; rename H' into H0.
  *)
  intro; intros.
  rename H0 into H'.
  intro; intros.
  intro; intros; split; intros ? ? H7; simpl in H1.
  + assert (a >= level a')%nat.
    {
      apply necR_level in H2. clear - H1 H2.
      apply le_trans with (level y); auto.
    }
    clear y H1 H2. rename H3 into H2.
    hnf.
    destruct H7 as [loc H7].
    hnf in H7. destruct H7 as [H1 H3].  hnf in H1.
    exists loc.
    apply prop_andp_i; auto.
    split; auto.
    hnf in H3|-*.
    intro; specialize ( H3 b).
    hnf in H3|-*.
    if_tac; auto.
    subst b.
    hnf in H3|-*.
    rewrite H3; clear H3.
    f_equal.
    simpl.
    f_equal.
    extensionality ts.
    extensionality x.
    extensionality b.
    extensionality rho.
    unfold packPQ.
    simpl.
    if_tac.
    - (* P proof *)
      specialize ( H ts x rho P0 Q0).
Check approx_eq_i.
      apply approx_eq_i.
pose proof (later_derives (unfash_derives H)).
      apply (later_derives (unfash_derives H)); clear H.
      rewrite later_unfash.
      unfold unfash.
      red. red.
      apply pred_nec_hereditary with a; auto.
      apply nec_nat; auto.
(* Q proof *)
clear H; rename H' into H.
specialize ( H (x,vl) P0 Q0).
apply approx_eq_i.
apply (later_derives (unfash_derives H)); clear H.
rewrite later_unfash.
red. red. red.
apply pred_nec_hereditary with a; auto.
apply nec_nat; auto.
(* Part 2 *)
assert (a >= level a')%nat.
 apply necR_level in H2. clear - H1 H2. apply le_trans with (level y); auto.
 clear y H1 H2. rename H3 into H2.
unfold fun_assert.
destruct H7 as [loc H7].
hnf in H7. destruct H7 as [H1 H3].  hnf in H1.
exists loc.
apply prop_andp_i; auto.
split; auto.
hnf.
intro.
specialize ( H3 b).
hnf in H3|-*.
if_tac; auto.
subst b.
hnf in H3|-*.
unfold yesat_raw in *.
rewrite H3; clear H3.
f_equal.
simpl.
f_equal.
unfold compose.
extensionality xy; destruct xy as [x [y [vl [ ] ]]].
unfold packPQ.
simpl.
if_tac.
(* P proof *)
specialize ( H (x,vl) P0 Q0).
symmetry.
apply approx_eq_i.
apply (later_derives (unfash_derives H)); clear H.
rewrite later_unfash.
red. red. red.
apply pred_nec_hereditary with a; auto.
apply nec_nat; auto.
(* Q proof *)
clear H; rename H' into H.
specialize ( H (x,vl) P0 Q0).
symmetry.
apply approx_eq_i.
apply (later_derives (unfash_derives H)); clear H.
rewrite later_unfash.
red. red. red.
apply pred_nec_hereditary with a; auto.
apply nec_nat; auto.
Qed.
*)
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

Definition core_load (ch: memory_chunk) (l: address) (v: val): mpred :=
  ∃ bl: list memval,
  ⌜length bl = size_chunk_nat ch /\ decode_val ch bl = v /\ (align_chunk ch | snd l)⌝ ∧
    ([∗ list] i ∈ seq 0 (size_chunk_nat ch), ∃ sh, mapsto (adr_add l (Z.of_nat i)) sh (VAL (nthbyte i bl)))
    ∗ True.

Definition core_load' (ch: memory_chunk) (l: address) (v: val) (bl: list memval) : mpred :=
  ⌜length bl = size_chunk_nat ch /\ decode_val ch bl = v /\ (align_chunk ch | snd l)⌝ ∧
    ([∗ list] i ∈ seq 0 (size_chunk_nat ch), ∃ sh, mapsto (adr_add l (Z.of_nat i)) sh (VAL (nthbyte i bl)))
    ∗ True.

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
  rewrite big_sepL_app plus_0_l.
  rewrite -{2}(plus_0_r (Z.to_nat n)) -fmap_add_seq big_sepL_fmap.
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
  rewrite big_sepL_app plus_0_l.
  rewrite -{2}(plus_0_r (Z.to_nat n)) -fmap_add_seq big_sepL_fmap.
  setoid_rewrite Nat2Z.inj_add; rewrite Z2Nat.id; last lia.
  unfold adr_add; simpl.
  by iSplit; iIntros "[$ H]"; iApply (big_sepL_mono with "H"); intros ???; rewrite Z.add_assoc.
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
  iDestruct (mapsto_valid_2 with "H1 H2") as %[H _].
  apply share_valid2_joins in H as (? & ? & ?%share_joins_self); contradiction.
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
  range_overlap p1 n1 p2 n2 ->
  nonlock_permission_bytes sh p1 n1 ∗ nonlock_permission_bytes sh p2 n2 ⊢ False.
Proof.
  intros ????? ((?, ?) & Hadr1 & Hadr2).
  destruct p1 as (?, ofs1), p2 as (?, ofs2), Hadr1, Hadr2; subst.
  iIntros "[H1 H2]".
  unfold nonlock_permission_bytes.
  rewrite (big_sepL_lookup_acc _ _ _ (Z.to_nat (z - ofs1))).
  rewrite (big_sepL_lookup_acc _ (seq _ (Z.to_nat n2)) _ (Z.to_nat (z - ofs2))).
  iDestruct "H1" as "[H1 _]"; iDestruct "H2" as "[H2 _]".
  iDestruct "H1" as (v1 ?) "H1"; iDestruct "H2" as (v2 ?) "H2".
  rewrite /adr_add /=.
  rewrite !Z2Nat.id; try lia.
  rewrite !Zplus_minus.
  iDestruct (mapsto_valid_2 with "H1 H2") as %[J _].
  apply share_valid2_joins in J as (? & ? & ?%share_joins_self); contradiction.
  { rewrite lookup_seq_lt; [done | lia]. }
  { rewrite lookup_seq_lt; [done | lia]. }
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

Lemma mapsto_list_value_cohere: forall a sh1 sh2 n b1 b2 (Hl1: length b1 = n) (Hl2: length b2 = n),
  (([∗ list] i ∈ seq 0 n, mapsto (adr_add a (Z.of_nat i)) sh1 (VAL (nthbyte (Z.of_nat i) b1))) ∗
   [∗ list] i ∈ seq 0 n, mapsto (adr_add a (Z.of_nat i)) sh2 (VAL (nthbyte (Z.of_nat i) b2))) ⊢
  ⌜b1 = b2⌝.
Proof.
  induction n as [|n']; intros.
  - apply nil_length_inv in Hl1, Hl2; subst; auto.
  - rewrite seq_S !big_sepL_app /=.
    iIntros "[(H1 & Hv1 & _) (H2 & Hv2 & _)]".
    iDestruct (mapsto_value_cohere with "[$Hv1 $Hv2]") as %Heq.
    inversion Heq as [Heq'].
    rewrite /nthbyte Nat2Z.id in Heq'.
    rewrite -(take_drop n' b1) -(take_drop n' b2) in Heq' |- *.
    pose proof (drop_length b1 n') as Hd1; pose proof (drop_length b2 n') as Hd2.
    rewrite Hl1 Nat.sub_succ_l in Hd1; last done.
    rewrite Hl2 Nat.sub_succ_l in Hd2; last done.
    rewrite minus_diag in Hd1, Hd2.
    destruct (drop n' b1) as [| ? [|]], (drop n' b2) as [| ? [|]]; try discriminate.
    pose proof (take_length_le b1 n' ltac:(lia)) as Hlen1.
    pose proof (take_length_le b2 n' ltac:(lia)) as Hlen2.
    rewrite -{1}Hlen1 -{3}Hlen2 !nth_middle in Heq'; subst.
    iDestruct (IHn' (take n' b1) (take n' b2) with "[H1 H2]") as %->; try done.
    iSplitL "H1".
    + iApply (big_sepL_mono with "H1").
      intros ???%lookup_seq.
      rewrite /nthbyte Nat2Z.id app_nth1; [done | lia].
    + iApply (big_sepL_mono with "H2").
      intros ???%lookup_seq.
      rewrite /nthbyte Nat2Z.id app_nth1; [done | lia].
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
  by iDestruct (mapsto_list_value_cohere with "[$H1 $H2]") as %->.
Qed.

(*Definition almost_empty rm: Prop :=
  forall loc sh psh k P, rm @ loc = YES sh psh k P -> forall val, ~ k = VAL val.

Definition no_locks phi :=
  forall addr sh sh' z z' P,
phi @ addr <> YES sh sh' (LK z z') P.*)

End heap.

#[export] Hint Resolve VALspec_range_0: normalize.

Arguments heapGS _ : clear implicits.

(* To use the heap, do Context `{!heapGS Σ}. *)

Definition rmap `{heapGS Σ} := iResUR Σ.
Definition resource `{heapGS Σ} := resource'(Σ := Σ).
Definition mpred `{heapGS Σ} := iProp Σ.

Global Notation "l ↦ dq v" := (mapsto (V:=resource) l dq v)
  (at level 20, dq custom dfrac at level 1, format "l  ↦ dq  v") : bi_scope.

(*Global Infix "@" := resource_at (at level 50, no associativity).*)
