(**
  A program logic for the atomic machine instantiated with lambda-Rust
  ([at_step] with [lr_language]), after lambda-Rust's [lrust.lang.lifting].

  [at_lang] is the machine as an Iris language whose threads are the
  machine's thread states ([tstate]) and whose state is the shared memory and
  the reader/writer map.  Its primitive steps are the per-thread rules of
  [at_step] ([at_prim_step]): [Core_Try] runs the sequential semantics of
  [sq_sem.v] and reserves its events, [Core_Commit] finishes them, the
  [SC_] rules perform the atomic operations, and [Spawn] forks.  Iris's
  thread pool then appends forked threads where [at_step] uses the least
  free index; [at_adequacy.v] relates the two.

  The logic is built on the sequential one of [sq_logic.v].  Its state
  interpretation is the sequential one, [heap_ctx (sq_heap m)], together
  with the reservations ([at_resv]), and a [Core_Try] step is a step of
  [sq_lang]: the rules for the non-atomic operations run the corresponding
  rule of [sq_logic.v] for that step ([sq_wp_try], [sq_wp_step]) and only add
  the reservations, and the pure steps are those of the sequential logic
  ([at_pure_exec_sq]).  What only the machine has, the atomic operations and
  [Fork], gets its own rules.  The rules are lambda-Rust's, with the same
  resources ([l ↦{q} v], [†l…n]).  As in lambda-Rust, the rules for
  non-atomic accesses, allocation, and deallocation take two steps, here
  [Core_Try] and [Core_Commit], so the reservation in between is never
  exposed.

  A [WP] for [at_lang] is about a thread state, usually [Running e []], with
  a postcondition on [at_val].
*)

From iris.algebra Require Import auth gset gmap.
From iris.base_logic.lib Require Import ghost_map.
From iris.program_logic Require Export weakestpre lifting.
From iris.proofmode Require Import proofmode.
From lrust.lang Require Import lifting.
Require Import VST.atomic_machine.atomic_machine.
Require Export VST.atomic_machine.lambda_rust.logic.sq_logic.
Require Import VST.atomic_machine.lambda_rust.equivalence.
Require Import VST.atomic_machine.lambda_rust.adequacy.
Require Import VST.atomic_machine.lambda_rust.safety_reflection.
Require Import VST.atomic_machine.lambda_rust.machine_safety.

Set Default Proof Using "Type".
#[local] Set Warnings "-redundant-canonical-projection".

(** * Evaluation contexts around a redex *)

Lemma fill_decompose K K' e r :
  redex_shape r -> to_val r = None -> to_val e = None ->
  fill K e = fill K' r -> exists K'', K' = K'' ++ K /\ e = fill K'' r.
Proof.
  intros Hr Hvr Hve. revert K'. induction K as [ | Ki K IH ] using rev_ind; intros K' Hfill.
  - exists K'. by rewrite app_nil_r.
  - destruct K' as [ | Kj K' _ ] using rev_ind.
    + exfalso. rewrite fill_app in Hfill. simpl in Hfill.
      destruct (Hr Ki (fill K e) (eq_sym Hfill)) as [v Hv]. by rewrite fill_not_val in Hv.
    + rewrite !fill_app in Hfill. simpl in Hfill.
      pose proof (fill_item_no_val_inj Ki Kj _ _ (fill_not_val K e Hve)
                    (fill_not_val K' r Hvr) Hfill) as <-.
      apply (inj (fill_item Ki)) in Hfill.
      destruct (IH K' Hfill) as (K'' & -> & ->). exists K''. by rewrite assoc.
Qed.

Lemma lr_head_step_not_val e m T e' m' : lr_head_step e m T e' m' -> to_val e = None.
Proof. by destruct 1. Qed.

Lemma lr_head_external_not_val e op k : lr_head_external e op k -> to_val e = None.
Proof. by destruct 1. Qed.

Lemma lr_head_step_redex_shape e m T e' m' : lr_head_step e m T e' m' -> redex_shape e.
Proof. intros Hh Ki e1 ->. by eapply (sq_base_ctx_step_val _ _ m T e' m' []), SqHeadStep. Qed.

Lemma lr_head_external_redex_shape e op k : lr_head_external e op k -> redex_shape e.
Proof. intros Hh Ki e1 ->. destruct Ki; inversion Hh; subst; rewrite ?to_of_val; eauto. Qed.

Lemma lr_head_step_external e m T e' m' op k :
  lr_head_step e m T e' m' -> lr_head_external e op k -> False.
Proof. destruct 1; inversion 1. Qed.

(** A step of a thread whose expression has redex shape happens at its head. *)

Lemma lr_step_head e m T e' m' :
  redex_shape e -> lr_step e m T e' m' -> lr_head_step e m T e' m'.
Proof.
  intros Hr Hstep. inversion Hstep as [K e1 ? ? e2 ? Hh He]; subst.
  destruct (fill_redex_shape_inv K e1 _ Hr (lr_head_step_not_val _ _ _ _ _ Hh) eq_refl)
    as (-> & _). exact Hh.
Qed.

Lemma lr_external_head e op k :
  redex_shape e -> lr_external e op k -> lr_head_external e op k.
Proof.
  intros Hr Hext. inversion Hext as [K e1 ? k1 Hh He]; subst.
  destruct (fill_redex_shape_inv K e1 _ Hr (lr_head_external_not_val _ _ _ Hh) eq_refl)
    as (-> & _). exact Hh.
Qed.

Lemma lr_spawn_head e c' c_new :
  redex_shape e -> lr_spawn e c' c_new -> e = Fork c_new /\ c' = Lit LitPoison.
Proof.
  intros Hr Hspawn. inversion Hspawn as [K e1 He]; subst.
  by destruct (fill_redex_shape_inv K (Fork c_new) _ Hr eq_refl eq_refl) as (-> & _).
Qed.

(** * The language *)

Definition at_val : Type := val.
Definition at_state : Type := (lr_mem * rw_map)%type.
Definition at_obs : Type := Empty_set.

Local Notation lr_tstate := (tstate (L := lr_language)).

Definition at_of_val (v : at_val) : lr_tstate := Running (of_val v) [].

Definition at_to_val (t : lr_tstate) : option at_val :=
  match t with
  | Running e [] => to_val e
  | _ => None
  end.

(** The rules of [at_step] for the thread at hand. *)
Inductive at_prim_step
    : lr_tstate -> at_state -> list at_obs -> lr_tstate -> at_state -> list lr_tstate -> Prop :=
| AtTry c m mu T c' m' mu' :
    lr_step c m T c' m' ->
    rsv T mu = Some mu' ->
    at_prim_step (Running c []) (m, mu) [] (Running c' T) (m', mu') []
| AtCommit c T m mu mu' :
    T ≠ [] ->
    atomic_machine.fin T mu = Some mu' ->
    at_prim_step (Running c T) (m, mu) [] (Running c []) (m, mu') []
| AtRead c ly l v K m mu :
    lr_external c (ALoad ly l) K ->
    readable mu (layout_to_locs l ly) ->
    load m l ly = Some v ->
    at_prim_step (Running c []) (m, mu) [] (Running (K (Some v)) []) (m, mu) []
| AtWrite c ly l v m' K m mu :
    lr_external c (AStore ly l v) K ->
    writable mu (layout_to_locs l ly) ->
    store m l ly v = Some m' ->
    at_prim_step (Running c []) (m, mu) [] (Running (K None) []) (m', mu) []
| AtCasSuc c ly l v_exp v_new v_cur m' K m mu :
    lr_external c (ACAS ly l v_exp v_new) K ->
    writable mu (layout_to_locs l ly) ->
    load m l ly = Some v_cur ->
    lr_val_eq m v_cur v_exp ->
    store m l ly v_new = Some m' ->
    at_prim_step (Running c []) (m, mu) []
      (Running (K (Some (LitV (lit_of_bool true)))) []) (m', mu) []
| AtCasFail c ly l v_exp v_new v_cur K m mu :
    lr_external c (ACAS ly l v_exp v_new) K ->
    readable mu (layout_to_locs l ly) ->
    load m l ly = Some v_cur ->
    lr_val_neq m v_cur v_exp ->
    at_prim_step (Running c []) (m, mu) []
      (Running (K (Some (LitV (lit_of_bool false)))) []) (m, mu) []
| AtCasStuck c ly l v_exp v_new v_cur K m mu :
    lr_external c (ACAS ly l v_exp v_new) K ->
    load m l ly = Some v_cur ->
    lr_val_eq m v_cur v_exp ->
    ~ writable mu (layout_to_locs l ly) ->
    at_prim_step (Running c []) (m, mu) [] StuckState (m, mu) []
| AtSpawn c c' c_new m mu :
    lr_spawn c c' c_new ->
    at_prim_step (Running c []) (m, mu) [] (Running c' []) (m, mu) [Running c_new []].

Lemma at_val_stuck t σ κ t' σ' efs : at_prim_step t σ κ t' σ' efs -> at_to_val t = None.
Proof.
  destruct 1; simpl; eauto using lr_step_not_val, lr_external_not_val, lr_spawn_not_val.
  by destruct T.
Qed.

Lemma at_lang_mixin : LanguageMixin at_of_val at_to_val at_prim_step.
Proof.
  split.
  - intros v. apply to_of_val.
  - intros [e [ | ] | ] v; simpl; try discriminate. intros ?. by rewrite /at_of_val (of_to_val e v).
  - apply at_val_stuck.
Qed.

Canonical Structure at_lang := Language at_lang_mixin.

(** Evaluation contexts *)

Definition at_fill (K : list ectx_item) (t : lr_tstate) : lr_tstate :=
  match t with
  | Running e T => Running (fill K e) T
  | StuckState => StuckState
  end.

Global Instance at_fill_ctx K : LanguageCtx (at_fill K).
Proof.
  split.
  - intros [e [ | ] | ]; simpl; try done. apply fill_not_val.
  - intros t1 σ1 κ t2 σ2 efs Hstep. destruct Hstep; simpl.
    + econstructor; [ | done ]. destruct H as [K' e1 ? ? e2 ? Hh].
      rewrite -!fill_app. by constructor.
    + by econstructor.
    + inversion H as [K' e1 ? k Hh]; subst. rewrite -!fill_app.
      eapply (AtRead _ _ _ _ (fun ov => fill (K' ++ K) (k ov))); [ by constructor | done | done ].
    + inversion H as [K' e1 ? k Hh]; subst. rewrite -!fill_app.
      eapply (AtWrite _ _ _ _ _ (fun ov => fill (K' ++ K) (k ov))); [ by constructor | done | done ].
    + inversion H as [K' e1 ? k Hh]; subst. rewrite -!fill_app.
      eapply (AtCasSuc _ _ _ _ _ _ _ (fun ov => fill (K' ++ K) (k ov))); [ by constructor | done.. ].
    + inversion H as [K' e1 ? k Hh]; subst. rewrite -!fill_app.
      eapply (AtCasFail _ _ _ _ _ _ (fun ov => fill (K' ++ K) (k ov))); [ by constructor | done.. ].
    + inversion H as [K' e1 ? k Hh]; subst. rewrite -!fill_app.
      eapply AtCasStuck; [ by apply (LREctxExternal (K' ++ K) e1 _ k) | done.. ].
    + destruct H as [K' e]. rewrite -!fill_app. constructor. by constructor.
  - intros [e T | ] σ1 κ t2 σ2 efs Hv Hstep; [ | inversion Hstep ].
    inversion Hstep as [c m mu T' c' m' mu' Hs Hrsv | c T' m mu mu' Hne Hfin
      | c ly l v k m mu Hext Hmu Hload | c ly l v m' k m mu Hext Hmu Hstore
      | c ly l ve vn vc m' k m mu Hext Hmu Hload Heq Hstore
      | c ly l ve vn vc k m mu Hext Hmu Hload Hneq | c ly l ve vn vc k m mu Hext Hload Heq Ho
      | c c' cn m mu Hspawn ]; subst.
    + simpl in Hv. inversion Hs as [K' e1 ? ? e2 ? Hh He]; subst.
      destruct (fill_decompose K K' e e1 (lr_head_step_redex_shape _ _ _ _ _ Hh)
                  (lr_head_step_not_val _ _ _ _ _ Hh) Hv (eq_sym He)) as (K'' & -> & ->).
      exists (Running (fill K'' e2) T'). rewrite /= fill_app. split; [ done | ].
      econstructor; [ by constructor | done ].
    + exists (Running e []). split; [ done | ]. by constructor.
    + simpl in Hv. inversion Hext as [K' e1 ? k1 Hh He]; subst.
      destruct (fill_decompose K K' e e1 (lr_head_external_redex_shape _ _ _ Hh)
                  (lr_head_external_not_val _ _ _ Hh) Hv (eq_sym He)) as (K'' & -> & ->).
      exists (Running (fill K'' (k1 (Some v))) []). rewrite /= fill_app. split; [ done | ].
      eapply (AtRead _ _ _ _ (fun ov => fill K'' (k1 ov))); [ by constructor | done | done ].
    + simpl in Hv. inversion Hext as [K' e1 ? k1 Hh He]; subst.
      destruct (fill_decompose K K' e e1 (lr_head_external_redex_shape _ _ _ Hh)
                  (lr_head_external_not_val _ _ _ Hh) Hv (eq_sym He)) as (K'' & -> & ->).
      exists (Running (fill K'' (k1 None)) []). rewrite /= fill_app. split; [ done | ].
      eapply (AtWrite _ _ _ _ _ (fun ov => fill K'' (k1 ov))); [ by constructor | done | done ].
    + simpl in Hv. inversion Hext as [K' e1 ? k1 Hh He]; subst.
      destruct (fill_decompose K K' e e1 (lr_head_external_redex_shape _ _ _ Hh)
                  (lr_head_external_not_val _ _ _ Hh) Hv (eq_sym He)) as (K'' & -> & ->).
      eexists (Running (fill K'' (k1 _)) []). rewrite /= fill_app. split; [ done | ].
      eapply (AtCasSuc _ _ _ _ _ _ _ (fun ov => fill K'' (k1 ov))); [ by constructor | done.. ].
    + simpl in Hv. inversion Hext as [K' e1 ? k1 Hh He]; subst.
      destruct (fill_decompose K K' e e1 (lr_head_external_redex_shape _ _ _ Hh)
                  (lr_head_external_not_val _ _ _ Hh) Hv (eq_sym He)) as (K'' & -> & ->).
      eexists (Running (fill K'' (k1 _)) []). rewrite /= fill_app. split; [ done | ].
      eapply (AtCasFail _ _ _ _ _ _ (fun ov => fill K'' (k1 ov))); [ by constructor | done.. ].
    + simpl in Hv. inversion Hext as [K' e1 ? k1 Hh He]; subst.
      destruct (fill_decompose K K' e e1 (lr_head_external_redex_shape _ _ _ Hh)
                  (lr_head_external_not_val _ _ _ Hh) Hv (eq_sym He)) as (K'' & -> & ->).
      exists StuckState. split; [ done | ]. eapply AtCasStuck; [ by constructor | done.. ].
    + simpl in Hv. inversion Hspawn as [K' e1 He]; subst.
      assert (Hr : redex_shape (Fork cn)) by (intros Ki e' Heq; destruct Ki; discriminate).
      destruct (fill_decompose K K' e (Fork cn) Hr eq_refl Hv (eq_sym He)) as (K'' & -> & ->).
      exists (Running (fill K'' (Lit LitPoison)) []). rewrite /= fill_app. split; [ done | ].
      by constructor.
Qed.


Global Instance at_state_inhabited : Inhabited at_state := populate (∅, ∅).

(** * Sequential steps

    A thread steps as in [sq_lang] by [Core_Try], and a thread that can do so
    is not at an atomic operation or a [Fork]. *)

Lemma sq_prim_step_lr_step (e : sq_expr) m κ e' m' efs :
  prim_step e m κ e' m' efs <-> lr_step e m κ e' m' /\ efs = [].
Proof.
  split.
  - intros [K e1 e2 -> -> Hs]. inversion Hs; subst. split; [ by apply LREctxStep | done ].
  - intros [[K e1 ? ? e2 ? Hh] ->]. apply (Ectx_step' (Λ := sq_ectx_lang) K). by apply SqHeadStep.
Qed.

Lemma lr_step_external_disjoint e m T e' m' op k :
  lr_step e m T e' m' -> lr_external e op k -> False.
Proof.
  intros [K1 e1 ?? e2 ? Hh] Hext. inversion Hext as [K2 e3 ? k' Hh' Heq].
  destruct (fill_redex_unique K2 K1 e3 e1 (lr_head_external_redex_shape _ _ _ Hh')
              (lr_head_step_redex_shape _ _ _ _ _ Hh) (lr_head_external_not_val _ _ _ Hh')
              (lr_head_step_not_val _ _ _ _ _ Hh) Heq) as [_ ->].
  exact (lr_head_step_external _ _ _ _ _ _ _ Hh Hh').
Qed.

Lemma lr_step_spawn_disjoint e m T e' m' c' c_new :
  lr_step e m T e' m' -> lr_spawn e c' c_new -> False.
Proof.
  intros [K1 e1 ?? e2 ? Hh] Hspawn. inversion Hspawn as [K2 e3 Heq]; subst.
  assert (Hr : redex_shape (Fork c_new)) by (intros Ki e0 Hk; destruct Ki; discriminate).
  destruct (fill_redex_unique K2 K1 (Fork c_new) e1 Hr (lr_head_step_redex_shape _ _ _ _ _ Hh)
              eq_refl (lr_head_step_not_val _ _ _ _ _ Hh) Heq) as [_ <-].
  inversion Hh.
Qed.

Lemma at_pure_step_sq (e1 e2 : sq_expr) :
  pure_step e1 e2 -> pure_step (Running e1 [] : lr_tstate) (Running e2 []).
Proof.
  intros [Hsafe Hdet]. split.
  - intros [m mu]. destruct (Hsafe m) as (e' & m' & efs & [Hs ->]%sq_prim_step_lr_step).
    do 3 eexists. by eapply AtTry.
  - intros [m mu] κ t2 σ2 efs Hs.
    destruct (Hsafe m) as (e' & m' & efs' & [Hs0 _]%sq_prim_step_lr_step).
    inversion Hs as [c ?? T c' m'' mu' Hstep Hrsv | c T ?? mu' Hne Hfin
      | c ly l v k ?? Hext | c ly l v ? k ?? Hext | c ly l ve vn vc ? k ?? Hext
      | c ly l ve vn vc k ?? Hext | c ly l ve vn vc k ?? Hext | c c' cn ?? Hspawn ]; subst;
      try done; try (exfalso; by eauto using lr_step_external_disjoint, lr_step_spawn_disjoint).
    destruct (Hdet m T c' m'' []) as (-> & -> & -> & _); [ by apply sq_prim_step_lr_step | ].
    simpl in Hrsv. injection Hrsv as <-. done.
Qed.

(** The pure steps of the sequential logic. *)
Global Instance at_pure_exec_sq φ n (e1 e2 : sq_expr) :
  PureExec φ n e1 e2 -> PureExec φ n (Running e1 [] : lr_tstate) (Running e2 []).
Proof.
  intros Hex Hφ. specialize (Hex Hφ).
  induction Hex as [ | n e1 e1' e2 Hs _ IH ]; [ constructor | ].
  econstructor; [ by apply at_pure_step_sq | done ].
Qed.

Local Hint Constructors lr_head_step sq_mem.bin_op_eval sq_mem.lit_eq lit_neq : core.

Ltac inv_lr_lit :=
  repeat match goal with
  | H : lr_val_eq _ (LitV _) (LitV _) |- _ => simpl in H
  | H : lr_val_neq _ (LitV _) (LitV _) |- _ => simpl in H
  | H : sq_mem.lit_eq _ ?x ?y |- _ => inversion H; clear H; simplify_map_eq/=
  | H : lit_neq ?x ?y |- _ => inversion H; clear H; simplify_map_eq/=
  | H : sq_mem.bin_op_eval _ ?c _ _ _ |- _ =>
      is_constructor c; inversion H; clear H; simplify_eq/=
  end.

(** The locations being deallocated by [Free n l]. *)
Definition lr_loc_set (l : loc) (n : nat) : gset loc := list_to_set (lr_locs l n).

Lemma elem_of_lr_loc_set l n l' : l' ∈ lr_loc_set l n <-> loc_in_range l n l'.
Proof.
  rewrite /lr_loc_set. revert l. induction n as [ | n IH ]; intros l.
  - rewrite /= elem_of_empty. destruct l, l'. rewrite /loc_in_range /=. lia.
  - rewrite /= elem_of_union elem_of_singleton IH.
    destruct l as [b o], l' as [b' o']. rewrite /loc_in_range /shift_loc /=.
    split; [ intros [[=-> ->] | [-> ?]]; lia | ].
    intros [-> ?]. destruct (decide (o' = o)) as [-> | ?]; [ by left | right; lia ].
Qed.

Lemma lr_locs_length l n : length (lr_locs l n) = n.
Proof. revert l. induction n; intros l; simpl; auto. Qed.

(** The number of pending reads of [l]. *)
Definition resv_count (R : gmap nat (loc * Qp * val)) (l : loc) : nat :=
  size (filter (fun kx : nat * (loc * Qp * val) => kx.2.1.1 = l) R).

Lemma resv_count_empty l : resv_count ∅ l = 0%nat.
Proof. by rewrite /resv_count map_filter_empty map_size_empty. Qed.

Lemma resv_count_insert R k x l :
  R !! k = None ->
  resv_count (<[k := x]> R) l = if decide (x.1.1 = l) then S (resv_count R l) else resv_count R l.
Proof.
  intros Hk. rewrite /resv_count. case_decide.
  - rewrite map_filter_insert_True // map_size_insert_None //.
    apply map_lookup_filter_None. by left.
  - by rewrite map_filter_insert_False // delete_id.
Qed.

Lemma resv_count_delete R k x l :
  R !! k = Some x ->
  resv_count R l = if decide (x.1.1 = l) then S (resv_count (delete k R) l) else resv_count (delete k R) l.
Proof.
  intros Hk. rewrite /resv_count map_filter_delete. case_decide.
  - assert (Hf : filter (fun kx : nat * (loc * Qp * val) => kx.2.1.1 = l) R !! k = Some x).
    { by apply map_lookup_filter_Some. }
    rewrite map_size_delete_Some; [ | by eexists ].
    assert (size (filter (fun kx : nat * (loc * Qp * val) => kx.2.1.1 = l) R) ≠ 0%nat).
    { apply (map_size_ne_0_lookup_2 _ k). by eexists. }
    lia.
  - rewrite delete_id //. apply map_lookup_filter_None. right. naive_solver.
Qed.

Lemma resv_count_pos R l :
  resv_count R l ≠ 0%nat -> exists k x, R !! k = Some x /\ x.1.1 = l.
Proof.
  rewrite /resv_count map_size_ne_0_lookup. intros (k & x & Hk%map_lookup_filter_Some). eauto.
Qed.


(** * Reservations

    A pending access keeps its points-to in the state interpretation from
    [Core_Try] to [Core_Commit]: a read the fraction it read with ([R], one
    entry per pending read), a write the location it wrote ([Wm]).  Pending
    deallocations, gone from the memory but still reserved, are recorded in
    [P].  Owning a points-to therefore tells the reservations of its location:
    a fraction rules out a pending write, the full points-to any pending
    access ([at_resv_frac], [at_resv_full]). *)
Definition at_resv_rel (m : lr_mem) (mu : rw_map) (R : gmap nat (loc * Qp * val))
    (Wm : gmap loc val) (P : gset loc) : Prop :=
  (forall l, match mu !! l with
     | Some (Rst n) => n = resv_count R l /\ Wm !! l = None
     | Some Wst => resv_count R l = 0%nat /\ is_Some (Wm !! l)
     | None => resv_count R l = 0%nat /\ Wm !! l = None /\ m !! l = None
     end) /\
  (forall l, l ∈ P -> m !! l = None /\ mu !! l = Some (Rst 0)).

Section resv_rel.
  Implicit Types (m : lr_mem) (mu : rw_map) (R : gmap nat (loc * Qp * val))
    (Wm : gmap loc val) (P : gset loc).

  Lemma resv_rel_read_try m mu R Wm P l n k x :
    at_resv_rel m mu R Wm P -> is_Some (m !! l) -> mu !! l = Some (Rst n) ->
    R !! k = None -> x.1.1 = l ->
    at_resv_rel m (<[l := Rst (S n)]> mu) (<[k := x]> R) Wm P.
  Proof.
    intros [Hrel HP] [v Hm] Hmu Hk Hx. split.
    - intros l'. specialize (Hrel l'). rewrite (resv_count_insert _ _ _ _ Hk).
      destruct (decide (l = l')) as [<- | Hne].
      + rewrite lookup_insert_eq decide_True // Hmu in Hrel |- *. naive_solver.
      + rewrite lookup_insert_ne // decide_False //. by rewrite Hx.
    - intros l' Hl'. destruct (HP l' Hl') as [Hm' Hmu']. rewrite lookup_insert_ne //.
      intros ->. congruence.
  Qed.

  Lemma resv_rel_read_commit m mu R Wm P k x :
    at_resv_rel m mu R Wm P -> R !! k = Some x ->
    exists n, mu !! x.1.1 = Some (Rst (S n)) /\
      at_resv_rel m (<[x.1.1 := Rst n]> mu) (delete k R) Wm P.
  Proof.
    intros [Hrel HP] Hk. pose proof (resv_count_delete _ _ _ x.1.1 Hk) as Hc.
    rewrite decide_True // in Hc. pose proof (Hrel x.1.1) as Hl.
    destruct (mu !! x.1.1) as [[n | ] | ] eqn:Hmu; [ | lia | lia ].
    destruct Hl as [-> HW]. exists (resv_count (delete k R) x.1.1). rewrite Hc.
    split; [ done | ]. split.
    - intros l'. specialize (Hrel l'). pose proof (resv_count_delete _ _ _ l' Hk) as Hc'.
      destruct (decide (x.1.1 = l')) as [<- | Hne].
      + by rewrite lookup_insert_eq.
      + rewrite lookup_insert_ne // -Hc'. done.
    - intros l' Hl'. destruct (HP l' Hl') as [Hm' Hmu']. rewrite lookup_insert_ne //.
      intros <-. congruence.
  Qed.

  Lemma resv_rel_write_try m mu R Wm P l v :
    at_resv_rel m mu R Wm P -> is_Some (m !! l) -> mu !! l = Some (Rst 0) ->
    at_resv_rel (<[l := v]> m) (<[l := Wst]> mu) R (<[l := v]> Wm) P.
  Proof.
    intros [Hrel HP] [w Hm] Hmu. split.
    - intros l'. specialize (Hrel l'). destruct (decide (l = l')) as [<- | Hne].
      + rewrite !lookup_insert_eq. rewrite Hmu in Hrel. naive_solver.
      + by rewrite !lookup_insert_ne.
    - intros l' Hl'. destruct (HP l' Hl') as [Hm' Hmu'].
      assert (l ≠ l') by (intros ->; congruence). by rewrite !lookup_insert_ne.
  Qed.

  Lemma resv_rel_write_commit m mu R Wm P l v :
    at_resv_rel m mu R Wm P -> Wm !! l = Some v ->
    mu !! l = Some Wst /\ at_resv_rel m (<[l := Rst 0]> mu) R (delete l Wm) P.
  Proof.
    intros [Hrel HP] HW. pose proof (Hrel l) as Hl.
    destruct (mu !! l) as [[n | ] | ] eqn:Hmu; [ naive_solver | | naive_solver ].
    destruct Hl as [Hc _]. split; [ done | ]. split.
    - intros l'. specialize (Hrel l'). destruct (decide (l = l')) as [<- | Hne].
      + by rewrite lookup_insert_eq lookup_delete_eq.
      + by rewrite lookup_insert_ne // lookup_delete_ne.
    - intros l' Hl'. destruct (HP l' Hl') as [Hm' Hmu'].
      assert (l ≠ l') by congruence. by rewrite lookup_insert_ne.
  Qed.

  Lemma resv_rel_store m mu R Wm P l v :
    at_resv_rel m mu R Wm P -> is_Some (m !! l) -> at_resv_rel (<[l := v]> m) mu R Wm P.
  Proof.
    intros [Hrel HP] [w Hm]. split.
    - intros l'. specialize (Hrel l'). destruct (mu !! l') as [[] | ]; try done.
      destruct Hrel as (? & ? & Hm'). split_and!; [ done | done | ].
      rewrite lookup_insert_ne //. intros ->. congruence.
    - intros l' Hl'. destruct (HP l' Hl') as [Hm' Hmu'].
      assert (l ≠ l') by (intros ->; congruence). by rewrite lookup_insert_ne.
  Qed.

  Lemma resv_rel_alloc m mu R Wm P l n :
    at_resv_rel m mu R Wm P -> (forall z, m !! (l +ₗ z) = None) ->
    (forall z, (0 <= z < Z.of_nat n)%Z -> mu !! (l +ₗ z) = None) ->
    at_resv_rel (alloc_gmap (LitV LitPoison) l n m) (alloc_gmap (Rst 0) l n mu) R Wm P.
  Proof.
    intros [Hrel HP] Hm Hmu. split.
    - intros l'. specialize (Hrel l'). rewrite !sq_mem_lookup_init_mem.
      case_decide as Hin; [ | done ].
      destruct (loc_in_range_shift_range _ _ _ Hin) as (z & Hz & ->).
      rewrite Hmu in Hrel; [ naive_solver | done ].
    - intros l' Hl'. destruct (HP l' Hl') as [Hm' Hmu']. rewrite !sq_mem_lookup_init_mem.
      case_decide as Hin; [ | done ].
      destruct (loc_in_range_shift_range _ _ _ Hin) as (z & Hz & ->).
      rewrite Hmu in Hmu'; [ done | done ].
  Qed.

  Lemma resv_rel_free m mu R Wm P l n :
    at_resv_rel m mu R Wm P ->
    (forall z, (0 <= z < Z.of_nat n)%Z ->
       is_Some (m !! (l +ₗ z)) /\ mu !! (l +ₗ z) = Some (Rst 0)) ->
    lr_loc_set l n ## P /\
    at_resv_rel (free_gmap l n m) mu R Wm (lr_loc_set l n ∪ P).
  Proof.
    intros [Hrel HP] Hin.
    assert (Hin' : forall l', loc_in_range l n l' ->
              is_Some (m !! l') /\ mu !! l' = Some (Rst 0)).
    { intros l' Hl. destruct (loc_in_range_shift_range _ _ _ Hl) as (z & Hz & ->). by apply Hin. }
    split; [ | split ].
    - intros l' Hl1%elem_of_lr_loc_set Hl2. destruct (Hin' l' Hl1) as [[v Hm] _].
      destruct (HP l' Hl2) as [Hm' _]. congruence.
    - intros l'. specialize (Hrel l'). rewrite sq_mem_lookup_free_mem.
      destruct (mu !! l') as [[] | ]; try done. destruct Hrel as (? & ? & Hm').
      rewrite Hm'. by case_decide.
    - intros l' [Hl%elem_of_lr_loc_set | Hl]%elem_of_union.
      + rewrite sq_mem_lookup_free_mem decide_True //. split; [ done | apply Hin', Hl ].
      + destruct (HP l' Hl) as [Hm Hmu]. rewrite sq_mem_lookup_free_mem Hm.
        split; [ by case_decide | done ].
  Qed.

  Lemma resv_rel_free_commit m mu R Wm P l n :
    at_resv_rel m mu R Wm P -> lr_loc_set l n ⊆ P ->
    (forall z, (0 <= z < Z.of_nat n)%Z -> is_Some (mu !! (l +ₗ z))) /\
    at_resv_rel m (free_gmap l n mu) R Wm (P ∖ lr_loc_set l n).
  Proof.
    intros [Hrel HP] Hsub. split; [ | split ].
    - intros z Hz. destruct (HP (l +ₗ z)) as [_ ->]; [ | eauto ].
      apply Hsub, elem_of_lr_loc_set. destruct l as [b o].
      rewrite /loc_in_range /shift_loc /=. lia.
    - intros l'. specialize (Hrel l'). rewrite sq_mem_lookup_free_mem.
      case_decide as Hl; [ | done ].
      apply elem_of_lr_loc_set, Hsub, HP in Hl as [Hm Hmu]. rewrite Hmu in Hrel. naive_solver.
    - intros l' [Hl Hnot]%elem_of_difference. rewrite elem_of_lr_loc_set in Hnot.
      rewrite sq_mem_lookup_free_mem decide_False //. by apply HP.
  Qed.
End resv_rel.

(** * The state interpretation *)

Class lrAtGS Σ := LrAtGS {
  lrAtGS_sqGS :: lrSqGS Σ;
  lrAtGS_readsG :: ghost_mapG Σ nat (loc * Qp * val);
  lrAtGS_writesG :: ghost_mapG Σ loc val;
  lrAtGS_freesG :: inG Σ (authR (gset_disjUR loc));
  lrAtGS_reads_name : gname;
  lrAtGS_writes_name : gname;
  lrAtGS_frees_name : gname
}.

Section state_interp.
  Context `{!lrAtGS Σ}.

  Definition at_resv (m : lr_mem) (mu : rw_map) : iProp Σ :=
    ∃ (R : gmap nat (loc * Qp * val)) (Wm : gmap loc val) (P : gset loc),
      (** A pending na-read (i.e. Core_Try'ed but not Core_Commit'ed) of
      [l {q}↦ v] adds an entry [k ↦ (l, q, v)] to [R], where [k] is a fresh 
      key; the threoad gets the frag piece [k ↪[lrAtGS_reads_name] (l, q, v)].
      The points-to [l {q}↦ v] is also transferred to [at_resv].
      
      When the thread commits, it turns in [k ↪[lrAtGS_reads_name] (l, q, v)],
      removes the entry from [R], and takes [l {q}↦ v] back.
      
      The [lrAtGS_reads_name] ghost state only appears between Try and Commit,
      does not appear in the proof rule's logic level, and the model for the
      points-to is exactly the same as lambda-rust's. *)
      ghost_map_auth lrAtGS_reads_name 1 R ∗ ([∗ map] x ∈ R, x.1.1 ↦{x.1.2} x.2) ∗
      (* Similarly, a pending write adds the write location and value to [Wm]
      and keeps the points-to until commit. *)
      ghost_map_auth lrAtGS_writes_name 1 Wm ∗ ([∗ map] l ↦ v ∈ Wm, l ↦ v) ∗
      (* [P] records a set of freed locations. *)
      own lrAtGS_frees_name (● GSet P) ∗
      (* An invariant that ties [rw_map] to the ghost states above. *)
       ⌜at_resv_rel m mu R Wm P⌝.

  (** The sequential state interpretation plus the ghosts for the reservations. *)
  Definition at_si (m : lr_mem) (mu : rw_map) : iProp Σ :=
    heap_ctx (sq_heap m) ∗ at_resv m mu.
End state_interp.

Global Instance lrAtGS_irisGS `{!lrAtGS Σ} : irisGS at_lang Σ := {
  iris_invGS := lrSqGS_invGS;
  state_interp σ _ _ _ := at_si σ.1 σ.2;
  fork_post _ := True%I;
  num_laters_per_step _ := 0%nat;
  state_interp_mono _ _ _ _ := fupd_intro _ _
}.

Section resv.
  Context `{!lrAtGS Σ}.

  Lemma heap_pointsto_excl' l q v w : l ↦ v ∗ l ↦{q} w ⊢ ⌜False⌝.
  Proof.
    rewrite heap_pointsto_eq -own_op -auth_frag_op own_valid internal_cmra_valid_discrete.
    eapply bi.pure_elim; [done|]=> /auth_frag_valid /=.
    rewrite singleton_op -pair_op singleton_valid=> -[[Hq _] _].
    by apply (exclusive_l 1%Qp q) in Hq.
  Qed.

  Lemma heap_pointsto_excl l q v w : l ↦ v -∗ l ↦{q} w -∗ False.
  Proof. iIntros "H1 H2". by iDestruct (heap_pointsto_excl' with "[$H1 $H2]") as %[]. Qed.

  Lemma at_resv_frac m mu l q v :
    heap_ctx (sq_heap m) -∗ at_resv m mu -∗ l ↦{q} v -∗
    ⌜m !! l = Some v /\ exists n, mu !! l = Some (Rst n)⌝.
  Proof.
    iIntros "Hσ (%R & %Wm & %P & HR & HRd & HW & HWd & HP & %Hrel) Hv".
    iDestruct (heap_read with "Hσ Hv") as %[? [_ Hm]%lookup_sq_heap_Some].
    pose proof (proj1 Hrel l) as Hl. destruct (mu !! l) as [[n | ] | ] eqn:Hmu.
    - eauto.
    - destruct Hl as [_ [w Hw]]. iDestruct (big_sepM_lookup with "HWd") as "Hw"; [ done | ].
      iDestruct (heap_pointsto_excl with "Hw Hv") as %[].
    - destruct Hl as (_ & _ & Hm'). congruence.
  Qed.

  Lemma at_resv_full m mu l v :
    heap_ctx (sq_heap m) -∗ at_resv m mu -∗ l ↦ v -∗
    ⌜m !! l = Some v /\ mu !! l = Some (Rst 0)⌝.
  Proof.
    iIntros "Hσ (%R & %Wm & %P & HR & HRd & HW & HWd & HP & %Hrel) Hv".
    iDestruct (heap_read_1 with "Hσ Hv") as %[_ Hm]%lookup_sq_heap_Some.
    pose proof (proj1 Hrel l) as Hl. destruct (mu !! l) as [[[ | n] | ] | ] eqn:Hmu.
    - done.
    - destruct Hl as [Hc _]. destruct (resv_count_pos R l) as (k & x & Hk & <-); [ lia | ].
      iDestruct (big_sepM_lookup with "HRd") as "Hx"; [ done | ].
      iDestruct (heap_pointsto_excl with "Hv Hx") as %[].
    - destruct Hl as [_ [w Hw]]. iDestruct (big_sepM_lookup with "HWd") as "Hw"; [ done | ].
      iDestruct (heap_pointsto_excl with "Hw Hv") as %[].
    - destruct Hl as (_ & _ & Hm'). congruence.
  Qed.

  Lemma at_resv_full_vec m mu l vl :
    heap_ctx (sq_heap m) -∗ at_resv m mu -∗ l ↦∗ vl -∗
    ⌜forall z, (0 <= z < Z.of_nat (length vl))%Z ->
       is_Some (m !! (l +ₗ z)) /\ mu !! (l +ₗ z) = Some (Rst 0)⌝.
  Proof.
    iIntros "Hσ Hr Hvl". iInduction vl as [ | v vl IH ] forall (l).
    { iPureIntro. simpl. lia. }
    rewrite heap_pointsto_vec_cons. iDestruct "Hvl" as "[Hv Hvl]".
    iDestruct (at_resv_full with "Hσ Hr Hv") as %[Hm Hmu].
    iDestruct ("IH" with "Hσ Hr Hvl") as %Hvl.
    iPureIntro. intros z Hz. destruct (decide (z = 0%Z)) as [-> | Hne].
    - rewrite shift_loc_0. eauto.
    - destruct (Hvl (z - 1)%Z) as [Hm' Hmu']; [ simpl in Hz; lia | ].
      rewrite shift_loc_assoc Z.add_sub_assoc Z.add_simpl_l in Hm' Hmu'. done.
  Qed.

  Lemma at_resv_read_try m mu l n q v :
    is_Some (m !! l) -> mu !! l = Some (Rst n) ->
    at_resv m mu -∗ l ↦{q} v ==∗
    ∃ k, at_resv m (<[l := Rst (S n)]> mu) ∗ k ↪[lrAtGS_reads_name] (l, q, v).
  Proof.
    iIntros (Hm Hmu) "(%R & %Wm & %P & HR & HRd & HW & HWd & HP & %Hrel) Hv".
    pose proof (is_fresh (dom R)) as Hk%not_elem_of_dom.
    iMod (ghost_map_insert _ (l, q, v) Hk with "HR") as "[HR Hk]".
    iModIntro. iExists _. iFrame "Hk". iExists _, Wm, P. iFrame.
    iSplitL. { iApply big_sepM_insert; [ done | ]. iFrame. }
    iPureIntro. by eapply resv_rel_read_try.
  Qed.

  Lemma at_resv_read_commit m mu k l q v :
    at_resv m mu -∗ k ↪[lrAtGS_reads_name] (l, q, v) ==∗
    ∃ n, ⌜mu !! l = Some (Rst (S n))⌝ ∗ at_resv m (<[l := Rst n]> mu) ∗ l ↦{q} v.
  Proof.
    iIntros "(%R & %Wm & %P & HR & HRd & HW & HWd & HP & %Hrel) Hk".
    iDestruct (ghost_map_lookup with "HR Hk") as %Hk.
    destruct (resv_rel_read_commit _ _ _ _ _ _ _ Hrel Hk) as (n & Hmu & Hrel').
    iMod (ghost_map_delete with "HR Hk") as "HR".
    iDestruct (big_sepM_delete with "HRd") as "[Hv HRd]"; [ done | ].
    iModIntro. iExists n. iSplit; [ done | ]. iFrame. done.
  Qed.

  Lemma at_resv_write_try m mu l v :
    is_Some (m !! l) -> mu !! l = Some (Rst 0) ->
    at_resv m mu -∗ l ↦ v ==∗
    at_resv (<[l := v]> m) (<[l := Wst]> mu) ∗ l ↪[lrAtGS_writes_name] v.
  Proof.
    iIntros (Hm Hmu) "(%R & %Wm & %P & HR & HRd & HW & HWd & HP & %Hrel) Hv".
    assert (HW : Wm !! l = None).
    { pose proof (proj1 Hrel l) as Hl. rewrite Hmu in Hl. naive_solver. }
    iMod (ghost_map_insert l v HW with "HW") as "[HW Hw]".
    iModIntro. iFrame "Hw". iExists R, _, P. iFrame.
    iSplitL. { iApply big_sepM_insert; [ done | ]. iFrame. }
    iPureIntro. by apply resv_rel_write_try.
  Qed.

  Lemma at_resv_write_commit m mu l v :
    at_resv m mu -∗ l ↪[lrAtGS_writes_name] v ==∗
    ⌜mu !! l = Some Wst⌝ ∗ at_resv m (<[l := Rst 0]> mu) ∗ l ↦ v.
  Proof.
    iIntros "(%R & %Wm & %P & HR & HRd & HW & HWd & HP & %Hrel) Hw".
    iDestruct (ghost_map_lookup with "HW Hw") as %HW.
    destruct (resv_rel_write_commit _ _ _ _ _ _ _ Hrel HW) as [Hmu Hrel'].
    iMod (ghost_map_delete with "HW Hw") as "HW".
    iDestruct (big_sepM_delete with "HWd") as "[Hv HWd]"; [ done | ].
    iModIntro. iSplit; [ done | ]. iFrame. done.
  Qed.

  Lemma at_resv_store m mu l v :
    is_Some (m !! l) -> at_resv m mu -∗ at_resv (<[l := v]> m) mu.
  Proof.
    iIntros (Hm) "(%R & %Wm & %P & HR & HRd & HW & HWd & HP & %Hrel)".
    iFrame. iPureIntro. by apply resv_rel_store.
  Qed.

  Lemma at_resv_alloc m mu l n :
    (forall z, m !! (l +ₗ z) = None) ->
    (forall z, (0 <= z < Z.of_nat n)%Z -> mu !! (l +ₗ z) = None) ->
    at_resv m mu -∗ at_resv (alloc_gmap (LitV LitPoison) l n m) (alloc_gmap (Rst 0) l n mu).
  Proof.
    iIntros (Hm Hmu) "(%R & %Wm & %P & HR & HRd & HW & HWd & HP & %Hrel)".
    iFrame. iPureIntro. by apply resv_rel_alloc.
  Qed.

  Lemma at_resv_free_try m mu l n :
    (forall z, (0 <= z < Z.of_nat n)%Z ->
       is_Some (m !! (l +ₗ z)) /\ mu !! (l +ₗ z) = Some (Rst 0)) ->
    at_resv m mu ==∗
    at_resv (free_gmap l n m) mu ∗ own lrAtGS_frees_name (◯ GSet (lr_loc_set l n)).
  Proof.
    iIntros (Hin) "(%R & %Wm & %P & HR & HRd & HW & HWd & HP & %Hrel)".
    destruct (resv_rel_free _ _ _ _ _ _ _ Hrel Hin) as [Hdisj Hrel'].
    iMod (own_update with "HP") as "[HP Hfr]".
    { by apply auth_update_alloc, (gset_disj_alloc_empty_local_update _ (lr_loc_set l n)). }
    iModIntro. iFrame "Hfr". iFrame. done.
  Qed.

  Lemma at_resv_free_commit m mu l n :
    at_resv m mu -∗ own lrAtGS_frees_name (◯ GSet (lr_loc_set l n)) ==∗
    ⌜forall z, (0 <= z < Z.of_nat n)%Z -> is_Some (mu !! (l +ₗ z))⌝ ∗
    at_resv m (free_gmap l n mu).
  Proof.
    iIntros "(%R & %Wm & %P & HR & HRd & HW & HWd & HP & %Hrel) Hfr".
    iCombine "HP Hfr" gives %[Hsub%gset_disj_included _]%auth_both_valid_discrete.
    destruct (resv_rel_free_commit _ _ _ _ _ _ _ Hrel Hsub) as [Hsome Hrel'].
    iMod (own_update_2 with "HP Hfr") as "HP".
    { apply auth_update_dealloc, gset_disj_dealloc_local_update. }
    iModIntro. iSplit; [ done | ]. iFrame. done.
  Qed.
End resv.

(** * Inverting the steps of a thread at a redex *)

Lemma lr_head_step_step e m T e' m' : lr_head_step e m T e' m' -> lr_step e m T e' m'.
Proof. exact (LREctxStep [] e m T e' m'). Qed.

Lemma lr_head_external_external e op k : lr_head_external e op k -> lr_external e op k.
Proof. exact (LREctxExternal [] e op k). Qed.

Ltac solve_redex_shape :=
  let Ki := fresh "Ki" in let e' := fresh "e'" in let Heq := fresh "Heq" in
  intros Ki e' Heq; destruct Ki; simpl in Heq; simplify_eq; rewrite /= ?to_of_val; by eauto.

Ltac inv_at_step :=
  repeat match goal with
  | H : ?x ≠ ?x |- _ => by destruct H
  | H : to_val (of_val _) = Some _ |- _ => rewrite to_of_val in H; simplify_eq
  | H : to_val (Lit _) = Some _ |- _ => simpl in H; simplify_eq
  | H : at_prim_step _ _ _ _ _ _ |- _ => inversion H; clear H; subst
  | H : lr_step ?e _ _ _ _ |- _ =>
      try (is_var e; fail 1); apply lr_step_head in H; [ | solve_redex_shape ]
  | H : lr_external ?e _ _ |- _ =>
      try (is_var e; fail 1); apply lr_external_head in H; [ | solve_redex_shape ]
  | H : lr_spawn ?e _ _ |- _ =>
      try (is_var e; fail 1); apply lr_spawn_head in H as [? ?]; [ simplify_eq | solve_redex_shape ]
  | H : lr_head_step ?e _ _ _ _ |- _ =>
      try (is_var e; fail 1); inversion H; clear H; subst
  | H : lr_head_external ?e _ _ |- _ =>
      try (is_var e; fail 1); inversion H; clear H; subst
  end.

Section step_inv.
  Implicit Types (m : lr_mem) (mu : rw_map) (κ : list at_obs) (t : lr_tstate)
    (σ : at_state) (efs : list lr_tstate).

  Lemma at_step_commit_inv e T m mu κ t2 σ2 efs :
    T ≠ [] -> at_prim_step (Running e T) (m, mu) κ t2 σ2 efs ->
    exists mu', κ = [] /\ efs = [] /\ atomic_machine.fin T mu = Some mu' /\
      t2 = Running e [] /\ σ2 = (m, mu').
  Proof. intros HT Hs. inversion Hs; subst; try by destruct HT. eauto 10. Qed.

  Lemma at_step_read_na_inv l m mu κ t2 σ2 efs :
    at_prim_step (Running (Read Na1Ord (Lit (LitLoc l))) []) (m, mu) κ t2 σ2 efs ->
    exists v mu', κ = [] /\ efs = [] /\ m !! l = Some v /\
      rsv [lr_read_event l] mu = Some mu' /\
      t2 = Running (of_val v) [lr_read_event l] /\ σ2 = (m, mu').
  Proof. intros Hs. inv_at_step. eauto 10. Qed.

  Lemma at_step_write_na_inv l v m mu κ t2 σ2 efs :
    at_prim_step (Running (Write Na1Ord (Lit (LitLoc l)) (of_val v)) []) (m, mu) κ t2 σ2 efs ->
    exists v' mu', κ = [] /\ efs = [] /\ m !! l = Some v' /\
      rsv [lr_write_event l] mu = Some mu' /\
      t2 = Running (Lit LitPoison) [lr_write_event l] /\ σ2 = (<[l := v]> m, mu').
  Proof. intros Hs. inv_at_step. eauto 10. Qed.

  Lemma at_step_alloc_inv n m mu κ t2 σ2 efs :
    at_prim_step (Running (Alloc (Lit (LitInt n))) []) (m, mu) κ t2 σ2 efs ->
    exists l mu', κ = [] /\ efs = [] /\ (forall z, m !! (l +ₗ z) = None) /\
      rsv (lr_alloc_events l (Z.to_nat n)) mu = Some mu' /\
      t2 = Running (Lit (LitLoc l)) (lr_alloc_events l (Z.to_nat n)) /\
      σ2 = (alloc_gmap (LitV LitPoison) l (Z.to_nat n) m, mu').
  Proof. intros Hs. inv_at_step. eauto 10. Qed.

  Lemma at_step_free_inv n l m mu κ t2 σ2 efs :
    at_prim_step (Running (Free (Lit (LitInt n)) (Lit (LitLoc l))) []) (m, mu) κ t2 σ2 efs ->
    exists mu', κ = [] /\ efs = [] /\
      rsv (lr_free_events l (Z.to_nat n)) mu = Some mu' /\
      t2 = Running (Lit LitPoison) (lr_free_events l (Z.to_nat n)) /\
      σ2 = (free_gmap l (Z.to_nat n) m, mu').
  Proof. intros Hs. inv_at_step. eauto 10. Qed.

  Lemma at_step_read_sc_inv l m mu κ t2 σ2 efs :
    at_prim_step (Running (Read ScOrd (Lit (LitLoc l))) []) (m, mu) κ t2 σ2 efs ->
    exists v, κ = [] /\ efs = [] /\ m !! l = Some v /\
      t2 = Running (of_val v) [] /\ σ2 = (m, mu).
  Proof. intros Hs. inv_at_step. eauto 10. Qed.

  Lemma at_step_write_sc_inv l v m mu κ t2 σ2 efs :
    at_prim_step (Running (Write ScOrd (Lit (LitLoc l)) (of_val v)) []) (m, mu) κ t2 σ2 efs ->
    κ = [] /\ efs = [] /\ t2 = Running (Lit LitPoison) [] /\ σ2 = (<[l := v]> m, mu).
  Proof.
    intros Hs. inv_at_step. match goal with H : store _ _ _ _ = Some _ |- _ => revert H end.
    rewrite /=. case_match; naive_solver.
  Qed.

  Lemma at_step_cas_inv l lit1 lit2 m mu κ t2 σ2 efs :
    at_prim_step (Running (CAS (Lit (LitLoc l)) (Lit lit1) (Lit lit2)) []) (m, mu) κ t2 σ2 efs ->
    κ = [] /\ efs = [] /\ exists v_cur, m !! l = Some v_cur /\
      ((lr_val_eq m v_cur (LitV lit1) /\ mu !! l = Some (Rst 0) /\
         t2 = Running (Lit (lit_of_bool true)) [] /\ σ2 = (<[l := LitV lit2]> m, mu)) \/
       (lr_val_neq m v_cur (LitV lit1) /\
         t2 = Running (Lit (lit_of_bool false)) [] /\ σ2 = (m, mu)) \/
       (lr_val_eq m v_cur (LitV lit1) /\ mu !! l ≠ Some (Rst 0) /\
         t2 = StuckState /\ σ2 = (m, mu))).
  Proof.
    intros Hs. inv_at_step; (do 2 (split; [ done | ])).
    - match goal with Hl : load _ _ _ = Some _, Hs : store _ _ _ _ = Some _ |- _ =>
        simpl in Hl, Hs; rewrite Hl in Hs; injection Hs as <- end.
      match goal with H : writable _ _ |- _ => rewrite /writable /= Forall_singleton in H end.
      eexists. split; [ done | ]. left. eauto.
    - eexists. split; [ done | ]. right. left. eauto.
    - eexists. split; [ done | ]. right. right. split; [ done | ]. split; [ | done ].
      match goal with H : ¬ writable _ _ |- _ =>
        intros Hmu; apply H; by rewrite /writable /= Forall_singleton end.
  Qed.

  Lemma lr_step_free_inv n l m T e' m' :
    lr_step (Free (Lit (LitInt n)) (Lit (LitLoc l))) m T e' m' ->
    (0 < n)%Z /\ (forall z, is_Some (m !! (l +ₗ z)) <-> (0 <= z < n)%Z).
  Proof. intros Hs. inv_at_step. eauto. Qed.

  Lemma at_step_fork_inv e m mu κ t2 σ2 efs :
    at_prim_step (Running (Fork e) []) (m, mu) κ t2 σ2 efs ->
    κ = [] /\ efs = [Running e []] /\ t2 = Running (Lit LitPoison) [] /\ σ2 = (m, mu).
  Proof. intros Hs. inv_at_step. eauto. Qed.
End step_inv.

(** * Running the sequential logic for a [Core_Try] step

    A [Core_Try] step is a step of [sq_lang] on the sequential part of the
    state interpretation.  [sq_wp_try] runs a [WP] of the sequential logic
    for a step whose events [T] are known beforehand, and also yields that the
    expression can step; [sq_wp_step] runs it once the step is known, for an
    allocation, whose events depend on the location the machine picks. *)

Section sq_step.
  Context `{!lrAtGS Σ}.

  Lemma sq_wp_try E (e : sq_expr) (Ψ : sq_val -> iProp Σ) m T :
    to_val e = None ->
    WP e @ E {{ Ψ }} -∗ heap_ctx (sq_heap m) ={E,∅}=∗
    ⌜exists T' e' m', lr_step e m T' e' m'⌝ ∗
    ∀ (e' : sq_expr) m', ⌜lr_step e m T e' m'⌝ -∗ £ 1 ={∅}=∗ ▷ |={∅,E}=>
      heap_ctx (sq_heap m') ∗ WP e' @ E {{ Ψ }}.
  Proof.
    iIntros (Hv) "Hwp Hσ". rewrite wp_unfold /wp_pre /= Hv.
    iMod ("Hwp" $! m 0%nat T [] 0%nat with "Hσ") as "[%Hred Hstep]".
    iModIntro. iSplit.
    { iPureIntro. destruct Hred as (κ & e' & m' & efs & [Hs _]%sq_prim_step_lr_step). eauto. }
    iIntros (e' m' Hs) "Hc".
    iMod ("Hstep" $! e' m' [] with "[%] Hc") as "Hstep"; [ by apply sq_prim_step_lr_step | ].
    iModIntro. iNext. iMod "Hstep". iMod "Hstep" as "(Hσ & Hwp & _)". iModIntro. iFrame.
  Qed.

  Lemma sq_wp_value_inv E (v : sq_val) (Ψ : sq_val -> iProp Σ) :
    WP (of_val v : sq_expr) @ E {{ Ψ }} ={E}=∗ Ψ v.
  Proof. rewrite wp_value_fupd'. auto. Qed.

  Lemma sq_wp_step E (e : sq_expr) (Ψ : sq_val -> iProp Σ) m T (e' : sq_expr) m' :
    lr_step e m T e' m' ->
    WP e @ E {{ Ψ }} -∗ heap_ctx (sq_heap m) -∗ £ 1 ={E,∅}=∗ ▷ |={∅,E}=>
      heap_ctx (sq_heap m') ∗ WP e' @ E {{ Ψ }}.
  Proof.
    iIntros (Hs) "Hwp Hσ Hc".
    iMod (sq_wp_try _ _ _ _ T with "Hwp Hσ") as "[_ Hstep]"; [ by eapply lr_step_not_val | ].
    by iMod ("Hstep" with "[%] Hc").
  Qed.
End sq_step.

(** * The rules *)

Section lifting.
Context `{!lrAtGS Σ}.
Implicit Types P Q : iProp Σ.

(** Binding: [at_fill K] is an evaluation context of [at_lang]. *)
Lemma at_wp_bind K E e (Φ : at_val -> iProp Σ) :
  WP Running e [] @ E {{ λ v : at_val, WP Running (fill K (of_val v)) [] @ E {{ Φ }} }} ⊢
  WP Running (fill K e) [] @ E {{ Φ }}.
Proof. exact (wp_bind (at_fill K) _ E (Running e []) Φ). Qed.

(** [Core_Commit] for a thread whose expression is a value. *)
Lemma at_wp_commit E e T v (Φ : at_val -> iProp Σ) :
  T ≠ [] -> to_val e = Some v ->
  (∀ m mu, at_resv m mu ={E}=∗
     ∃ mu', ⌜atomic_machine.fin T mu = Some mu'⌝ ∗ at_resv m mu' ∗ Φ v) -∗
  WP Running e T @ E {{ Φ }}.
Proof.
  iIntros (HT Hv) "H". iApply wp_lift_atomic_step; [ destruct T; [ by destruct HT | done ] | ].
  iIntros ([m mu] ns κ κs nt) "[Hσ Hr]". iMod ("H" with "Hr") as (mu' Hfin) "[Hr HΦ]".
  iModIntro. iSplit; [ iPureIntro; do 4 eexists; by eapply AtCommit | ].
  iNext. iIntros (t2 σ2 efs Hstep) "_".
  destruct (at_step_commit_inv _ _ _ _ _ _ _ _ HT Hstep) as (mu3 & -> & -> & Hfin' & -> & ->).
  rewrite Hfin in Hfin'. injection Hfin' as <-.
  iModIntro. iFrame. iSplitL; [ | done ]. by rewrite /= Hv.
Qed.

(** A sequential step without events, to a value: a [Core_Try] step with
    nothing to reserve or commit. *)
Lemma at_wp_sq_value E (e : sq_expr) (Φ : at_val -> iProp Σ) :
  to_val e = None ->
  (forall m T e' m', lr_step e m T e' m' -> T = [] /\ m' = m /\ is_Some (to_val e')) ->
  WP e @ E {{ λ v : sq_val, Φ v }} ⊢ WP Running e [] @ E {{ Φ }}.
Proof.
  iIntros (Hv Hval) "Hwp". iApply wp_lift_step_fupd; [ done | ].
  iIntros ([m mu] ns κ κs nt) "[Hσ Hr]".
  iMod (sq_wp_try _ _ _ m [] with "Hwp Hσ") as "[%Hred Hstep]"; [ done | ].
  destruct Hred as (T' & e' & m' & Hs). destruct (Hval _ _ _ _ Hs) as (-> & -> & _).
  iModIntro. iSplit; [ iPureIntro; do 4 eexists; by eapply AtTry | ].
  iIntros (t2 σ2 efs Hat) "Hc".
  inversion Hat as [c ?? T c' m'' mu' Hs' Hrsv | c T ?? mu' Hne Hfin
      | c ly l v k ?? Hext | c ly l v ? k ?? Hext | c ly l ve vn vc ? k ?? Hext
      | c ly l ve vn vc k ?? Hext | c ly l ve vn vc k ?? Hext | c c' cn ?? Hspawn ]; subst;
    try done; try (exfalso; by eauto using lr_step_external_disjoint, lr_step_spawn_disjoint).
  destruct (Hval _ _ _ _ Hs') as (-> & -> & [v Hv']). apply of_to_val in Hv' as <-.
  simpl in Hrsv. injection Hrsv as <-.
  iMod ("Hstep" with "[%] Hc") as "Hstep"; [ done | ].
  iModIntro. iNext. iMod "Hstep" as "[Hσ Hwp]". iMod (sq_wp_value_inv with "Hwp") as "HΦ".
  iModIntro. iSplitL "Hσ Hr"; [ iFrame | ]. iSplitL; [ | done ]. by iApply wp_value'.
Qed.

Lemma at_wp_fork E e :
  {{{ ▷ WP Running e [] {{ _, True }} }}} Running (Fork e) [] @ E
  {{{ RET (LitV LitPoison : at_val); True }}}.
Proof.
  iIntros (Φ) "He HΦ". iApply wp_lift_atomic_step; [ done | ].
  iIntros ([m mu] ns κ κs nt) "Hsi". iModIntro. iSplit.
  { iPureIntro. do 4 eexists. by apply AtSpawn, (LRSpawn []). }
  iNext. iIntros (t2 σ2 efs Hstep) "_".
  destruct (at_step_fork_inv _ _ _ _ _ _ _ Hstep) as (-> & -> & -> & ->).
  iModIntro. iFrame "Hsi". iSplitL "HΦ"; [ by iApply "HΦ" | ]. by iFrame.
Qed.

(** ** Non-atomic operations: the rules of the sequential logic, plus the
    reservations *)

Lemma at_wp_alloc E (n : Z) :
  0 < n ->
  {{{ True }}} Running (Alloc (Lit $ LitInt n)) [] @ E
  {{{ l (sz: nat), RET (LitV $ LitLoc l : at_val);
      ⌜n = sz⌝ ∗ †l…sz ∗ l ↦∗ repeat (LitV LitPoison) sz }}}.
Proof.
  iIntros (Hn Φ) "_ HΦ". iApply wp_lift_step_fupd; [ done | ].
  iIntros ([m mu] ns κ κs nt) "[Hσ Hr]".
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iSplit.
  { iPureIntro. destruct (lr_fresh_block m mu) as [l Hl].
    do 4 eexists. eapply AtTry; [ apply lr_head_step_step, LRAllocS; [ done | apply Hl ] | ].
    apply lr_rsv_alloc_events, Hl. }
  iIntros (t2 σ2 efs Hstep) "Hc". iMod "Hclose" as "_".
  destruct (at_step_alloc_inv _ _ _ _ _ _ _ Hstep)
    as (l & mu' & -> & -> & Hfresh & Hrsv & -> & ->).
  apply lr_rsv_alloc_events_inv in Hrsv as [-> Hmu].
  iMod (sq_wp_step _ _ (fun r => ∃ (l' : loc) (sz : nat), ⌜r = LitV (LitLoc l')⌝ ∗
          ⌜n = sz⌝ ∗ †l'…sz ∗ l' ↦∗ repeat (LitV LitPoison) sz)%I with "[] Hσ Hc") as "Hstep".
  { apply lr_head_step_step. by apply LRAllocS. }
  { iApply (sq_wp_alloc with "[//]"); [ done | ]. iIntros "!>" (l' sz) "H".
    iExists l', sz. iSplit; [ done | iExact "H" ]. }
  iModIntro. iNext. iMod "Hstep" as "[Hσ Hwp]".
  iMod (sq_wp_value_inv _ (LitV (LitLoc l)) with "Hwp") as (l' sz Heq Hsz) "[Hf Hl]".
  injection Heq as <-.
  iModIntro. iSplitL "Hσ Hr".
  { iFrame "Hσ". iApply (at_resv_alloc with "Hr"); [ done | done ]. }
  iSplitL; [ | done ].
  assert (Hne : lr_alloc_events l (Z.to_nat n) ≠ []).
  { rewrite -length_zero_iff_nil length_map lr_locs_length. lia. }
  iApply (at_wp_commit _ _ _ (LitV (LitLoc l)) with "[Hf Hl HΦ]"); [ done | done | ].
  iIntros (m2 mu2) "Hr". iModIntro. iExists mu2. iFrame "Hr".
  iSplit; [ by rewrite lr_fin_alloc_events | ]. iApply ("HΦ" $! l sz). iFrame. by iPureIntro.
Qed.

Lemma at_wp_free E (n:Z) l vl :
  n = length vl ->
  {{{ ▷ l ↦∗ vl ∗ ▷ †l…(length vl) }}}
    Running (Free (Lit $ LitInt n) (Lit $ LitLoc l)) [] @ E
  {{{ RET (LitV LitPoison : at_val); True }}}.
Proof.
  iIntros (Hn Φ) "[>Hmt >Hf] HΦ". iApply wp_lift_step_fupd; [ done | ].
  iIntros ([m mu] ns κ κs nt) "[Hσ Hr]".
  iDestruct (at_resv_full_vec with "Hσ Hr Hmt") as %Hvl.
  iMod (sq_wp_try _ (Free (Lit $ LitInt n) (Lit $ LitLoc l)) (fun _ => True)%I m
          (lr_free_events l (Z.to_nat n)) with "[Hmt Hf] Hσ") as "[%Hred Hstep]"; [ done | | ].
  { iApply (sq_wp_free _ _ _ _ Hn with "[$Hmt $Hf]"). by iIntros "!> _". }
  destruct Hred as (T' & e' & m' & Hs). destruct (lr_step_free_inv _ _ _ _ _ _ Hs) as [Hpos Hdom].
  iModIntro. iSplit.
  { iPureIntro. do 4 eexists.
    eapply AtTry; [ by apply lr_head_step_step, LRFreeS | apply lr_rsv_free_events ]. }
  iIntros (t2 σ2 efs Hstep) "Hc".
  destruct (at_step_free_inv _ _ _ _ _ _ _ _ Hstep) as (mu' & -> & -> & Hrsv & -> & ->).
  rewrite lr_rsv_free_events in Hrsv. injection Hrsv as <-.
  iMod ("Hstep" with "[%] Hc") as "Hstep"; [ by apply lr_head_step_step, LRFreeS | ].
  iModIntro. iNext. iMod "Hstep" as "[Hσ _]".
  iMod (at_resv_free_try _ _ l (Z.to_nat n) with "Hr") as "[Hr Hfr]".
  { intros z Hz. apply Hvl. rewrite Z2Nat.id in Hz; lia. }
  iModIntro. iSplitL "Hσ Hr"; [ iFrame | ]. iSplitL; [ | done ].
  assert (Hne : lr_free_events l (Z.to_nat n) ≠ []).
  { rewrite -length_zero_iff_nil length_map lr_locs_length. lia. }
  iApply (at_wp_commit _ _ _ (LitV LitPoison) with "[Hfr HΦ]"); [ done | done | ].
  iIntros (m2 mu2) "Hr". iMod (at_resv_free_commit with "Hr Hfr") as (Hsome) "Hr".
  iModIntro. iExists _. iFrame "Hr". iSplit; [ by rewrite lr_fin_free_events | ].
  by iApply "HΦ".
Qed.

Lemma at_wp_read_na E l q v :
  {{{ ▷ l ↦{q} v }}} Running (Read Na1Ord (Lit $ LitLoc l)) [] @ E
  {{{ RET (v : at_val); l ↦{q} v }}}.
Proof.
  iIntros (Φ) ">Hv HΦ". iApply wp_lift_step_fupd; [ done | ].
  iIntros ([m mu] ns κ κs nt) "[Hσ Hr]".
  iDestruct (at_resv_frac with "Hσ Hr Hv") as %[Hm [n Hmu]].
  iMod (sq_wp_try _ (Read Na1Ord (Lit $ LitLoc l)) (fun r => ⌜r = v⌝ ∗ l ↦{q} v)%I m
          [lr_read_event l] with "[Hv] Hσ") as "[_ Hstep]"; [ done | | ].
  { iApply (sq_wp_read_na with "Hv"). iIntros "!> Hv". by iFrame. }
  iModIntro. iSplit.
  { iPureIntro. do 4 eexists. eapply AtTry; [ by apply lr_head_step_step, LRReadNaS | ].
    by apply lr_rsv_read. }
  iIntros (t2 σ2 efs Hstep) "Hc".
  destruct (at_step_read_na_inv _ _ _ _ _ _ _ Hstep)
    as (v' & mu' & -> & -> & Hm' & Hrsv & -> & ->).
  rewrite Hm in Hm'. injection Hm' as <-.
  rewrite (lr_rsv_read _ _ _ Hmu) in Hrsv. injection Hrsv as <-.
  iMod ("Hstep" with "[%] Hc") as "Hstep"; [ by apply lr_head_step_step, LRReadNaS | ].
  iModIntro. iNext. iMod "Hstep" as "[Hσ Hwp]".
  iMod (sq_wp_value_inv with "Hwp") as "[_ Hv]".
  iMod (at_resv_read_try with "Hr Hv") as (k) "[Hr Hk]"; [ by eexists | done | ].
  iModIntro. iSplitL "Hσ Hr"; [ iFrame | ]. iSplitL; [ | done ].
  iApply (at_wp_commit _ _ _ v with "[Hk HΦ]"); [ done | apply to_of_val | ].
  iIntros (m2 mu2) "Hr". iMod (at_resv_read_commit with "Hr Hk") as (n2 Hmu2) "[Hr Hv]".
  iModIntro. iExists _. iFrame "Hr". iSplit; [ by rewrite (lr_fin_read _ _ _ Hmu2) | ].
  by iApply "HΦ".
Qed.

Lemma at_wp_write_na E l e v v' :
  IntoVal e v ->
  {{{ ▷ l ↦ v' }}} Running (Write Na1Ord (Lit $ LitLoc l) e) [] @ E
  {{{ RET (LitV LitPoison : at_val); l ↦ v }}}.
Proof.
  iIntros (<- Φ) ">Hv HΦ". iApply wp_lift_step_fupd; [ done | ].
  iIntros ([m mu] ns κ κs nt) "[Hσ Hr]".
  iDestruct (at_resv_full with "Hσ Hr Hv") as %[Hm Hmu].
  iMod (sq_wp_try _ (Write Na1Ord (Lit $ LitLoc l) (of_val v))
          (fun r => ⌜r = LitV LitPoison⌝ ∗ l ↦ v)%I m [lr_write_event l]
          with "[Hv] Hσ") as "[_ Hstep]"; [ done | | ].
  { iApply (sq_wp_write_na with "Hv"). iIntros "!> Hv". by iFrame. }
  iModIntro. iSplit.
  { iPureIntro. do 4 eexists. eapply AtTry; [ | by apply lr_rsv_write ].
    apply lr_head_step_step. econstructor; [ apply to_of_val | done ]. }
  iIntros (t2 σ2 efs Hstep) "Hc".
  destruct (at_step_write_na_inv _ _ _ _ _ _ _ _ Hstep)
    as (v'' & mu' & -> & -> & Hm' & Hrsv & -> & ->).
  rewrite (lr_rsv_write _ _ Hmu) in Hrsv. injection Hrsv as <-.
  iMod ("Hstep" with "[%] Hc") as "Hstep".
  { apply lr_head_step_step. econstructor; [ apply to_of_val | exact Hm' ]. }
  iModIntro. iNext. iMod "Hstep" as "[Hσ Hwp]".
  iMod (sq_wp_value_inv _ (LitV LitPoison) with "Hwp") as "[_ Hv]".
  iMod (at_resv_write_try with "Hr Hv") as "[Hr Hw]"; [ by eexists | done | ].
  iModIntro. iSplitL "Hσ Hr"; [ iFrame | ]. iSplitL; [ | done ].
  iApply (at_wp_commit _ _ _ (LitV LitPoison) with "[Hw HΦ]"); [ done | done | ].
  iIntros (m2 mu2) "Hr". iMod (at_resv_write_commit with "Hr Hw") as (Hmu2) "[Hr Hv]".
  iModIntro. iExists _. iFrame "Hr". iSplit; [ by rewrite (lr_fin_write _ _ Hmu2) | ].
  by iApply "HΦ".
Qed.

Lemma at_wp_eq_loc E (l1 : loc) (l2: loc) q1 q2 v1 v2 P (Φ : at_val -> iProp Σ) :
  (P ⊢ ▷ l1 ↦{q1} v1) ->
  (P ⊢ ▷ l2 ↦{q2} v2) ->
  (P ⊢ ▷ Φ (LitV (bool_decide (l1 = l2)))) ->
  P ⊢ WP Running (BinOp EqOp (Lit (LitLoc l1)) (Lit (LitLoc l2))) [] @ E {{ Φ }}.
Proof.
  iIntros (Hl1 Hl2 Hpost) "HP". iApply at_wp_sq_value; [ done | | ].
  - intros m T e' m' Hs. apply lr_step_head in Hs; [ | solve_redex_shape ].
    inversion Hs; subst. split_and!; [ done | done | by eexists ].
  - by iApply (sq_wp_eq_loc _ _ _ _ _ _ _ _ _ Hl1 Hl2 Hpost with "HP").
Qed.

(** ** Atomic operations *)

Lemma at_wp_read_sc E l q v :
  {{{ ▷ l ↦{q} v }}} Running (Read ScOrd (Lit $ LitLoc l)) [] @ E
  {{{ RET (v : at_val); l ↦{q} v }}}.
Proof.
  iIntros (Φ) ">Hv HΦ". iApply wp_lift_atomic_step; [ done | ].
  iIntros ([m mu] ns κ κs nt) "[Hσ Hr]".
  iDestruct (at_resv_frac with "Hσ Hr Hv") as %[Hm [n Hmu]].
  iModIntro. iSplit.
  { iPureIntro. do 4 eexists. eapply AtRead; [ by apply lr_head_external_external, LRReadScE | | done ].
    apply Forall_singleton. by rewrite Hmu. }
  iNext. iIntros (t2 σ2 efs Hstep) "_".
  destruct (at_step_read_sc_inv _ _ _ _ _ _ _ Hstep) as (v' & -> & -> & Hm' & -> & ->).
  rewrite Hm in Hm'. injection Hm' as <-.
  iModIntro. iSplitL "Hσ Hr"; [ iFrame | ]. iSplitL; [ | done ].
  rewrite /= to_of_val /=. by iApply "HΦ".
Qed.

Lemma at_wp_write_sc E l e v v' :
  IntoVal e v ->
  {{{ ▷ l ↦ v' }}} Running (Write ScOrd (Lit $ LitLoc l) e) [] @ E
  {{{ RET (LitV LitPoison : at_val); l ↦ v }}}.
Proof.
  iIntros (<- Φ) ">Hv HΦ". iApply wp_lift_atomic_step; [ done | ].
  iIntros ([m mu] ns κ κs nt) "[Hσ Hr]".
  iDestruct (at_resv_full with "Hσ Hr Hv") as %[Hm Hmu].
  iMod (heap_write _ _ _ v with "Hσ Hv") as "[Hσ Hv]". rewrite -sq_heap_insert.
  iModIntro. iSplit.
  { iPureIntro. do 4 eexists. eapply AtWrite.
    - apply lr_head_external_external, LRWriteScE, to_of_val.
    - by apply Forall_singleton.
    - by rewrite /= Hm. }
  iNext. iIntros (t2 σ2 efs Hstep) "_".
  destruct (at_step_write_sc_inv _ _ _ _ _ _ _ _ Hstep) as (-> & -> & -> & ->).
  iModIntro. iSplitL "Hσ Hr".
  { iFrame "Hσ". iApply (at_resv_store with "Hr"). by eexists. }
  iSplitL; [ | done ]. by iApply "HΦ".
Qed.

(** The CAS rules.  A CAS that would succeed while the location is being
    read non-atomically gets stuck ([AtCasStuck]); none of the rules below
    allows that. *)

Lemma at_wp_cas_int_fail E l q z1 e2 lit2 zl :
  IntoVal e2 (LitV lit2) -> z1 ≠ zl ->
  {{{ ▷ l ↦{q} LitV (LitInt zl) }}}
    Running (CAS (Lit $ LitLoc l) (Lit $ LitInt z1) e2) [] @ E
  {{{ RET (LitV $ LitInt 0 : at_val); l ↦{q} LitV (LitInt zl) }}}.
Proof.
  iIntros (<- ? Φ) ">Hv HΦ". iApply wp_lift_atomic_step; [ done | ].
  iIntros ([m mu] ns κ κs nt) "[Hσ Hr]".
  iDestruct (at_resv_frac with "Hσ Hr Hv") as %[Hm [n Hmu]].
  iModIntro. iSplit.
  { iPureIntro. do 4 eexists. eapply AtCasFail.
    - by apply lr_head_external_external, LRCasE.
    - apply Forall_singleton. by rewrite Hmu.
    - by rewrite /= Hm.
    - simpl. constructor. congruence. }
  iNext. iIntros (t2 σ2 efs Hstep) "_".
  destruct (at_step_cas_inv _ _ _ _ _ _ _ _ _ Hstep) as (-> & -> & vc & Hm' & Hcase).
  rewrite Hm in Hm'. injection Hm' as <-.
  destruct Hcase as [(Heq & _) | [(_ & -> & ->) | (Heq & _)]]; try by inv_lr_lit.
  iModIntro. iSplitL "Hσ Hr"; [ iFrame | ]. iSplitL; [ | done ]. simpl. by iApply "HΦ".
Qed.

Lemma at_wp_cas_suc E l lit1 e2 lit2 :
  IntoVal e2 (LitV lit2) -> lit1 ≠ LitPoison ->
  {{{ ▷ l ↦ LitV lit1 }}}
    Running (CAS (Lit $ LitLoc l) (Lit lit1) e2) [] @ E
  {{{ RET (LitV (LitInt 1) : at_val); l ↦ LitV lit2 }}}.
Proof.
  iIntros (<- ? Φ) ">Hv HΦ". iApply wp_lift_atomic_step; [ done | ].
  iIntros ([m mu] ns κ κs nt) "[Hσ Hr]".
  iDestruct (at_resv_full with "Hσ Hr Hv") as %[Hm Hmu].
  iModIntro. iSplit.
  { iPureIntro. do 4 eexists. eapply AtCasSuc.
    - by apply lr_head_external_external, LRCasE.
    - by apply Forall_singleton.
    - by rewrite /= Hm.
    - simpl. destruct lit1; first [ done | constructor ].
    - by rewrite /= Hm. }
  iNext. iIntros (t2 σ2 efs Hstep) "_".
  destruct (at_step_cas_inv _ _ _ _ _ _ _ _ _ Hstep) as (-> & -> & vc & Hm' & Hcase).
  rewrite Hm in Hm'. injection Hm' as <-.
  destruct Hcase as [(_ & _ & -> & ->) | [(Hneq & _) | (_ & Hmu' & _)]];
    [ | by destruct lit1; inv_lr_lit | done ].
  iMod (heap_write with "Hσ Hv") as "[Hσ Hv]". rewrite -sq_heap_insert.
  iModIntro. iSplitL "Hσ Hr".
  { iFrame "Hσ". iApply (at_resv_store with "Hr"). by eexists. }
  iSplitL; [ | done ]. simpl. by iApply "HΦ".
Qed.

Lemma at_wp_cas_int_suc E l z1 e2 lit2 :
  IntoVal e2 (LitV lit2) ->
  {{{ ▷ l ↦ LitV (LitInt z1) }}}
    Running (CAS (Lit $ LitLoc l) (Lit $ LitInt z1) e2) [] @ E
  {{{ RET (LitV (LitInt 1) : at_val); l ↦ LitV lit2 }}}.
Proof. intros ?. by apply at_wp_cas_suc. Qed.

Lemma at_wp_cas_loc_suc E l l1 e2 lit2 :
  IntoVal e2 (LitV lit2) ->
  {{{ ▷ l ↦ LitV (LitLoc l1) }}}
    Running (CAS (Lit $ LitLoc l) (Lit $ LitLoc l1) e2) [] @ E
  {{{ RET (LitV (LitInt 1) : at_val); l ↦ LitV lit2 }}}.
Proof. intros ?. by apply at_wp_cas_suc. Qed.

Lemma at_wp_cas_loc_fail E l q q' q1 l1 v1' e2 lit2 l' vl' :
  IntoVal e2 (LitV lit2) -> l1 ≠ l' ->
  {{{ ▷ l ↦{q} LitV (LitLoc l') ∗ ▷ l' ↦{q'} vl' ∗ ▷ l1 ↦{q1} v1' }}}
    Running (CAS (Lit $ LitLoc l) (Lit $ LitLoc l1) e2) [] @ E
  {{{ RET (LitV (LitInt 0) : at_val);
      l ↦{q} LitV (LitLoc l') ∗ l' ↦{q'} vl' ∗ l1 ↦{q1} v1' }}}.
Proof.
  iIntros (<- ? Φ) "(>Hl & >Hl' & >Hl1) HΦ". iApply wp_lift_atomic_step; [ done | ].
  iIntros ([m mu] ns κ κs nt) "[Hσ Hr]".
  iDestruct (at_resv_frac with "Hσ Hr Hl") as %[Hm [n Hmu]].
  iDestruct (at_resv_frac with "Hσ Hr Hl'") as %[Hm' _].
  iDestruct (at_resv_frac with "Hσ Hr Hl1") as %[Hm1 _].
  iModIntro. iSplit.
  { iPureIntro. do 4 eexists. eapply AtCasFail.
    - by apply lr_head_external_external, LRCasE.
    - apply Forall_singleton. by rewrite Hmu.
    - by rewrite /= Hm.
    - simpl. constructor. congruence. }
  iNext. iIntros (t2 σ2 efs Hstep) "_".
  destruct (at_step_cas_inv _ _ _ _ _ _ _ _ _ Hstep) as (-> & -> & vc & Hmc & Hcase).
  rewrite Hm in Hmc. injection Hmc as <-.
  destruct Hcase as [(Heq & _) | [(_ & -> & ->) | (Heq & _)]]; try by inv_lr_lit.
  iModIntro. iSplitL "Hσ Hr"; [ iFrame | ]. iSplitL; [ | done ]. simpl. iApply "HΦ"; iFrame.
Qed.

Lemma at_wp_cas_loc_nondet E l l1 e2 l2 ll :
  IntoVal e2 (LitV $ LitLoc l2) ->
  {{{ ▷ l ↦ LitV (LitLoc ll) }}}
    Running (CAS (Lit $ LitLoc l) (Lit $ LitLoc l1) e2) [] @ E
  {{{ b, RET (LitV (lit_of_bool b) : at_val);
      if b is true then l ↦ LitV (LitLoc l2)
      else ⌜l1 ≠ ll⌝ ∗ l ↦ LitV (LitLoc ll) }}}.
Proof.
  iIntros (<- Φ) ">Hv HΦ". iApply wp_lift_atomic_step; [ done | ].
  iIntros ([m mu] ns κ κs nt) "[Hσ Hr]".
  iDestruct (at_resv_full with "Hσ Hr Hv") as %[Hm Hmu].
  iModIntro. iSplit.
  { iPureIntro. destruct (decide (ll = l1)) as [-> | Hne]; do 4 eexists.
    - eapply AtCasSuc; [ by apply lr_head_external_external, LRCasE | by apply Forall_singleton
        | by rewrite /= Hm | simpl; by constructor | by rewrite /= Hm ].
    - eapply AtCasFail; [ by apply lr_head_external_external, LRCasE
        | apply Forall_singleton; by rewrite Hmu | by rewrite /= Hm
        | simpl; constructor; congruence ]. }
  iNext. iIntros (t2 σ2 efs Hstep) "_".
  destruct (at_step_cas_inv _ _ _ _ _ _ _ _ _ Hstep) as (-> & -> & vc & Hmc & Hcase).
  rewrite Hm in Hmc. injection Hmc as <-.
  destruct Hcase as [(_ & _ & -> & ->) | [(Hneq & -> & ->) | (_ & Hmu' & _)]]; [ | | done ].
  - iMod (heap_write with "Hσ Hv") as "[Hσ Hv]". rewrite -sq_heap_insert.
    iModIntro. iSplitL "Hσ Hr".
    { iFrame "Hσ". iApply (at_resv_store with "Hr"). by eexists. }
    iSplitL; [ | done ]. simpl. iApply ("HΦ" $! true). iFrame.
  - inv_lr_lit. iModIntro. iSplitL "Hσ Hr"; [ iFrame | ]. iSplitL; [ | done ].
    simpl. iApply ("HΦ" $! false). by iFrame.
Qed.

(** ** Proof rules for working on the n-ary argument list *)
Lemma at_wp_app_ind E f (el : list expr) (Ql : vec (at_val -> iProp Σ) (length el)) vs
    (Φ : at_val -> iProp Σ) :
  AsVal f ->
  ([∗ list] eQ ∈ zip el Ql, WP Running eQ.1 [] @ E {{ eQ.2 }}) -∗
    (∀ vl : vec val (length el), ([∗ list] vQ ∈ zip vl Ql, vQ.2 $ vQ.1) -∗
                    WP Running (App f (of_val <$> vs ++ vl)) [] @ E {{ Φ }}) -∗
    WP Running (App f ((of_val <$> vs) ++ el)) [] @ E {{ Φ }}.
Proof.
  intros [vf <-]. revert vs Ql.
  induction el as [|e el IH]=>/= vs Ql; inv_vec Ql; simpl.
  - iIntros "_ H". iSpecialize ("H" $! [#]). rewrite !app_nil_r /=. by iApply "H".
  - iIntros (Q Ql) "[He Hl] HΦ".
    change (Running (App (of_val vf) ((of_val <$> vs) ++ e :: el)) [])
      with (at_fill [AppRCtx vf vs el] (Running e [])).
    iApply wp_bind. iApply (wp_wand with "He"). iIntros (v) "HQ /=".
    rewrite cons_middle (assoc app) -(fmap_app _ _ [v]).
    iApply (IH _ _ with "Hl"). iIntros "%vl Hvl". rewrite -assoc.
    iApply ("HΦ" $! (v:::vl)). iFrame.
Qed.

Lemma at_wp_app_vec E f el (Ql : vec (at_val -> iProp Σ) (length el)) (Φ : at_val -> iProp Σ) :
  AsVal f ->
  ([∗ list] eQ ∈ zip el Ql, WP Running eQ.1 [] @ E {{ eQ.2 }}) -∗
    (∀ vl : vec val (length el), ([∗ list] vQ ∈ zip vl Ql, vQ.2 $ vQ.1) -∗
                    WP Running (App f (of_val <$> (vl : list val))) [] @ E {{ Φ }}) -∗
    WP Running (App f el) [] @ E {{ Φ }}.
Proof. iIntros (Hf). by iApply (at_wp_app_ind _ _ _ _ []). Qed.

Lemma at_wp_app (Ql : list (at_val -> iProp Σ)) E f el (Φ : at_val -> iProp Σ) :
  length Ql = length el -> AsVal f ->
  ([∗ list] eQ ∈ zip el Ql, WP Running eQ.1 [] @ E {{ eQ.2 }}) -∗
    (∀ vl : list val, ⌜length vl = length el⌝ -∗
            ([∗ list] k ↦ vQ ∈ zip vl Ql, vQ.2 $ vQ.1) -∗
             WP Running (App f (of_val <$> (vl : list val))) [] @ E {{ Φ }}) -∗
    WP Running (App f el) [] @ E {{ Φ }}.
Proof.
  iIntros (Hlen Hf) "Hel HΦ". rewrite -(vec_to_list_to_vec Ql).
  generalize (list_to_vec Ql). rewrite Hlen. clear Hlen Ql=>Ql.
  iApply (at_wp_app_vec with "Hel"). iIntros (vl) "Hvl".
  iApply ("HΦ" with "[%] Hvl"). by rewrite length_vec_to_list.
Qed.


End lifting.
