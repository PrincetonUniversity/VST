Require Import VST.veric.rmaps.
Require Import VST.progs.conclib.
Require Import VST.progs.conc_queue.
Require Import SetoidList.
Require Import VST.floyd.library.

Set Bullet Behavior "Strict Subproofs".

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition tqueue := Tstruct _queue noattr.
Definition tqueue_t := Tstruct _queue_t noattr.

Definition MAX := 10.

(* Ghost histories in the style of
   History-based Verification of Functional Behaviour of Concurrent Programs,
   Blom, Huisman, and Zharieva-Stojanovski (VerCors)
   Twente tech report, 2015 *)

Inductive hist_el {A} := QAdd (p : val) (v : A) | QRem (p : val) (v : A).
Notation hist A := (list (@hist_el A)).
Fixpoint consistent {A} (h : hist A) a b :=
  match h with
  | [] => a = b
  | QAdd p v :: h' => consistent h' (a ++ [(p, v)]) b
  | QRem p v :: h' => match a with [] => False | v' :: q' => v' = (p, v) /\ consistent h' q' b end
  end.
Notation feasible h := (exists b, consistent h [] b).

Parameter ghost : forall (sh : share) {t} (f : share * hist t) (p : val), mpred.
(*Parameter ghost_factory : mpred.

Axiom ghost_alloc : forall Espec D P Q R C P',
  semax(Espec := Espec) D (PROPx P (LOCALx Q (SEPx (ghost_factory :: R)))) C P' ->
  semax D (PROPx P (LOCALx Q (SEPx R))) C P'.
Axiom new_ghost : forall Espec D P Q R C P' t v,
  semax(Espec := Espec) D (PROPx P (LOCALx Q (SEPx (ghost_factory ::
    (EX p : val, ghost Tsh t v p) :: R)))) C P' ->
  semax D (PROPx P (LOCALx Q (SEPx (ghost_factory :: R)))) C P'.
Axiom alloc_conflict : ghost_factory * ghost_factory |-- FF.*)

(* In effect, we want two different ways of splitting/combining history shares.
   One combines the histories as well; the other guarantees injectivity on histories. *)

(* This is definitely unsound, since we can repeat it. *)
Axiom new_ghost : forall {CS : compspecs} {Espec : OracleKind} D P Q R C P' t' t v p,
  semax D (PROPx P (LOCALx Q (SEPx (ghost Tsh (Tsh, ([] : hist t')) p :: data_at Tsh t v p :: R)))) C P' ->
  semax D (PROPx P (LOCALx Q (SEPx (data_at Tsh t v p :: R)))) C P'.

Inductive list_incl {A} : list A -> list A -> Prop :=
| incl_nil l : list_incl [] l
| incl_skip l1 a l2 (Hincl : list_incl l1 l2) : list_incl l1 (a :: l2)
| incl_cons a l1 l2 (Hincl : list_incl l1 l2) : list_incl (a :: l1) (a :: l2).
Hint Constructors list_incl.

Inductive interleave {A} : list (list A) -> list A -> Prop :=
| interleave_nil ls (Hnil : Forall (fun l => l = []) ls) : interleave ls []
| interleave_cons ls i a l l' (Hcons : Znth i ls [] = a :: l) (Hrest : interleave (upd_Znth i ls l) l') :
    interleave ls (a :: l').

Axiom ghost_share_join : forall sh1 sh2 sh t (h1 h2 : hist t) p, sepalg.join sh1 sh2 Tsh -> list_incl h1 h2 ->
  ghost sh1 (sh, h1) p * ghost sh2 (Tsh, h2) p = ghost Tsh (Tsh, h2) p.
Axiom hist_share_join : forall sh sh1 sh2 sh' t (h1 h2 : hist t) p, sepalg.join sh1 sh2 sh' ->
  ghost sh (sh1, h1) p * ghost sh (sh2, h2) p = EX h' : hist t, !!(interleave [h1; h2] h') && ghost sh (sh', h') p.
Axiom hist_add : forall {CS : compspecs} {Espec : OracleKind} D P Q R C P' t (h : hist t) e p,
  feasible (h ++ [e]) ->
  semax D (PROPx P (LOCALx Q (SEPx (ghost Tsh (Tsh, h ++ [e]) p :: R)))) C P' ->
  semax D (PROPx P (LOCALx Q (SEPx (ghost Tsh (Tsh, h) p :: R)))) C P'.
Axiom ghost_inj : forall sh1 sh2 sh t (h1 h2 : hist t) p, ghost sh1 (sh, h1) p * ghost sh2 (Tsh, h2) p
  |-- !!(list_incl h1 h2).
Axiom ghost_inj_Tsh : forall sh1 sh2 t (h1 h2 : hist t) p, ghost sh1 (Tsh, h1) p * ghost sh2 (Tsh, h2) p
  |-- !!(h1 = h2).
(* Should this be an axiom? *)
Axiom ghost_feasible : forall sh t (h : hist t) p, ghost sh (Tsh, h) p |-- !!(feasible h).

Axiom ghost_conflict : forall sh1 sh2 t (v1 v2 : share * hist t) p,
  ghost sh1 v1 p * ghost sh2 v2 p |-- !!sepalg.joins sh1 sh2.

(* We would prefer to let the queue hold arbitrarily complex data, not necessarily associated with a C type.
   For now, the mpred embedding can't handle type application, so we have to default to data_at instead of
   taking a general predicate for the queue, and that means the data is always of a C type. *)
Definition q_lock_pred' (t : type) P p (vals : list (val * reptype t)) head (addc remc : val) lock gsh h :=
  !!(Zlength vals <= MAX /\ 0 <= head < MAX /\ consistent h [] vals) &&
  (data_at Tsh tqueue (rotate (complete MAX (map fst vals)) head MAX, (vint (Zlength vals),
                      (vint head, (vint ((head + Zlength vals) mod MAX), (addc, remc))))) p *
   cond_var Tsh addc * cond_var Tsh remc * malloc_token Tsh (sizeof tqueue_t) p *
   malloc_token Tsh (sizeof tcond) addc * malloc_token Tsh (sizeof tcond) remc *
   malloc_token Tsh (sizeof tlock) lock * ghost gsh (Tsh, h) p *
   fold_right sepcon emp (map (fun x => let '(p, v) := x in
     !!(P v) && (data_at Tsh t v p * malloc_token Tsh (sizeof t) p)) vals)).

Definition q_lock_pred A P p lock gsh := EX vals : list (val * reptype A), EX head : Z,
  EX addc : val, EX remc : val, EX h : hist _, q_lock_pred' A P p vals head addc remc lock gsh h.

Definition lqueue lsh t P p lock gsh1 gsh2 (h : hist (reptype t)) :=
  !!(sepalg.join gsh1 gsh2 Tsh /\ field_compatible tqueue_t [] p) &&
  (field_at lsh tqueue_t [StructField _lock] lock p *
   lock_inv lsh lock (q_lock_pred t P p lock gsh2) * ghost gsh1 (lsh, h) p).

Lemma lqueue_feasible : forall A P p lock gsh1 gsh2 (h : hist (reptype A)),
  lqueue Tsh A P p lock gsh1 gsh2 h = !!(feasible h) && lqueue Tsh A P p lock gsh1 gsh2 h.
Proof.
  intros; rewrite andp_comm; apply add_andp.
  unfold lqueue; Intros.
  setoid_rewrite add_andp with (P0 := ghost gsh1 (Tsh, h) p); [|apply ghost_feasible].
  Intros; apply prop_right; auto.
Qed.

(*Definition PredType := ArrowType (ConstType val) (ArrowType (DependentType 0) Mpred).
Definition q_new_type := ProdType (ConstType (share * share)) PredType.

Program Definition q_new_spec' := mk_funspec (nil, tptr tqueue_t) cc_default q_new_type
  (fun (ts: list Type) (x: share * share * (val -> nth 0 ts unit -> mpred)) => let '(gsh1, gsh2, P) := x in
    PROP (sepalg.join gsh1 gsh2 Tsh)
    LOCAL ()
    SEP ())
  (fun (ts: list Type) (x: share * share * (val -> nth 0 ts unit -> mpred)) => let '(gsh1, gsh2, P) := x in
    EX newq : val, EX lock : val,
    PROP ()
    LOCAL (temp ret_temp newq)
    SEP (lqueue Tsh (nth 0 ts unit) P newq lock gsh1 gsh2 [])) _ _.
Next Obligation.
Proof.
  replace _ with (fun (ts : list Type) (x : share * share * (val -> nth 0 ts unit -> mpred)) rho =>
    PROP (let '(gsh1, gsh2, P) := x in sepalg.join gsh1 gsh2 Tsh) LOCAL () SEP () rho).
  apply (PROP_LOCAL_SEP_super_non_expansive q_new_type [fun _ => _] [] []); repeat constructor.
  hnf; intros.
  destruct x as ((?, ?), ?); auto.
  { repeat extensionality.
    destruct x0 as ((?, ?), ?); auto. }
Qed.
Next Obligation.
Proof.

(* How do we prove super_non_expansive of an existential? Use exp_approx from veric/seplog / veric/Clight_seplog. *)
Admitted.*)

Definition surely_malloc_spec' :=
   WITH n:Z
   PRE [ _n OF tuint ]
       PROP (0 <= n <= Int.max_unsigned)
       LOCAL (temp _n (Vint (Int.repr n)))
       SEP ()
    POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP (malloc_token Tsh n p * memory_block Tsh n p).
Definition surely_malloc_spec prog := DECLARE (ext_link_prog prog "surely_malloc") surely_malloc_spec'.

Definition q_new_spec' :=
  WITH Q : {t : type & reptype t -> Prop}, gsh1 : share, gsh2 : share
  PRE [ ]
   PROP (sepalg.join gsh1 gsh2 Tsh)
   LOCAL ()
   SEP ()
  POST [ tptr tqueue_t ]
   let (t, P) := Q in
   EX newq : val, EX lock : val,
   PROP () LOCAL (temp ret_temp newq)
   SEP (lqueue Tsh t P newq lock gsh1 gsh2 []).
Definition q_new_spec prog := DECLARE (ext_link_prog prog "q_new") q_new_spec'.

Notation q_new_args t P := (existT (fun t => @reptype CompSpecs t -> Prop) t P).

Definition q_del_spec' :=
  WITH Q : {t : type & ((reptype t -> Prop) * hist (reptype t))%type}, p : val, lock : val, gsh1 : share, gsh2 : share
  PRE [ _tgt OF (tptr tqueue_t) ]
   let (t, R) := Q in let (P, h) := R in
   PROP (consistent h [] [])
   LOCAL (temp _tgt p)
   SEP (lqueue Tsh t P p lock gsh1 gsh2 h)
  POST [ tvoid ]
   PROP ()
   LOCAL ()
   SEP ().
Definition q_del_spec prog := DECLARE (ext_link_prog prog "q_del") q_del_spec'.

Notation q_rem_args t P h := (existT (fun t => ((@reptype CompSpecs t -> Prop) * hist (@reptype CompSpecs t))%type) t (P, h)).

Definition q_add_spec' :=
  WITH sh : share, Q : {t : type & ((reptype t -> Prop) * hist (reptype t) * reptype t)%type}, p : val, lock : val,
       e : val, gsh1 : share, gsh2 : share
  PRE [ _tgt OF (tptr tqueue_t), _r OF (tptr tvoid) ]
   let (t, R) := Q in let (S, v) := R in let (P, h) := S in
   PROP (readable_share sh; P v)
   LOCAL (temp _tgt p; temp _r e)
   SEP (lqueue sh t P p lock gsh1 gsh2 h; data_at Tsh t v e; malloc_token Tsh (sizeof t) e)
  POST [ tvoid ]
   let (t, R) := Q in let (S, v) := R in let (P, h) := S in
   PROP ()
   LOCAL ()
   SEP (lqueue sh t P p lock gsh1 gsh2 (h ++ [QAdd e v])).
Definition q_add_spec prog := DECLARE (ext_link_prog prog "q_add") q_add_spec'.

Notation q_add_args t P h v := (existT (fun t =>
  ((@reptype CompSpecs t -> Prop) * hist (@reptype CompSpecs t) * @reptype CompSpecs t)%type) t (P, h, v)).

Definition q_remove_spec' :=
  WITH sh : share, Q : {t : type & ((reptype t -> Prop) * hist (reptype t))%type}, p : val, lock : val, gsh1 : share, gsh2 : share
  PRE [ _tgt OF (tptr tqueue_t) ]
   let (t, R) := Q in let (P, h) := R in
   PROP (readable_share sh)
   LOCAL (temp _tgt p)
   SEP (lqueue sh t P p lock gsh1 gsh2 h)
  POST [ tptr tvoid ]
   let (t, R) := Q in let (P, h) := R in
   EX e : val, EX v : reptype t,
   PROP (P v)
   LOCAL (temp ret_temp e)
   SEP (lqueue sh t P p lock gsh1 gsh2 (h ++ [QRem e v]); data_at Tsh t v e; malloc_token Tsh (sizeof t) e).
Definition q_remove_spec prog := DECLARE (ext_link_prog prog "q_remove") q_remove_spec'.

Definition q_tryremove_spec' :=
  WITH sh : share, Q : {t : type & ((reptype t -> Prop) * hist (reptype t))%type}, p : val, lock : val, gsh1 : share, gsh2 : share
  PRE [ _tgt OF (tptr tqueue_t) ]
   let (t, R) := Q in let (P, h) := R in
   PROP (readable_share sh)
   LOCAL (temp _tgt p)
   SEP (lqueue sh t P p lock gsh1 gsh2 h)
  POST [ tptr tvoid ]
   let (t, R) := Q in let (P, h) := R in
   EX e : val,
   PROP ()
   LOCAL (temp ret_temp e)
   SEP (if eq_dec e nullval then lqueue sh t P p lock gsh1 gsh2 h else
        (EX v : reptype t, !!(P v) &&
         (lqueue sh t P p lock gsh1 gsh2 (h ++ [QRem e v]) * data_at Tsh t v e * malloc_token Tsh (sizeof t) e))).
Definition q_tryremove_spec prog := DECLARE (ext_link_prog prog "q_tryremove") q_tryremove_spec'.

Lemma lock_precise : forall sh p lock (Hsh : readable_share sh),
  precise (field_at sh tqueue_t [StructField _lock] lock p).
Proof.
  intros.
  unfold field_at, at_offset; apply precise_andp2.
  rewrite data_at_rec_eq; simpl; auto.
Qed.

Lemma interleave_single : forall {A} (l l' : list A), interleave [l] l' = (l' = l).
Proof.
  intros; apply prop_ext; split; intro; subst.
  - remember [l] as l0; revert dependent l; induction H; intros; subst.
    + inv Hnil; auto.
    + exploit (Znth_inbounds i [l0] []).
      { rewrite Hcons; discriminate. }
      intro; assert (i = 0) by (rewrite Zlength_cons, Zlength_nil in *; omega).
      subst; rewrite Znth_0_cons in Hcons; subst.
      rewrite upd_Znth0, sublist_nil in IHinterleave; specialize (IHinterleave _ eq_refl); subst; auto.
  - induction l; econstructor; auto.
    + instantiate (2 := 0); rewrite Znth_0_cons; eauto.
    + rewrite upd_Znth0, sublist_nil; auto.
Qed.

Lemma interleave_remove_nil : forall {A} ls (l' : list A),
  interleave ([] :: ls) l' <-> interleave ls l'.
Proof.
  split; intro.
  - remember ([] :: ls) as l0; revert dependent ls; induction H; intros; subst.
    + inv Hnil; constructor; auto.
    + destruct (Z_le_dec i 0).
      { destruct (eq_dec i 0); [subst; rewrite Znth_0_cons in Hcons | rewrite Znth_underflow in Hcons];
          try discriminate; try omega. }
      rewrite Znth_pos_cons in Hcons; [econstructor; eauto | omega].
      apply IHinterleave.
      setoid_rewrite upd_Znth_app2 with (l1 := [[]]); auto.
      rewrite Zlength_cons, Zlength_nil.
      destruct (Z_le_dec (i - 1) (Zlength ls0)); [omega | rewrite Znth_overflow in Hcons; [discriminate | omega]].
  - induction H.
    + constructor; auto.
    + destruct (zlt i 0); [rewrite Znth_underflow in Hcons; [discriminate | auto]|].
      econstructor.
      * rewrite Znth_pos_cons, Z.add_simpl_r; eauto; omega.
      * setoid_rewrite upd_Znth_app2 with (l1 := [[]]); rewrite Zlength_cons, Zlength_nil.
        rewrite Z.add_simpl_r; auto.
        { destruct (Z_le_dec i (Zlength ls)); [omega | rewrite Znth_overflow in Hcons; [discriminate | omega]]. }
Qed.

Corollary interleave_remove_nils : forall {A} ls0 ls (l' : list A), Forall (fun l => l = []) ls0 ->
  interleave (ls0 ++ ls) l' <-> interleave ls l'.
Proof.
  induction ls0; [reflexivity | intros].
  inv H; simpl; rewrite interleave_remove_nil; auto.
Qed.

Lemma interleave_trans : forall {A} ls1 ls2 (l' l'' : list A)
  (Hl' : interleave ls1 l') (Hl'' : interleave (l' :: ls2) l''), interleave (ls1 ++ ls2) l''.
Proof.
  intros until 1; revert ls2 l''; induction Hl'; intros.
  - rewrite interleave_remove_nil in Hl''; rewrite interleave_remove_nils; auto.
  - remember ((a :: l') :: ls2) as ls0; revert dependent ls2; revert dependent l'; revert dependent a;
      induction Hl''; intros; subst.
    { inv Hnil; discriminate. }
    exploit (Znth_inbounds i ls []).
    { rewrite Hcons0; discriminate. }
    intro; destruct (eq_dec i0 0).
    + subst; rewrite Znth_0_cons in Hcons; inv Hcons.
      econstructor.
      * rewrite app_Znth1; eauto; omega.
      * rewrite upd_Znth_app1; auto.
        rewrite upd_Znth0, sublist_1_cons, sublist_same in Hl''; auto.
        rewrite Zlength_cons; omega.
    + exploit (Znth_inbounds i0 ((a0 :: l'0) :: ls2) []).
      { rewrite Hcons; discriminate. }
      intro; rewrite Znth_pos_cons in Hcons; [|omega].
      econstructor.
      * rewrite app_Znth2, Z.add_simpl_r; eauto; omega.
      * rewrite Zlength_cons in *; rewrite upd_Znth_app2, Z.add_simpl_r; [|omega].
        eapply IHHl''; eauto.
        rewrite upd_Znth_cons; auto; omega.
Qed.

Lemma lqueue_share_join : forall t P sh1 sh2 sh p lock gsh1 gsh2 h1 h2
  (Hsh1 : readable_share sh1) (Hsh2 : readable_share sh2) (Hjoin : sepalg.join sh1 sh2 sh),
  lqueue sh1 t P p lock gsh1 gsh2 h1 * lqueue sh2 t P p lock gsh1 gsh2 h2 =
  EX h' : hist _, !!(interleave [h1; h2] h') && lqueue sh t P p lock gsh1 gsh2 h'.
Proof.
  intros; unfold lqueue; normalize.
  rewrite sepcon_comm, (sepcon_comm _ (ghost _ _ _)), <- !sepcon_assoc, (sepcon_comm _ (ghost _ _ _)).
  erewrite hist_share_join; eauto.
  rewrite !sepcon_assoc, (sepcon_comm _ (lock_inv sh2 _ _)), <- (sepcon_assoc (lock_inv _ _ _)).
  erewrite lock_inv_share_join; eauto.
  rewrite (sepcon_comm _ (field_at _ _ _ _ _)), <- (sepcon_assoc (field_at _ _ _ _ _)).
  erewrite field_at_share_join; eauto.
  normalize.
  f_equal; extensionality.
  normalize.
  rewrite sepcon_assoc, sepcon_comm; f_equal; f_equal.
  apply prop_ext; tauto.
Qed.

Corollary lqueue_share_join_nil : forall t P sh1 sh2 sh p lock gsh1 gsh2
  (Hsh1 : readable_share sh1) (Hsh2 : readable_share sh2) (Hjoin : sepalg.join sh1 sh2 sh),
  lqueue sh t P p lock gsh1 gsh2 [] |--
  lqueue sh1 t P p lock gsh1 gsh2 [] * lqueue sh2 t P p lock gsh1 gsh2 [].
Proof.
  intros; erewrite lqueue_share_join; eauto.
  Exists ([] : hist (reptype t)); entailer!; constructor; auto.
Qed.

Corollary lqueue_shares_join : forall t P p lock sh1 sh2 sh shs h hs
  (Hlen : length shs = length hs)
  (Hsplit : forall i, 0 <= i < Zlength shs ->
    let '(a, b) := Znth i shs (sh, sh) in
    readable_share a /\ readable_share b /\ sepalg.join a b (fst (Znth (i + 1) shs (sh, sh)))),
  lqueue (fst (Znth 0 shs (sh, sh))) t P p lock sh1 sh2 h *
  fold_right sepcon emp (map (fun x => let '(sh, h) := x in lqueue sh t P p lock sh1 sh2 h)
    (combine (map snd shs) hs)) |--
  EX h' : hist _, !!(interleave (h :: hs) h') && lqueue sh t P p lock sh1 sh2 h'.
Proof.
  induction shs; destruct hs; try discriminate; simpl; intros.
  - Exists h; rewrite interleave_single; entailer!.
  - rewrite Znth_0_cons; simpl.
    rewrite Zlength_cons in Hsplit.
    exploit (Hsplit 0).
    { rewrite Zlength_correct; omega. }
    rewrite !Znth_0_cons; destruct a; intros (? & ? & ?).
    erewrite <- sepcon_assoc, lqueue_share_join; eauto.
    simpl; rewrite Znth_pos_cons, Zminus_diag; [|omega].
    Intros h'.
    eapply derives_trans; [apply IHshs; auto|].
    { intros; specialize (Hsplit (i + 1)).
      rewrite !Znth_pos_cons, !Z.add_simpl_r in Hsplit; try omega.
      apply Hsplit; omega. }
    Intros h''.
    Exists h''; entailer!.
    eapply interleave_trans with (ls1 := [h; l]); eauto.
Qed.

Lemma all_ptrs : forall t P vals, fold_right sepcon emp (map (fun x => let '(p, v) := x in
  !!(P v) && (data_at Tsh t v p * malloc_token Tsh (sizeof t) p)) vals) |--
  !!(Forall isptr (map fst vals)).
Proof.
  induction vals; simpl; intros; entailer.
  destruct a.
  rewrite data_at_isptr.
  eapply derives_trans; [apply saturate_aux20 with (P' := isptr v)|].
  { Intros; apply prop_right; auto. }
  { apply IHvals; auto. }
  normalize.
Qed.

Lemma vals_precise : forall r t P vals1 vals2 r1 r2
  (Hvals : map fst vals1 = map fst vals2)
  (Hvals1 : predicates_hered.app_pred(A := compcert_rmaps.R.rmap) (fold_right sepcon emp
    (map (fun x => let '(p, v) := x in !!(P v) && (data_at Tsh t v p * malloc_token Tsh (sizeof t) p)) vals1)) r1)
  (Hvals2 : predicates_hered.app_pred(A := compcert_rmaps.R.rmap) (fold_right sepcon emp
    (map (fun x => let '(p, v) := x in !!(P v) && (data_at Tsh t v p * malloc_token Tsh (sizeof t) p)) vals2)) r2)
  (Hr1 : sepalg.join_sub r1 r) (Hr2 : sepalg.join_sub r2 r), r1 = r2.
Proof.
  induction vals1; simpl; intros; destruct vals2; inversion Hvals.
  - apply sepalg.same_identity with (a := r); auto.
    { destruct Hr1 as (? & H); specialize (Hvals1 _ _ H); subst; auto. }
    { destruct Hr2 as (? & H); specialize (Hvals2 _ _ H); subst; auto. }
  - destruct a, p; simpl in *; subst.
    destruct Hvals1 as (? & r1b & ? & (? & r1a & ? & ? & Hh1 & Hm1) & ?),
      Hvals2 as (? & r2b & ? & (? & r2a & ? & ? & Hh2 & Hm2) & ?).
    exploit malloc_token_precise.
    { apply Hm1. }
    { apply Hm2. }
    { join_sub. }
    { join_sub. }
    assert (r1a = r2a); [|intros; subst].
    { apply data_at_data_at_ in Hh1; apply data_at_data_at_ in Hh2.
      eapply data_at__precise with (sh := Tsh); auto; eauto; join_sub. }
    assert (r1b = r2b); [|subst].
    { eapply IHvals1; eauto; join_sub. }
    join_inj.
Qed.

Axiom ghost_precise : forall sh {t} p, precise (EX f : share * hist (reptype t), ghost sh f p).

Lemma tqueue_inj : forall r (buf1 buf2 : list val) len1 len2 head1 head2 tail1 tail2
  (addc1 addc2 remc1 remc2 : val) p r1 r2
  (Hp1 : predicates_hered.app_pred(A := compcert_rmaps.R.rmap)
     (data_at Tsh tqueue (buf1, (vint len1, (vint head1, (vint tail1, (addc1, remc1))))) p) r1)
  (Hp2 : predicates_hered.app_pred(A := compcert_rmaps.R.rmap)
     (data_at Tsh tqueue (buf2, (vint len2, (vint head2, (vint tail2, (addc2, remc2))))) p) r2)
  (Hr1 : sepalg.join_sub r1 r) (Hr2 : sepalg.join_sub r2 r)
  (Hbuf1 : Forall (fun v => v <> Vundef) buf1) (Hl1 : Zlength buf1 = MAX)
  (Hbuf2 : Forall (fun v => v <> Vundef) buf2) (Hl2 : Zlength buf2 = MAX)
  (Haddc1 : addc1 <> Vundef) (Haddc2 : addc2 <> Vundef) (Hremc1 : remc1 <> Vundef) (Hremc2 : remc2 <> Vundef),
  r1 = r2 /\ buf1 = buf2 /\ Int.repr len1 = Int.repr len2 /\ Int.repr head1 = Int.repr head2 /\
  Int.repr tail1 = Int.repr tail2 /\ addc1 = addc2 /\ remc1 = remc2.
Proof.
  intros.
  unfold data_at in Hp1, Hp2; erewrite field_at_Tstruct in Hp1, Hp2; try reflexivity; try apply JMeq_refl.
  simpl in Hp1, Hp2; unfold withspacer in Hp1, Hp2; simpl in Hp1, Hp2.
  destruct Hp1 as (? & ? & ? & (? & Hb1) & ? & ? & ? & (? & Hlen1) & ? & ? & ? & (? & Hhead1) & ? & ? & ? &
    (? & Htail1) & ? & ? & ? & (? & Hadd1) & ? & Hrem1).
  destruct Hp2 as (? & ? & ? & (? & Hb2) & ? & ? & ? & (? & Hlen2) & ? & ? & ? & (? & Hhead2) & ? & ? & ? &
    (? & Htail2) & ? & ? & ? & (? & Hadd2) & ? & Hrem2); unfold at_offset in *.
  assert (readable_share Tsh) as Hread by auto.
  exploit (mapsto_inj _ _ _ _ _ _ _ r Hread Hrem1 Hrem2); auto; try join_sub.
  exploit (mapsto_inj _ _ _ _ _ _ _ r Hread Hadd1 Hadd2); auto; try join_sub.
  exploit (mapsto_inj _ _ _ _ _ _ _ r Hread Htail1 Htail2); auto; try join_sub; try discriminate.
  exploit (mapsto_inj _ _ _ _ _ _ _ r Hread Hhead1 Hhead2); auto; try join_sub; try discriminate.
  exploit (mapsto_inj _ _ _ _ _ _ _ r Hread Hlen1 Hlen2); auto; try join_sub; try discriminate.
  exploit (data_at_ptr_array_inj _ _ _ _ _ _ _ _ r Hread Hb1 Hb2); auto; try join_sub.
  unfold repinject.
  intros (? & ?) (? & ?) (? & ?) (? & ?) (? & ?) (? & ?); subst; join_inj.
  repeat split; auto; congruence.
Qed.

Lemma q_inv_precise : forall t P p lock gsh2, precise (q_lock_pred t P p lock gsh2).
Proof.
  unfold q_lock_pred, q_lock_pred'; intros ???????? H1 H2 Hw1 Hw2.
  destruct H1 as (vals1 & head1 & addc1 & remc1 & h1 & (? & ? & ?) & ? & ? & ? & (? & ? & ? & (? & ? & ? &
    (? & ? & ? & (? & ? & ? & (? & ? & ? & (? & ? & ? & (? & ? & ? & (Hq1 & Haddc1)) & Hremc1) & Htv1) & Hta1) &
    Htr1) & Htl1) & Hghost1) & Hvals1),
  H2 as (vals2 & head2 & addc2 & remc2 & h2 & (? & ? & ?) & ? & ? & ? & (? & ? & ? & (? & ? & ? &
    (? & ? & ? & (? & ? & ? & (? & ? & ? & (? & ? & ? & (? & ? & ? & (Hq2 & Haddc2)) & Hremc2) & Htv2) & Hta2) &
    Htr2) & Htl2) & Hghost2) & Hvals2).
  pose proof (all_ptrs _ _ _ _ Hvals1) as Hptrs1.
  pose proof (all_ptrs _ _ _ _ Hvals2) as Hptrs2.
  exploit (tqueue_inj w _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hq1 Hq2); try join_sub.
  { apply Forall_rotate, Forall_complete; auto; [|discriminate].
    eapply Forall_impl; [|apply Hptrs1]; destruct a; try contradiction; discriminate. }
  { rewrite Zlength_rotate; try rewrite Zlength_complete; try omega; rewrite Zlength_map; auto. }
  { apply Forall_rotate, Forall_complete; auto; [|discriminate].
    eapply Forall_impl; [|apply Hptrs2]; destruct a; try contradiction; discriminate. }
  { rewrite Zlength_rotate; try rewrite Zlength_complete; try omega; rewrite Zlength_map; auto. }
  { rewrite cond_var_isptr in Haddc1; destruct Haddc1, addc1; try contradiction; discriminate. }
  { rewrite cond_var_isptr in Haddc2; destruct Haddc2, addc2; try contradiction; discriminate. }
  { rewrite cond_var_isptr in Hremc1; destruct Hremc1, remc1; try contradiction; discriminate. }
  { rewrite cond_var_isptr in Hremc2; destruct Hremc2, remc2; try contradiction; discriminate. }
  intros (? & ? & Hlen & ? & ? & ? & ?); subst.
  exploit (ghost_precise(t := t) gsh2 p w).
  { eexists; apply Hghost1. }
  { eexists; apply Hghost2. }
  { join_sub. }
  { join_sub. }
  intro; subst.
  assert (head1 = head2) as ->.
  { apply repr_inj_unsigned; auto; split; try omega; transitivity MAX; try omega; unfold MAX; computable. }
  assert (length vals1 = length vals2).
  { apply repr_inj_unsigned in Hlen; rewrite Zlength_correct in Hlen.
    rewrite Zlength_correct in Hlen; Omega0.
    - split; [rewrite Zlength_correct; omega|]; transitivity MAX; try omega; unfold MAX; computable.
    - split; [rewrite Zlength_correct; omega|]; transitivity MAX; try omega; unfold MAX; computable. }
  assert (map fst vals1 = map fst vals2) as Heq.
  { eapply complete_inj; [|rewrite !map_length; auto].
    eapply rotate_inj; eauto; try omega.
    repeat rewrite length_complete; try rewrite Zlength_map; auto.
    rewrite Zlength_complete; try rewrite Zlength_map; omega. }
  rewrite Heq in *.
  exploit (vals_precise w _ _ _ _ _ _ Heq Hvals1 Hvals2); auto; try join_sub.
  assert (readable_share Tsh) as Hread by auto.
  exploit (cond_var_precise _ _ Hread w _ _ Haddc1 Haddc2); try join_sub.
  exploit (cond_var_precise _ _ Hread w _ _ Hremc1 Hremc2); try join_sub.
  exploit (malloc_token_precise _ _ _ w _ _ Hta1 Hta2); try join_sub.
  exploit (malloc_token_precise _ _ _ w _ _ Htr1 Htr2); try join_sub.
  exploit (malloc_token_precise _ _ _ w _ _ Htv1 Htv2); try join_sub.
  exploit (malloc_token_precise _ _ _ w _ _ Htl1 Htl2); try join_sub.
  intros; subst; join_inj.
Qed.

Lemma q_inv_positive : forall t P p lock gsh2, positive_mpred (q_lock_pred t P p lock gsh2).
Proof.
  intros; simpl.
  repeat (apply ex_positive; intro).
  apply positive_andp2.
  do 7 apply positive_sepcon1; apply positive_sepcon2; auto.
Qed.
Hint Resolve q_inv_precise q_inv_positive.

Lemma lqueue_precise : forall lsh t P p lock gsh1 gsh2,
  precise (EX h : hist (reptype t), lqueue lsh t P p lock gsh1 gsh2 h).
Proof.
  intros; unfold lqueue.
  apply derives_precise' with (Q := field_at lsh tqueue_t [StructField conc_queue._lock] lock p *
    lock_inv lsh lock (q_lock_pred t P p lock gsh2) * EX f : share * hist (reptype t), ghost gsh1 f p).
  - entailer!.
    Exists (lsh, h); auto.
  - repeat apply precise_sepcon; auto.
    apply ghost_precise.
Qed.
Hint Resolve lqueue_precise.

Lemma lqueue_isptr : forall lsh t P p lock gsh1 gsh2 h, lqueue lsh t P p lock gsh1 gsh2 h =
  !!isptr p && lqueue lsh t P p lock gsh1 gsh2 h.
Proof.
  intros; eapply local_facts_isptr with (P := fun p => lqueue lsh t P p lock gsh1 gsh2 h); eauto.
  unfold lqueue; rewrite field_at_isptr; Intros; apply prop_right; auto.
Qed.

Lemma list_incl_refl : forall {A} (l : list A), list_incl l l.
Proof.
  induction l; auto.
Qed.
Hint Resolve list_incl_refl.

Lemma consistent_inj : forall {t} (h : hist t) a b b' (Hb : consistent h a b) (Hb' : consistent h a b'), b = b'.
Proof.
  induction h; simpl; intros.
  - subst; auto.
  - destruct a; eauto.
    destruct a0; [contradiction|].
    destruct Hb, Hb'; eauto.
Qed.

Lemma consistent_trans : forall {t} (h1 h2 : hist t) a b c, consistent h1 a b -> consistent h2 b c ->
  consistent (h1 ++ h2) a c.
Proof.
  induction h1; simpl; intros; subst; auto.
  destruct a; eauto.
  destruct a0; [contradiction | destruct H; eauto].
Qed.

Corollary consistent_snoc_add : forall {t} (h : hist t) a b e v, consistent h a b ->
  consistent (h ++ [QAdd e v]) a (b ++ [(e, v)]).
Proof.
  intros; eapply consistent_trans; simpl; eauto.
Qed.

Corollary consistent_cons_rem : forall {t} (h : hist t) a b e v, consistent h a ((e, v) :: b) ->
  consistent (h ++ [QRem e v]) a b.
Proof.
  intros; eapply consistent_trans; eauto; simpl; auto.
Qed.

Lemma list_incl_app2 : forall {A} (l l1 l2 : list A), list_incl l l2 -> list_incl l (l1 ++ l2).
Proof.
  induction l1; auto; intros.
  simpl; constructor; auto.
Qed.

Lemma list_incl_app : forall {A} (l1 l2 l1' l2' : list A), list_incl l1 l2 -> list_incl l1' l2' ->
  list_incl (l1 ++ l1') (l2 ++ l2').
Proof.
  induction 1; intros.
  - simpl; apply list_incl_app2; auto.
  - simpl; constructor; auto.
  - simpl; constructor 3; auto.
Qed.

Definition is_add {A} (a : @hist_el A):= match a with QAdd _ _ => true | _ => false end.

Lemma consistent_adds : forall {A} (h : hist A) (Hadds : forallb is_add h = true),
  exists l, h = map (fun x => let '(p, v) := x in QAdd p v) l /\
    forall h2 a b, consistent (h ++ h2) a b <-> consistent h2 (a ++ l) b.
Proof.
  induction h; simpl; intros.
  - exists []; split; auto; intros; rewrite app_nil_r; reflexivity.
  - rewrite andb_true_iff in Hadds; destruct Hadds, a; try discriminate.
    destruct IHh as (l & ? & IH); auto; subst.
    exists ((p, v) :: l); split; auto; intros; rewrite IH, <- app_assoc; reflexivity.
Qed.

Corollary consistent_insert_rem : forall {A} (h1 h2 : hist A) a b p v (Hadds : forallb is_add h1 = true),
  consistent (h1 ++ h2) a b -> consistent (h1 ++ QRem p v :: h2) ((p, v) :: a) b.
Proof.
  intros.
  destruct (consistent_adds _ Hadds) as (l & ? & Hh1).
  rewrite Hh1 in *; simpl; auto.
Qed.

Lemma interleave_In : forall {A} ls (l' : list A) x (Hinter : interleave ls l'),
  In x l' <-> exists l, In l ls /\ In x l.
Proof.
  induction 1.
  - split; intro; [contradiction|].
    destruct H as (? & ? & ?).
    rewrite Forall_forall in Hnil; exploit Hnil; eauto; intro; subst; auto.
  - simpl; rewrite IHHinter.
    exploit (Znth_inbounds i ls []); [rewrite Hcons; discriminate | intro Hi].
    split; intro.
    + destruct H.
      * subst; exists (x :: l); split; simpl; auto.
        rewrite <- Hcons; apply Znth_In; auto.
      * destruct H as (l1 & Hl1 & ?).
        apply In_upd_Znth in Hl1; destruct Hl1; eauto.
        subst; exists (a :: l); split; simpl; auto.
        rewrite <- Hcons; apply Znth_In; auto.
    + destruct H as (l1 & Hl1 & ?).
      destruct (In_Znth _ _ [] Hl1) as (i' & ? & Hi').
      destruct (eq_dec i' i).
      * subst; rewrite Hcons in *; subst.
        destruct H; auto.
        right; exists l; split; auto.
        apply upd_Znth_In.
      * right; eexists; erewrite <- upd_Znth_diff in Hi'; [split; eauto; rewrite <- Hi'; apply Znth_In | | |];
          rewrite ?upd_Znth_Zlength; auto.
Qed.

Lemma add_first : forall {A} ls (h : hist A) a b
  (Hinter : interleave ls h) (Hcon : consistent h a b),
  exists h1 h2, interleave (map (filter is_add) ls) h1 /\
                interleave (map (filter (fun a => negb (is_add a))) ls) h2 /\ consistent (h1 ++ h2) a b.
Proof.
  intros until 1; revert a b; induction Hinter; intros.
  - exists [], []; simpl; repeat split; auto; constructor.
    + rewrite Forall_forall in *; intros.
      rewrite in_map_iff in H; destruct H as (? & ? & ?); subst.
      exploit Hnil; eauto; intro; subst; auto.
    + rewrite Forall_forall in *; intros.
      rewrite in_map_iff in H; destruct H as (? & ? & ?); subst.
      exploit Hnil; eauto; intro; subst; auto.
  - simpl in Hcon.
    exploit (Znth_inbounds i ls []); [rewrite Hcons; discriminate | intro].
    destruct a.
    + specialize (IHHinter _ _ Hcon); destruct IHHinter as (h1 & h2 & Hh1 & Hh2 & ?).
      exists (QAdd p v :: h1), h2; repeat split; auto.
      * econstructor.
        { rewrite Znth_map with (d' := []), Hcons; simpl; eauto. }
        rewrite upd_Znth_map; auto.
      * erewrite <- upd_Znth_map, upd_Znth_triv in Hh2; auto.
        { rewrite Zlength_map; auto. }
        rewrite Znth_map', Hcons; auto.
    + destruct a0; [contradiction | destruct Hcon as (? & Hcon); subst].
      specialize (IHHinter _ _ Hcon); destruct IHHinter as (h1 & h2 & Hh1 & Hh2 & ?).
      exists h1, (QRem p v :: h2); repeat split.
      * erewrite <- upd_Znth_map, upd_Znth_triv in Hh1; auto.
        { rewrite Zlength_map; auto. }
        rewrite Znth_map', Hcons; auto.
      * econstructor.
        { rewrite Znth_map with (d' := []), Hcons; simpl; eauto. }
        rewrite upd_Znth_map; auto.
      * apply consistent_insert_rem; auto.
        rewrite forallb_forall; intros ? Hin.
        rewrite interleave_In in Hin; [|eauto].
        destruct Hin as (? & Hin & Hin'); rewrite in_map_iff in Hin.
        destruct Hin as (? & ? & Hin); subst.
        rewrite filter_In in Hin'; destruct Hin'; auto.
Qed.

Lemma interleave_reorder : forall {A} ls1 ls2 (l l' : list A),
  interleave (ls1 ++ l :: ls2) l' <-> interleave (l :: ls1 ++ ls2) l'.
Proof.
  split; intro.
  - remember (ls1 ++ l :: ls2) as l0; revert dependent ls2; revert l ls1; induction H; intros; subst.
    + constructor; rewrite Forall_app in Hnil.
      destruct Hnil as (? & Hnil); inv Hnil; constructor; auto; rewrite Forall_app; auto.
    + exploit (Znth_inbounds i (ls1 ++ l0 :: ls2) []); [rewrite Hcons; discriminate | intro].
      destruct (zlt i (Zlength ls1)); [|rewrite app_Znth2 in Hcons; auto; destruct (eq_dec (i - Zlength ls1) 0)].
      * rewrite app_Znth1 in Hcons; auto.
        econstructor; [rewrite Znth_pos_cons, app_Znth1, Z.add_simpl_r; eauto; omega|].
        rewrite upd_Znth_cons, upd_Znth_app1; try omega.
        apply IHinterleave.
        rewrite upd_Znth_app1, Z.add_simpl_r; [auto | omega].
      * rewrite e, Znth_0_cons in Hcons; subst.
        econstructor; [rewrite Znth_0_cons; eauto|].
        rewrite upd_Znth0, sublist_1_cons, sublist_same; auto; [|rewrite Zlength_cons; omega].
        apply IHinterleave.
        rewrite upd_Znth_app2, e, upd_Znth0, sublist_1_cons, sublist_same; auto;
          rewrite Zlength_app, Zlength_cons in *; omega.
      * rewrite Znth_pos_cons in Hcons; [|omega].
        replace (i - Zlength ls1 - 1) with ((i - 1) - Zlength ls1) in Hcons by omega.
        assert (i > 0) by (rewrite Zlength_correct in *; omega).
        econstructor; [rewrite Znth_pos_cons, app_Znth2; eauto; omega|].
        rewrite Zlength_app, Zlength_cons in *.
        rewrite upd_Znth_cons, upd_Znth_app2; auto; try omega.
        apply IHinterleave.
        rewrite upd_Znth_app2, upd_Znth_cons; rewrite ?Zlength_cons; try omega.
        replace (i - Zlength ls1 - 1) with (i - 1 - Zlength ls1); Omega0.
  - remember (l :: ls1 ++ ls2) as l0; revert dependent ls2; revert l ls1; induction H; intros; subst.
    + inv Hnil; constructor.
      rewrite Forall_app in H2; destruct H2; rewrite Forall_app; split; auto.
    + exploit (Znth_inbounds i (l0 :: ls1 ++ ls2) []); [rewrite Hcons; discriminate | intro].
      destruct (eq_dec i 0); [|rewrite Znth_pos_cons in Hcons; [destruct (zlt (i - 1) (Zlength ls1)) | omega]].
      * subst; rewrite Znth_0_cons in Hcons; subst.
        econstructor; [rewrite app_Znth2, Zminus_diag, Znth_0_cons; eauto; omega|].
        rewrite upd_Znth_app2, Zminus_diag, upd_Znth0, sublist_1_cons, sublist_same; auto;
          try rewrite Zlength_cons, !Zlength_correct; try omega.
        apply IHinterleave.
        rewrite upd_Znth0, sublist_1_cons, sublist_same; auto; rewrite Zlength_cons; omega.
      * rewrite app_Znth1 in Hcons; auto.
        econstructor; [rewrite app_Znth1; eauto|].
        rewrite upd_Znth_app1; [|omega].
        apply IHinterleave.
        rewrite upd_Znth_cons, upd_Znth_app1; auto; omega.
      * rewrite app_Znth2 in Hcons; auto.
        replace (i - 1 - Zlength ls1) with (i - Zlength ls1 - 1) in Hcons by omega.
        econstructor; [rewrite app_Znth2, Znth_pos_cons; eauto; omega|].
        rewrite upd_Znth_app2, upd_Znth_cons; try rewrite Zlength_cons, Zlength_app in *; try omega.
        apply IHinterleave.
        rewrite upd_Znth_cons, upd_Znth_app2; try omega.
        replace (i - 1 - Zlength ls1) with (i - Zlength ls1 - 1); auto; omega.
Qed.

Corollary interleave_remove_nil' : forall {A} ls1 ls2 (l' : list A),
  interleave (ls1 ++ [] :: ls2) l' <-> interleave (ls1 ++ ls2) l'.
Proof.
  intros; rewrite interleave_reorder, interleave_remove_nil; reflexivity.
Qed.

Lemma consistent_rems : forall {A} (h : hist A) a b (Hrems : forallb (fun x => negb (is_add x)) h = true),
  consistent h a b ->
  exists l, a = l ++ b /\ h = map (fun x => let '(p, v) := x in QRem p v) l.
Proof.
  induction h; simpl; intros.
  - subst; exists []; auto.
  - rewrite andb_true_iff in Hrems; destruct Hrems.
    destruct a; [discriminate|].
    destruct a0; [contradiction | destruct H as (? & Hcon); subst].
    exploit IHh; eauto; intros (l & ? & ?); subst.
    exists ((p, v) :: l); auto.
Qed.

Lemma interleave_map_inj : forall {A B} (f : A -> B) ls l' (Hinj : forall x y, f x = f y -> x = y),
  interleave (map (map f) ls) (map f l') -> interleave ls l'.
Proof.
  intros.
  remember (map (map f) ls) as ls0; remember (map f l') as l1; revert dependent l'; revert dependent ls;
    induction H; intros; subst.
  - destruct l'; [|discriminate].
    constructor.
    rewrite Forall_forall in *; intros l Hin.
    exploit (Hnil (map f l)).
    { rewrite in_map_iff; eauto. }
    destruct l; auto; discriminate.
  - destruct l'0; [discriminate | inv Heql1].
    change [] with (map f []) in Hcons; rewrite Znth_map' in Hcons.
    destruct (Znth i ls0 []) eqn: Hi; [discriminate | inv Hcons].
    exploit Hinj; [eassumption | intro; subst].
    econstructor; eauto.
    apply IHinterleave; auto.
    apply upd_Znth_map.
Qed.

Lemma interleave_combine : forall {A B} ls1 ls2 (l1 : list A) (l2 : list B)
  (Hls : Forall2 (fun la lb => length la = length lb) ls1 ls2)
  (Hlen : length l1 = length l2),
  interleave (map (fun x => let '(la, lb) := x in combine la lb) (combine ls1 ls2)) (combine l1 l2) ->
  interleave ls1 l1 /\ interleave ls2 l2.
Proof.
  intros.
  remember (map (fun x => let '(la, lb) := x in combine la lb) (combine ls1 ls2)) as ls0;
    remember (combine l1 l2) as l0; revert dependent l2; revert l1; revert dependent ls2; revert ls1;
    induction H; intros; subst.
  - destruct l1, l2; try discriminate.
    pose proof (mem_lemmas.Forall2_Zlength Hls).
    split; constructor.
    + rewrite Forall_forall in *; intros l1 Hin.
      destruct (In_Znth _ _ [] Hin) as (i & ? & ?).
      exploit (Hnil (combine l1 (Znth i ls2 []))).
      { rewrite in_map_iff; eexists (_, _); split; eauto.
        subst; rewrite <- Znth_combine; auto.
        apply Znth_In; rewrite Zlength_combine, Z.min_l; auto; omega. }
      exploit (Forall2_Znth _ _ _ [] [] Hls); eauto.
      intros; subst.
      destruct (Znth i ls1 []); auto.
      destruct (Znth i ls2 []); discriminate.
    + rewrite Forall_forall in *; intros l2 Hin.
      destruct (In_Znth _ _ [] Hin) as (i & ? & ?).
      exploit (Hnil (combine (Znth i ls1 []) l2)).
      { rewrite in_map_iff; eexists (_, _); split; eauto.
        subst; rewrite <- Znth_combine; auto.
        apply Znth_In; rewrite Zlength_combine, Z.min_l; auto; omega. }
      exploit (Forall2_Znth _ _ _ [] [] Hls); [rewrite H; eauto|].
      intros; subst.
      destruct (Znth i ls2 []); auto.
      destruct (Znth i ls1 []); discriminate.
  - destruct l1, l2; try discriminate.
    pose proof (mem_lemmas.Forall2_Zlength Hls).
    inv Heql0; inv Hlen.
    change [] with ((fun x : list A * list B => let '(la, lb) := x in combine la lb) ([], [])) in Hcons.
    rewrite Znth_map', Znth_combine in Hcons; auto.
    destruct (Znth i ls1 []) as [|? la] eqn: Ha1; [discriminate|].
    destruct (Znth i ls2 []) as [|? lb] eqn: Ha2; [discriminate|].
    inv Hcons.
    exploit (Znth_inbounds i ls1 []); [rewrite Ha1; discriminate | intro].
    exploit (IHinterleave (upd_Znth i ls1 la) (upd_Znth i ls2 lb)); eauto.
    { apply Forall2_upd_Znth; auto; [|omega].
      exploit (Forall2_Znth _ _ _ [] [] Hls); eauto.
      rewrite Ha1, Ha2; intro Hlen; inv Hlen; auto. }
    { change (combine la lb) with ((fun x : list A * list B => let '(la, lb) := x in combine la lb) (la, lb)).
      rewrite upd_Znth_map, combine_upd_Znth; auto. }
    intros (? & ?); split; econstructor; eauto.
Qed.

Fixpoint total_length {A} (l : list (list A)) :=
  match l with
  | [] => 0
  | l :: rest => Zlength l + total_length rest
  end.

Lemma total_length_app : forall {A} (l1 l2 : list (list A)),
  total_length (l1 ++ l2) = total_length l1 + total_length l2.
Proof.
  induction l1; auto; intros; simpl.
  rewrite IHl1; omega.
Qed.

Lemma total_length_upd : forall {A} ls i (l : list A), 0 <= i < Zlength ls ->
  total_length (upd_Znth i ls l) = total_length ls - Zlength (Znth i ls []) + Zlength l.
Proof.
  intros; unfold upd_Znth.
  replace ls with (sublist 0 i ls ++ sublist i (Zlength ls) ls) at 4.
  rewrite !total_length_app; simpl.
  rewrite sublist_next with (i0 := i)(d := []); auto; try omega.
  simpl; omega.
  { rewrite <- sublist_split, sublist_same; auto; omega. }
Qed.

Lemma Zlength_interleave : forall {A} ls (l : list A), interleave ls l ->
  Zlength l = total_length ls.
Proof.
  induction 1.
  - rewrite Zlength_nil.
    induction ls; auto; simpl.
    inv Hnil.
    rewrite Zlength_nil, <- IHls; auto.
  - exploit (Znth_inbounds i ls []); [rewrite Hcons; discriminate | intro].
    rewrite total_length_upd, Hcons in IHinterleave; auto.
    rewrite Zlength_cons in *; omega.
Qed.
