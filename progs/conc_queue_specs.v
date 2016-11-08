Require Import progs.conclib.
Require Import progs.conc_queue.
Require Import SetoidList.
Require Import floyd.library.

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

Inductive hist_el {t} := QAdd (p : val) (v : reptype t) | QRem (p : val) (v : reptype t).
Notation hist t := (list (@hist_el t)).
Fixpoint consistent {t} (h : hist t) a b :=
  match h with
  | [] => a = b
  | QAdd p v :: h' => consistent h' (a ++ [(p, v)]) b
  | QRem p v :: h' => match a with [] => False | v' :: q' => v' = (p, v) /\ consistent h' q' b end
  end.

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

Axiom ghost_share_join : forall sh1 sh2 sh t (h1 h2 : hist t) p, sepalg.join sh1 sh2 Tsh -> list_incl h1 h2 ->
  ghost sh1 (sh, h1) p * ghost sh2 (Tsh, h2) p = ghost Tsh (Tsh, h2) p.
Axiom hist_share_join : forall sh sh1 sh2 sh' t (h1 h2 : hist t) p, sepalg.join sh1 sh2 sh' ->
  ghost sh (sh1, h1) p * ghost sh (sh2, h2) p = ghost sh (sh', h1 ++ h2) p.
Axiom hist_add : forall {CS : compspecs} {Espec : OracleKind} D P Q R C P' t (h : hist t) e p,
  semax D (PROPx P (LOCALx Q (SEPx (ghost Tsh (Tsh, h ++ [e]) p :: R)))) C P' ->
  semax D (PROPx P (LOCALx Q (SEPx (ghost Tsh (Tsh, h) p :: R)))) C P'.
Axiom ghost_inj : forall sh1 sh2 sh t (h1 h2 : hist t) p, ghost sh1 (sh, h1) p * ghost sh2 (Tsh, h2) p
  |-- !!(list_incl h1 h2).
Axiom ghost_inj_Tsh : forall sh1 sh2 t (h1 h2 : hist t) p, ghost sh1 (Tsh, h1) p * ghost sh2 (Tsh, h2) p
  |-- !!(h1 = h2).

(*Axiom ghost_conflict : forall sh1 sh2 t1 t2 v1 v2 p,
  ghost sh1 t1 v1 p * ghost sh2 t2 v2 p |-- !!sepalg.joins sh1 sh2.*)

Definition q_lock_pred' t P p vals head (addc remc : val) lock gsh h :=
  !!(Zlength vals <= MAX /\ 0 <= head < MAX /\ consistent h [] vals) &&
  (data_at Tsh tqueue (rotate (complete MAX (map fst vals)) head MAX, (vint (Zlength vals),
                      (vint head, (vint ((head + Zlength vals) mod MAX), (addc, remc))))) p *
   cond_var Tsh addc * cond_var Tsh remc * malloc_token Tsh (sizeof tqueue_t) p *
   malloc_token Tsh (sizeof tcond) addc * malloc_token Tsh (sizeof tcond) remc *
   malloc_token Tsh (sizeof tlock) lock * ghost gsh (Tsh, h) p *
   fold_right sepcon emp (map (fun x => let '(p, v) := x in 
     !!(P v) && (data_at Tsh t v p * malloc_token Tsh (sizeof t) p)) vals)).

Definition q_lock_pred t P p lock gsh := EX vals : list (val * reptype t), EX head : Z,
  EX addc : val, EX remc : val, EX h : hist t, q_lock_pred' t P p vals head addc remc lock gsh h.

Definition lqueue lsh t P p lock gsh1 gsh2 (h : hist t) :=
  !!(sepalg.join gsh1 gsh2 Tsh /\ field_compatible tqueue_t [] p) &&
  (field_at lsh tqueue_t [StructField _lock] lock p *
   lock_inv lsh lock (q_lock_pred t P p lock gsh2) * ghost gsh1 (lsh, h) p).

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

Definition q_del_spec' :=
  WITH Q : {t : type & ((reptype t -> Prop) * hist t)%type}, p : val, lock : val, gsh1 : share, gsh2 : share
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

Definition q_add_spec' :=
  WITH sh : share, Q : {t : type & ((reptype t -> Prop) * hist t * reptype t)%type}, p : val, lock : val,
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

Definition q_remove_spec' :=
  WITH sh : share, Q : {t : type & ((reptype t -> Prop) * hist t)%type}, p : val, lock : val, gsh1 : share, gsh2 : share
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
  WITH sh : share, Q : {t : type & ((reptype t -> Prop) * hist t)%type}, p : val, lock : val, gsh1 : share, gsh2 : share
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

Lemma lqueue_share_join : forall t P sh1 sh2 sh p lock gsh1 gsh2 h1 h2
  (Hsh1 : readable_share sh1) (Hsh2 : readable_share sh2) (Hjoin : sepalg.join sh1 sh2 sh),
  lqueue sh1 t P p lock gsh1 gsh2 h1 * lqueue sh2 t P p lock gsh1 gsh2 h2 =
  lqueue sh t P p lock gsh1 gsh2 (h1 ++ h2).
Proof.
  intros; unfold lqueue; normalize.
  f_equal.
  - f_equal; apply prop_ext; tauto.
  - erewrite <- (field_at_share_join _ _ _ _ _ _ _ Hjoin), <- (lock_inv_share_join sh1 sh2 sh),
      <- (hist_share_join _ _ _ _ _ _ _ _ Hjoin); auto.
    rewrite <- !sepcon_assoc, !sepcon_assoc; f_equal.
    rewrite <- sepcon_assoc, sepcon_comm, sepcon_assoc; f_equal.
    rewrite sepcon_comm, sepcon_assoc; f_equal.
    rewrite sepcon_comm, sepcon_assoc; f_equal.
    rewrite sepcon_comm; reflexivity.
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

Axiom ghost_precise : forall sh {t} p, precise (EX f : share * hist t, ghost sh f p).

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
  precise (EX h : hist t, lqueue lsh t P p lock gsh1 gsh2 h).
Proof.
  intros; unfold lqueue.
  apply derives_precise' with (Q := field_at lsh tqueue_t [StructField conc_queue._lock] lock p *
    lock_inv lsh lock (q_lock_pred t P p lock gsh2) * EX f : share * hist t, ghost gsh1 f p).
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
