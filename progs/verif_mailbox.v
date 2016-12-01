Require Import veric.rmaps.
Require Import progs.conclib.
Require Import floyd.library.
Require Import floyd.sublist.
Require Import progs.mailbox.

Set Bullet Behavior "Strict Subproofs".

(* up *)
Lemma sepcon_derives_prop : forall P Q R, P |-- !!R -> P * Q |-- !!R.
Proof.
  intros; eapply derives_trans; [apply saturate_aux20 with (Q' := True); eauto|].
  - entailer!.
  - apply prop_left; intros (? & ?); apply prop_right; auto.
Qed.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition acquire_spec := DECLARE _acquire acquire_spec.
Definition release_spec := DECLARE _release release_spec.
Definition makelock_spec := DECLARE _makelock (makelock_spec _).
(*Definition freelock_spec := DECLARE _freelock (freelock_spec _).
Definition spawn_spec := DECLARE _spawn spawn_spec.
Definition freelock2_spec := DECLARE _freelock2 (freelock2_spec _).
Definition release2_spec := DECLARE _release2 release2_spec.
Definition makecond_spec := DECLARE _makecond (makecond_spec _).
Definition freecond_spec := DECLARE _freecond (freecond_spec _).
Definition wait_spec := DECLARE _waitcond (wait2_spec _).
Definition signal_spec := DECLARE _signalcond (signal_spec _).*)

Definition surely_malloc_spec :=
 DECLARE _surely_malloc
   WITH n:Z
   PRE [ _n OF tuint ]
       PROP (0 <= n <= Int.max_unsigned)
       LOCAL (temp _n (Vint (Int.repr n)))
       SEP ()
    POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP (malloc_token Tsh n p * memory_block Tsh n p).

Definition memset_spec :=
 DECLARE _memset
  WITH sh : share, t : type, p : val, c : Z, n : Z
  PRE [ _s OF tptr tvoid, _c OF tint, _n OF tuint ]
   PROP (writable_share sh; sizeof t = n; n <= Int.max_unsigned; 0 <= c <= two_p 8 - 1)
   LOCAL (temp _s p; temp _c (vint c); temp _n (vint n))
   SEP (data_at_ sh t p)
  POST [ tptr tvoid ]
   PROP ()
   LOCAL (temp ret_temp p)
   SEP (data_at sh (tarray tuchar n) (repeat (vint c) (Z.to_nat n)) p).

Definition N := 3.
Definition B := N + 2.

Definition tbuffer := Tstruct _buffer noattr.

(*(* There are two invisible invariants: the last buffer written, and the buffer being read by each reader. *)
(* I think this can't be done with just ghost variables, though, since the readers want to track the value
   that the writer can update, and vice versa. Maybe it's more like the session type model, with views
   of a shared state machine. *)
(* For each reader, there's a pair of currently-reading and most-recently-published. *)
(* States:
   If currently-reading = most-recently-published, then comm[r] is Empty.
   Otherwise, comm[r] is most-recently-published.
   Writer can change most-recently-published to anything (...?)
   Reader can change currently-reading to most-recently-published.
 *)
(* From the reader's perspective, bw can be silently replaced with anything (except br).
   From the writer's perspective, br can be silently replaced with bw. *)
Inductive ghost_el := G (r : Z) (bro : Z) (br : Z) (bw : Z) | R (r : Z) (br : Z) | W (brs : list Z) (bw : Z).
Definition consistent1 m n :=
  match m with
  | G r bro br bw => match n with
                | R r' br' => r = r' /\ br = br'
                | W brs' bw' => Zlength brs' = N /\ bw' = bw /\ (Znth r brs' (-2) = br \/ (br = bw /\ Znth r brs' (-2) = bro))
                | G r' bro' br' bw' => (*bw' = bw /\ r <> r'*) False
                end
  | R r br => match n with
              | G r' bro br' bw => r = r' /\ br = br'
              | W brs bw => Zlength brs = N /\ (Znth r brs (-2) = br \/ br = bw)
              | _ => False
              end
  | W brs' bw' => Zlength brs' = N /\ match n with
                | G r bro br bw => bw' = bw /\ (Znth r brs' (-2) = br \/ (br = bw /\ Znth r brs' (-2) = bro))
                | R r br => Znth r brs' (-2) = br \/ br = bw'
                | _ => False
                end
  end.
Fixpoint consistent l :=
  match l with
  | [] => True
  | a :: rest => Forall (consistent1 a) rest /\ consistent rest
  end.
Definition view_shift m n := forall p, consistent (m ++ p) -> consistent (n ++ p).

Parameter ghost : list ghost_el -> mpred.
Axiom ghost_shift : forall Espec D P Q R C P' l l',
  view_shift l l' ->
  semax(Espec := Espec) D (PROPx P (LOCALx Q (SEPx (ghost l' :: R)))) C P' ->
  semax D (PROPx P (LOCALx Q (SEPx (ghost l :: R)))) C P'.
Axiom ghost_consistent : forall l, ghost l |-- !!consistent l.
Axiom ghost_join : forall l l', ghost l * ghost l' = ghost (l ++ l').*)

(* Ghost histories in the style of
   History-based Verification of Functional Behaviour of Concurrent Programs,
   Blom, Huisman, and Zharieva-Stojanovski (VerCors)
   Twente tech report, 2015 *)

(* These histories should be usable for any atomically accessed int-valued location. *)
Inductive hist_el := AE (r : Z) (w : Z).
Notation hist := (list hist_el).
Fixpoint apply_hist a h :=
  match h with
  | [] => Some a
  | AE r w :: h' => match apply_hist a h' with Some a' => if eq_dec a' r then Some w else None | _ => None end
  end.

Parameter ghost :
  forall (sh : share) (i : Z) (f : share * hist) (p : val), mpred.

Axiom new_ghost : forall {CS : compspecs} {Espec : OracleKind} D P Q R C P' t i v p,
  semax D (PROPx P (LOCALx Q (SEPx (ghost Tsh i (Tsh, []) p :: data_at Tsh t v p :: R)))) C P' ->
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

Axiom ghost_share_join : forall sh1 sh2 i sh h1 h2 p, sepalg.join sh1 sh2 Tsh -> list_incl h1 h2 ->
  ghost sh1 i (sh, h1) p * ghost sh2 i (Tsh, h2) p = ghost Tsh i (Tsh, h2) p.
Axiom hist_share_join : forall sh sh1 sh2 i sh' h1 h2 p, sepalg.join sh1 sh2 sh' ->
  ghost i sh (sh1, h1) p * ghost i sh (sh2, h2) p = EX h' : hist, !!(interleave [h1; h2] h') && ghost i sh (sh', h') p.
Axiom hist_add : forall {CS : compspecs} {Espec : OracleKind} D P Q R C P' i h e p,
  apply_hist i (e :: h) <> None ->
  semax D (PROPx P (LOCALx Q (SEPx (ghost Tsh i (Tsh, e :: h) p :: R)))) C P' ->
  semax D (PROPx P (LOCALx Q (SEPx (ghost Tsh i (Tsh, h) p :: R)))) C P'.
Axiom ghost_inj : forall sh1 sh2 i sh h1 h2 p, ghost sh1 i (sh, h1) p * ghost sh2 i (Tsh, h2) p
  |-- !!(list_incl h1 h2).
Axiom ghost_inj_Tsh : forall sh1 sh2 i h1 h2 p, ghost sh1 i (Tsh, h1) p * ghost sh2 i (Tsh, h2) p
  |-- !!(h1 = h2).
(* Should this be an axiom? *)
Axiom ghost_feasible : forall sh i h p, ghost sh i (Tsh, h) p |-- !!(apply_hist i h <> None).
Axiom ghost_conflict : forall sh1 sh2 i v1 v2 p,
  ghost sh1 i v1 p * ghost sh2 i v2 p |-- !!sepalg.joins sh1 sh2.

(* up *)
Lemma field_at_array_inbounds : forall sh t z a i v p,
  field_at sh (Tarray t z a) [ArraySubsc i] v p |-- !!(0 <= i < z).
Proof.
  intros; entailer!.
  destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & ?); auto.
Qed.

(* How can we generalize this? *)
(*Definition atomic_exchange_spec :=
 DECLARE _simulate_atomic_exchange
  WITH r : Z, v : Z, lock : val, locks : list val, comm : val, comms : list val, bufs : list val,
    sh1 : share, sh2 : share, g : ghost_el, brs : list Z, b : Z, v1 : Z, bsh2 : share
  PRE [ _r OF tint, _v OF tint ]
   PROP (readable_share sh1; readable_share sh2; repable_signed v; -1 <= v < B;
         if eq_dec v (-1) then g = R r b else g = W brs b /\ b <> v /\ Forall (fun x => x <> v) brs)
   LOCAL (temp _r (vint r); temp _v (vint v); gvar _lock lock; gvar _comm comm)
   SEP (data_at sh1 (tarray (tptr tint) N) comms comm;
        data_at sh1 (tarray (tptr tlock) N) locks lock;
        lock_inv sh2 (Znth r locks Vundef) (comm_inv (Znth r comms Vundef) bufs r bsh2); ghost gsh1 (sh, h) (Znth r comms Vundef);
        data_at bsh2 tbuffer (vint v1) (Znth (if eq_dec v (-1) then b else v) bufs Vundef))
  POST [ tint ]
   EX g' : ghost_el, EX v' : Z, EX v1 : Z,
   PROP (if eq_dec v (-1) then g' = R r (if eq_dec v' (-1) then b else v')
         else g' = W (if eq_dec v' (-1) then upd_Znth r brs b else brs) v; -1 <= v' < B)
   LOCAL (temp ret_temp (vint v'))
   SEP (data_at sh1 (tarray (tptr tint) N) comms comm;
        data_at sh1 (tarray (tptr tlock) N) locks lock;
        lock_inv sh2 (Znth r locks Vundef) (comm_inv (Znth r comms Vundef) bufs r bsh2);
        ghost gsh1 (sh, AE v' v :: h) (Znth r comms Vundef);
        data_at bsh2 tbuffer (vint v1)
          (Znth (if eq_dec v' (-1) then (if eq_dec v (-1) then b else Znth r brs (-1)) else v') bufs Vundef)).*)

Definition AE_inv x i sh gsh R := EX h : hist, EX v : Z,
  !!(apply_hist i h = Some v /\ repable_signed v) &&
  (data_at sh tint (vint v) x * ghost gsh i (Tsh, h) x * R h v * (weak_precise_mpred (R h v) && emp)).

Axiom ghost_inj' : forall sh i p h1 h2 r1 r2 r
  (Hp1 : predicates_hered.app_pred (ghost sh i (Tsh, h1) p) r1)
  (Hp1 : predicates_hered.app_pred (ghost sh i (Tsh, h2) p) r2)
  (Hr1 : sepalg.join_sub r1 r) (Hr2 : sepalg.join_sub r2 r),
  r1 = r2 /\ h1 = h2.

Arguments eq_dec _ _ _ _ : simpl never.

Lemma AE_inv_positive : forall x i sh gsh R, readable_share sh -> positive_mpred (AE_inv x i sh gsh R).
Proof.
  unfold AE_inv; intros.
  do 2 (apply ex_positive; intro).
  apply positive_andp2, positive_sepcon1, positive_sepcon1, positive_sepcon1; auto.
Qed.
Hint Resolve AE_inv_positive.

Lemma AE_inv_precise : forall x i sh gsh R (Hsh : readable_share sh),
  predicates_hered.derives TT (weak_precise_mpred (AE_inv x i sh gsh R)).
Proof.
  intros ?????? rho _ ???
    (? & h1 & v1 & (Hh1 & ?) & ? & ? & Hj1 & (? & ? & Hj'1 & (? & ? & ? & (? & Hv1) & Hg1) & HR1) & (HR & Hemp1))
    (? & h2 & v2 & (Hh2 & ?) & ? & ? & Hj2 & (? & ? & Hj'2 & (? & ? & ? & (? & Hv2) & Hg2) & HR2) & (_ & Hemp2))
    Hw1 Hw2.
  unfold at_offset in *; simpl in *; rewrite data_at_rec_eq in Hv1, Hv2; simpl in *.
  exploit (mapsto_inj _ _ _ _ _ _ _ w Hsh Hv1 Hv2); auto; try join_sub.
  { unfold unfold_reptype; simpl; discriminate. }
  { unfold unfold_reptype; simpl; discriminate. }
  unfold unfold_reptype; simpl; intros (? & Hv).
  assert (v1 = v2).
  { apply repr_inj_signed; auto; congruence. }
  exploit (ghost_inj' _ _ _ _ _ _ _ w Hg1 Hg2); try join_sub.
  intros (? & ?); subst.
  destruct (age_sepalg.join_level _ _ _ Hj1).
  exploit HR.
  { split; [|apply HR1].
    destruct (age_sepalg.join_level _ _ _ Hj'1); omega. }
  { split; [|apply HR2].
    pose proof (juicy_mem.rmap_join_sub_eq_level _ _ Hw1).
    pose proof (juicy_mem.rmap_join_sub_eq_level _ _ Hw2).
    destruct (age_sepalg.join_level _ _ _ Hj2), (age_sepalg.join_level _ _ _ Hj'2); omega. }
  { join_sub. }
  { join_sub. }
  intro; join_inj.
  apply sepalg.join_comm in Hj1; apply sepalg.join_comm in Hj2.
  match goal with H1 : predicates_hered.app_pred emp ?a,
    H2 : predicates_hered.app_pred emp ?b |- _ => assert (a = b);
      [eapply sepalg.same_identity; auto;
        [match goal with H : sepalg.join a ?x ?y |- _ =>
           specialize (Hemp1 _ _ H); instantiate (1 := x); subst; auto end |
         match goal with H : sepalg.join b ?x ?y |- _ =>
           specialize (Hemp2 _ _ H); subst; auto end] | subst] end.
  join_inj.
Qed.

Definition AE_spec i Rc Rx Rc' := forall hc hx vc vx, apply_hist i hx = Some vx ->
  Rx hx vx * Rc hc vc |--
  Rx (AE vx vc :: hx) vc * (weak_precise_mpred (Rx (AE vx vc :: hx) vc) && emp) * Rc' (AE vx vc :: hc) vx.

Definition AE_type := ProdType (ProdType (ProdType
  (ConstType (share * share * share * share * share * val * val * Z * Z * hist))
  (ArrowType (ConstType hist) (ArrowType (ConstType Z) Mpred)))
  (ArrowType (ConstType hist) (ArrowType (ConstType Z) Mpred)))
  (ArrowType (ConstType hist) (ArrowType (ConstType Z) Mpred)).

Program Definition atomic_exchange_spec := DECLARE _simulate_atomic_exchange
  mk_funspec ([(_tgt, tptr tint); (_l, tptr (Tstruct _lock_t noattr)); (_v, tint)], tint) cc_default AE_type
  (fun (ts: list Type) (x: share * share * share * share * share * val * val * Z * Z * hist *
                           (hist -> Z -> mpred) * (hist -> Z -> mpred) * (hist -> Z -> mpred)) =>
     let '(ish, lsh, gsh1, gsh2, hsh, tgt, l, i, v, h, Rc, Rx, Rc') := x in
     PROP (readable_share lsh; writable_share ish; sepalg.join gsh1 gsh2 Tsh; repable_signed v; AE_spec i Rc Rx Rc')
     LOCAL (temp _tgt tgt; temp _l l; temp _v (vint v))
     SEP (lock_inv lsh l (AE_inv tgt i ish gsh2 Rx); ghost gsh1 i (hsh, h) tgt; Rc h v;
          weak_precise_mpred (Rc h v) && emp))
  (fun (ts: list Type) (x: share * share * share * share * share * val * val * Z * Z * hist *
                           (hist -> Z -> mpred) * (hist -> Z -> mpred) * (hist -> Z -> mpred)) =>
     let '(ish, lsh, gsh1, gsh2, hsh, tgt, l, i, v, h, Rc, Rx, Rc') := x in
     EX v' : Z,
     PROP ()
     LOCAL (temp ret_temp (vint v'))
     SEP (lock_inv lsh l (AE_inv tgt i ish gsh2 Rx);
          ghost gsh1 i (hsh, AE v' v :: h) tgt; Rc' (AE v' v :: h) v')) _ _.
Next Obligation.
Proof.
  replace _ with (fun (_ : list Type)
    (x : share * share * share * share * share * val * val * Z * Z * hist *
         (hist -> Z -> mpred) * (hist -> Z -> mpred) * (hist -> Z -> mpred)) rho =>
    PROP (let '(ish, lsh, gsh1, gsh2, hsh, tgt, l, i, v, h, Rc, Rx, Rc') := x in readable_share lsh /\
      writable_share ish /\ sepalg.join gsh1 gsh2 Tsh /\ repable_signed v /\ AE_spec i Rc Rx Rc')
    LOCAL (let '(ish, lsh, gsh1, gsh2, hsh, tgt, l, i, v, h, Rc, Rx, Rc') := x in temp _tgt tgt;
           let '(ish, lsh, gsh1, gsh2, hsh, tgt, l, i, v, h, Rc, Rx, Rc') := x in temp _l l;
           let '(ish, lsh, gsh1, gsh2, hsh, tgt, l, i, v, h, Rc, Rx, Rc') := x in temp _v (vint v))
    SEP (let '(ish, lsh, gsh1, gsh2, hsh, tgt, l, i, v, h, Rc, Rx, Rc') := x in
         lock_inv lsh l (AE_inv tgt i ish gsh2 Rx) * ghost gsh1 i (hsh, h) tgt * Rc h v *
         (weak_precise_mpred (Rc h v) && emp)) rho).
  apply (PROP_LOCAL_SEP_super_non_expansive AE_type [fun _ => _] [fun _ => _; fun _ => _; fun _ => _]
    [fun _ => _]); repeat constructor; hnf; intros;
    destruct x as ((((((((((((?, ?), ?), ?), ?), ?), ?), ?), ?), ?), Rc), Rx), Rc'); auto; simpl.
  - unfold AE_spec.
    Print compcert_rmaps.RML.R.approx.
    (* I think these do actually derive each other. *) admit.
  - rewrite !approx_sepcon; f_equal; [f_equal|].
    + f_equal.
      rewrite (nonexpansive_super_non_expansive (fun R => lock_inv s0 v0 R)); [|apply nonexpansive_lock_inv].
      setoid_rewrite (nonexpansive_super_non_expansive (fun R => lock_inv s0 v0 R)) at 2; [|apply nonexpansive_lock_inv].
      f_equal; f_equal.
      unfold AE_inv; rewrite !approx_exp; f_equal; extensionality l'.
      rewrite !approx_exp; f_equal; extensionality z'.
      rewrite !approx_andp, !approx_sepcon; f_equal; f_equal.
      * replace (compcert_rmaps.RML.R.approx n (Rx l' z')) with
          (base.compose (compcert_rmaps.R.approx n) (compcert_rmaps.R.approx n) (Rx l' z')) at 1
          by (rewrite compcert_rmaps.RML.approx_oo_approx; auto); auto.
      * rewrite !approx_andp; f_equal.
        apply (nonexpansive_super_non_expansive), precise_mpred_nonexpansive.
    + replace (compcert_rmaps.RML.R.approx n (Rc l z0)) with
        (base.compose (compcert_rmaps.R.approx n) (compcert_rmaps.R.approx n) (Rc l z0)) at 1
        by (rewrite compcert_rmaps.RML.approx_oo_approx; auto); auto.
    + rewrite !approx_andp; f_equal.
      apply (nonexpansive_super_non_expansive), precise_mpred_nonexpansive.
  - extensionality ts x rho.
    destruct x as ((((((((((((?, ?), ?), ?), ?), ?), ?), ?), ?), ?), Rc), Rx), Rc'); auto.
    unfold PROPx, SEPx; simpl; rewrite !sepcon_assoc; f_equal.
    f_equal; apply prop_ext; tauto.
Admitted.
Next Obligation.
Proof.
  replace _ with (fun (_ : list Type)
    (x : share * share * share * share * share * val * val * Z * Z * hist *
         (hist -> Z -> mpred) * (hist -> Z -> mpred) * (hist -> Z -> mpred)) rho =>
    EX v' : Z, PROP () LOCAL (let '(ish, lsh, gsh1, gsh2, hsh, tgt, l, i, v, h, Rc, Rx, Rc') := x in temp ret_temp (vint v'))
    SEP (let '(ish, lsh, gsh1, gsh2, hsh, tgt, l, i, v, h, Rc, Rx, Rc') := x in
         lock_inv lsh l (AE_inv tgt i ish gsh2 Rx) * ghost gsh1 i (hsh, AE v' v :: h) tgt * Rc' (AE v' v :: h) v') rho).
  repeat intro.
  rewrite !approx_exp; f_equal; extensionality v'.
  pose proof (PROP_LOCAL_SEP_super_non_expansive AE_type []
    [fun ts x => let '(_, _, _, _, _, _, _, _, _, _, _, _, _) := x in temp ret_temp (vint v')]
    [fun ts x => let '(ish, lsh, gsh1, gsh2, hsh, tgt, l, i, v, h, Rc, Rx, Rc') := x in
       lock_inv lsh l (AE_inv tgt i ish gsh2 Rx) * ghost gsh1 i (hsh, AE v' v :: h) tgt * Rc' (AE v' v :: h) v'])
    as Heq; apply Heq; repeat constructor; hnf; intros;
      destruct x0 as ((((((((((((?, ?), ?), ?), ?), ?), ?), ?), ?), ?), Rc), Rx), Rc'); auto; simpl.
  - rewrite !approx_sepcon; f_equal.
    + rewrite (nonexpansive_super_non_expansive (fun R => lock_inv s0 v0 R)); [|apply nonexpansive_lock_inv].
      f_equal.
      setoid_rewrite (nonexpansive_super_non_expansive (fun R => lock_inv s0 v0 R)) at 2; [|apply nonexpansive_lock_inv].
      f_equal; f_equal.
      unfold AE_inv; rewrite !approx_exp; f_equal; extensionality l'.
      rewrite !approx_exp; f_equal; extensionality z'.
      rewrite !approx_andp, !approx_sepcon; f_equal; f_equal.
      * replace (compcert_rmaps.RML.R.approx n0 (Rx l' z')) with
          (base.compose (compcert_rmaps.R.approx n0) (compcert_rmaps.R.approx n0) (Rx l' z')) at 1
          by (rewrite compcert_rmaps.RML.approx_oo_approx; auto); auto.
      * rewrite !approx_andp; f_equal.
        apply (nonexpansive_super_non_expansive), precise_mpred_nonexpansive.
    + replace (compcert_rmaps.RML.R.approx n0 (Rc' _ v')) with
        (base.compose (compcert_rmaps.R.approx n0) (compcert_rmaps.R.approx n0) (Rc' (AE v' z0 :: l) v')) at 1
        by (rewrite compcert_rmaps.RML.approx_oo_approx; auto); auto.
  - extensionality ts x rho.
    destruct x as ((((((((((((?, ?), ?), ?), ?), ?), ?), ?), ?), ?), Rc), Rx), Rc'); auto.
    f_equal; extensionality.
    unfold SEPx; simpl; rewrite !sepcon_assoc; auto.
Qed.

Fixpoint last_read h :=
  match h with
  | [] => None
  | AE r w :: rest => if eq_dec w (-1) then if eq_dec r (-1) then last_read rest
                      else Some (r, rest) else last_read rest
  end.
Definition prev_read h := match last_read h with Some (_, rest) =>
  match last_read rest with Some (r, _) => Some r | _ => None end | _ => None end.

Definition comm_R bufs sh h b := !!(-1 <= b < B) && EX v : Z, if eq_dec b (-1) then
  match prev_read h with Some b' => data_at sh tbuffer (vint v) (Znth b' bufs Vundef)
  | None => emp end
  else data_at sh tbuffer (vint v) (Znth b bufs Vundef).

Definition comm_inv comm bufs sh gsh := AE_inv comm (-1) Tsh gsh (comm_R bufs sh).

Definition initialize_channels_spec :=
 DECLARE _initialize_channels
  WITH comm : val, lock : val, buf : val, reading : val, last_given : val, gsh1 : share, gsh2 : share,
    sh1 : share, shs : list share
  PRE [ ]
   PROP (sepalg.join gsh1 gsh2 Tsh; sepalg_list.list_join sh1 shs Tsh)
   LOCAL (gvar _comm comm; gvar _lock lock; gvar _bufs buf)
   SEP (data_at_ Ews (tarray (tptr tint) N) comm; data_at_ Ews (tarray (tptr tlock) N) lock;
        data_at_ Ews (tarray (tptr tbuffer) B) buf)
  POST [ tvoid ]
   EX comms : list val, EX locks : list val, EX bufs : list val,
   PROP ()
   LOCAL ()
   SEP (data_at Ews (tarray (tptr tint) N) comms comm;
        data_at Ews (tarray (tptr tlock) N) locks lock;
        data_at Ews (tarray (tptr tbuffer) B) bufs buf;
        fold_right sepcon emp (map (fun r =>
          lock_inv Tsh (Znth r locks Vundef) (comm_inv (Znth r comms Vundef) bufs (Znth r shs Tsh) gsh2))
          (upto (Z.to_nat N)));
        fold_right sepcon emp (map (ghost gsh1 (-1) (Tsh, [])) comms);
        fold_right sepcon emp (map (malloc_token Tsh (sizeof tint)) comms);
        fold_right sepcon emp (map (malloc_token Tsh (sizeof tlock)) locks);
        fold_right sepcon emp (map (malloc_token Tsh (sizeof tbuffer)) bufs);
        fold_right sepcon emp (map (data_at_ Tsh tbuffer) bufs)).
(* All the communication channels are now inside locks. *)

Definition initialize_reader_spec :=
 DECLARE _initialize_reader
  WITH r : Z, reading : val, last_read : val
  PRE [ _r OF tint ]
   PROP ()
   LOCAL (temp _r (vint r); gvar _reading reading; gvar _last_read last_read)
   SEP (field_at_ Ews (tarray tint N) [ArraySubsc r] reading;
        field_at_ Ews (tarray tint N) [ArraySubsc r] last_read)
  POST [ tvoid ]
   PROP ()
   LOCAL ()
   SEP (field_at Ews (tarray tint N) [ArraySubsc r] (vint (-1)) reading;
        field_at Ews (tarray tint N) [ArraySubsc r] (vint 0) last_read).

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, 
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0,  x13 at level 0, x14 at level 0, x15 at level 0,
             P at level 100, Q at level 100).

(* last_read retains the last buffer read, while reading is reset to Empty. *)
Definition start_read_spec :=
 DECLARE _start_read
  WITH r : Z, reading : val, last_read : val, lock : val, comm : val, c : val, bufs : list val,
    sh : share, sh1 : share, sh2 : share, l : val, b0 : Z, gsh1 : share, gsh2 : share, h : hist
  PRE [ _r OF tint ]
   PROP (readable_share sh; readable_share sh1; readable_share sh2; sepalg.join gsh1 gsh2 Tsh; isptr c)
   LOCAL (temp _r (vint r); gvar _reading reading; gvar _last_read last_read; gvar _lock lock; gvar _comm comm)
   SEP (field_at_ Ews (tarray tint N) [ArraySubsc r] reading;
        field_at Ews (tarray tint N) [ArraySubsc r] (vint b0) last_read;
        field_at sh1 (tarray (tptr tint) N) [ArraySubsc r] c comm;
        field_at sh1 (tarray (tptr tlock) N) [ArraySubsc r] l lock;
        lock_inv sh2 l (comm_inv c bufs sh gsh2);
        EX v : Z, data_at sh tbuffer (vint v) (Znth b0 bufs Vundef);
        ghost gsh1 (-1) (sh2, h) c)
  POST [ tvoid ]
   EX b : Z, EX v0 : Z, EX v : Z,
   PROP ()
   LOCAL ()
   SEP (field_at Ews (tarray tint N) [ArraySubsc r] (vint b) reading;
        field_at Ews (tarray tint N) [ArraySubsc r] (vint b) last_read;
        field_at sh1 (tarray (tptr tint) N) [ArraySubsc r] c comm;
        field_at sh1 (tarray (tptr tlock) N) [ArraySubsc r] l lock;
        lock_inv sh2 l (comm_inv c bufs sh gsh2);
        data_at sh tbuffer (vint v) (Znth b bufs Vundef);
        ghost gsh1 (-1) (sh2, AE v0 (-1) :: h) c).
(* And bufs[b] is the most recent buffer completed by finish_write. *)

Definition finish_read_spec :=
 DECLARE _finish_read
  WITH r : Z, reading : val, bufs : val, sh : share, b : Z
  PRE [ _r OF tint ]
   PROP (readable_share sh)
   LOCAL (temp _r (vint r); gvar _reading reading)
   SEP (field_at Ews (tarray tint N) [ArraySubsc r] (vint b) reading)
  POST [ tvoid ]
   PROP ()
   LOCAL ()
   SEP (field_at Ews (tarray tint N) [ArraySubsc r] (vint (-1)) reading).

Definition initialize_writer_spec :=
 DECLARE _initialize_writer
  WITH writing : val, last_given : val, last_taken : val
  PRE [ ]
   PROP ()
   LOCAL (gvar _writing writing; gvar _last_given last_given; gvar _last_taken last_taken)
   SEP (data_at_ Ews tint writing; data_at_ Ews tint last_given;
        data_at_ Ews (tarray tint N) last_taken)
  POST [ tvoid ]
   PROP ()
   LOCAL ()
   SEP (data_at Ews tint (vint (-1)) writing; data_at Ews tint (vint 0) last_given;
        data_at Ews (tarray tint N) (repeat (vint (-1)) (Z.to_nat N)) last_taken).

Definition start_write_spec :=
 DECLARE _start_write
  WITH gsh1 : share, writing : val, last_given : val, last_taken : val, reading : val, b0 : Z, lasts : list Z
  PRE [ ]
   PROP (0 <= b0 < B; Forall (fun x => -1 <= x < B) lasts)
   LOCAL (gvar _writing writing; gvar _last_given last_given; gvar _last_taken last_taken; gvar _reading reading)
   SEP (data_at_ Ews tint writing; data_at Ews tint (vint b0) last_given;
        data_at Ews (tarray tint N) (map (fun x => vint x) lasts) last_taken)
  POST [ tint ]
   EX b : Z,
   PROP (0 <= b < B; b <> b0; ~In b lasts)
   LOCAL (temp ret_temp (vint b))
   SEP (data_at Ews tint (vint b) writing; data_at Ews tint (vint b0) last_given;
        data_at Ews (tarray tint N) (map (fun x => vint x) lasts) last_taken).
(* And b is not in use by any reader. This follows from the property on lasts, but can we relate it to the
   relevant ghost state? *)

Fixpoint make_shares shs (lasts : list Z) i : list share :=
  match lasts with
  | [] => []
  | b :: rest => if eq_dec b i then make_shares (tl shs) rest i
                 else hd Share.bot shs :: make_shares (tl shs) rest i
  end.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 , x17 : t17 , x18 : t18 , x19 : t19 , x20 : t20 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16*t17*t18*t19*t20)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, 
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0,  x13 at level 0, x14 at level 0, x15 at level 0, x16 at level 0, x17 at level 0, x18 at level 0, x19 at level 0, x20 at level 0,
             P at level 100, Q at level 100).

Definition finish_write_spec :=
 DECLARE _finish_write
  WITH writing : val, last_given : val, last_taken : val, comm : val, lock : val,
    comms : list val, locks : list val, bufs : list val, b : Z, b0 : Z, lasts : list Z,
    sh1 : share, sh2 : share, lsh : share, shs : list share, gsh1 : share, gsh2 : share, h : list hist, sh0 : share, v : Z
  PRE [ ]
   PROP (0 <= b < B; 0 <= b0 < B; Forall (fun x => -1 <= x < B) lasts; Zlength h = N; Zlength shs = N;
         readable_share sh1; readable_share lsh; sepalg_list.list_join sh0 shs Tsh; sepalg.join gsh1 gsh2 Tsh;
         Forall isptr comms; b <> b0; ~In b lasts)
   LOCAL (gvar _writing writing; gvar _last_given last_given; gvar _last_taken last_taken; gvar _comm comm;
          gvar _lock lock)
   SEP (data_at Ews tint (vint b) writing; data_at Ews tint (vint b0) last_given;
        data_at Ews (tarray tint N) (map (fun x => vint x) lasts) last_taken;
        data_at sh1 (tarray (tptr tint) N) comms comm;
        data_at sh1 (tarray (tptr tlock) N) locks lock;
        fold_right sepcon emp (map (fun r =>
          lock_inv lsh (Znth r locks Vundef) (comm_inv (Znth r comms Vundef) bufs (Znth r shs Tsh) gsh2))
          (upto (Z.to_nat N)));
        fold_right sepcon emp (map (fun x => let '(c, h) := x in ghost gsh1 (-1) (lsh, h) c) (combine comms h));
        fold_right sepcon emp (map (fun i => EX sh : share,
          !!(if eq_dec i b0 then sh = sh0 else sepalg_list.list_join sh0 (make_shares shs lasts i) sh) &&
          EX v : Z, data_at sh tbuffer (vint v) (Znth i bufs Vundef)) (upto (Z.to_nat B))))
  POST [ tvoid ]
   EX lasts' : list Z, EX h' : list hist,
   PROP (Forall (fun x => -1 <= x < B) lasts'; Forall2 (fun h1 h2 => exists v, h2 = AE v b :: h1) h h')
   LOCAL ()
   SEP (data_at Ews tint (vint (-1)) writing; data_at Ews tint (vint b) last_given;
        data_at Ews (tarray tint N) (map (fun x => vint x) lasts') last_taken;
        data_at sh1 (tarray (tptr tint) N) comms comm;
        data_at sh1 (tarray (tptr tlock) N) locks lock;
        fold_right sepcon emp (map (fun r =>
          lock_inv lsh (Znth r locks Vundef) (comm_inv (Znth r comms Vundef) bufs (Znth r shs Tsh) gsh2))
          (upto (Z.to_nat N)));
        fold_right sepcon emp (map (fun x => let '(c, h) := x in ghost gsh1 (-1) (lsh, h) c) (combine comms h'));
        fold_right sepcon emp (map (fun i => EX sh : share,
          !!(if eq_dec i b then sh = sh0 else sepalg_list.list_join sh0 (make_shares shs lasts' i) sh) &&
          EX v : Z, data_at sh tbuffer (vint v) (Znth i bufs Vundef)) (upto (Z.to_nat B)))).

Definition Gprog : funspecs := ltac:(with_library prog [acquire_spec; release_spec; makelock_spec;
  surely_malloc_spec; memset_spec; atomic_exchange_spec; initialize_channels_spec; initialize_reader_spec;
  start_read_spec; finish_read_spec; initialize_writer_spec; start_write_spec; finish_write_spec]).

Lemma body_surely_malloc: semax_body Vprog Gprog f_surely_malloc surely_malloc_spec.
Proof.
  start_function. 
  forward_call (* p = malloc(n); *)
     n.
  Intros p.
  forward_if
  (PROP ( )
   LOCAL (temp _p p)
   SEP (malloc_token Tsh n p * memory_block Tsh n p)).
*
  if_tac.
    subst p. entailer!.
    entailer!.
*
    forward_call tt.
    contradiction.
*
    if_tac.
    + forward. subst p. inv H0.
    + Intros. forward. entailer!.
*
  forward. Exists p; entailer!.
Qed.

(* up *)
Lemma upd_init : forall {A} (l : list A) i b v v', i < b -> Zlength l = i ->
  upd_Znth i (l ++ repeat v (Z.to_nat (b - i))) v' = l ++ v' :: repeat v (Z.to_nat (b - (i + 1))).
Proof.
  intros.
  rewrite upd_Znth_app2; rewrite ?Zlength_repeat, ?Z2Nat.id; try omega.
  subst; rewrite Zminus_diag, upd_Znth0.
  destruct (Z.to_nat (b - Zlength l)) eqn: Hi.
  { change O with (Z.to_nat 0) in Hi; apply Z2Nat.inj in Hi; omega. }
  simpl; rewrite sublist_1_cons, sublist_same; try rewrite Zlength_cons, !Zlength_repeat; try omega.
  replace (Z.to_nat (b - (Zlength l + 1))) with n; auto.
  rewrite Z.sub_add_distr, Z2Nat.inj_sub; try omega.
  setoid_rewrite Hi; simpl; omega.
Qed.

Corollary upd_init_const : forall {A} i b (v v' : A), 0 <= i < b ->
  upd_Znth i (repeat v' (Z.to_nat i) ++ repeat v (Z.to_nat (b - i))) v' =
  repeat v' (Z.to_nat (i + 1)) ++ repeat v (Z.to_nat (b - (i + 1))).
Proof.
  intros.
  rewrite upd_init; try rewrite Zlength_repeat, Z2Nat.id; auto; try omega.
  rewrite Z2Nat.inj_add, repeat_plus, <- app_assoc; auto; omega.
Qed.

Lemma body_memset : semax_body Vprog Gprog f_memset memset_spec.
Proof.
  start_function.
  forward.
  rewrite data_at__isptr; Intros.
  rewrite sem_cast_neutral_ptr; auto.
  pose proof (sizeof_pos t).
  forward_for_simple_bound n (EX i : Z, PROP () LOCAL (temp _p p; temp _s p; temp _c (vint c); temp _n (vint n))
    SEP (data_at sh (tarray tuchar n) (repeat (vint c) (Z.to_nat i) ++ repeat Vundef (Z.to_nat (n - i))) p)).
  { entailer!.
    apply derives_trans with (Q := data_at_ sh (tarray tuchar (sizeof t)) p).
    - rewrite !data_at__memory_block; simpl.
      assert ((1 * Z.max 0 (sizeof t))%Z = sizeof t) as Hsize.
      { rewrite Z.mul_1_l, Z.max_r; auto; apply Z.ge_le; auto. }
      setoid_rewrite Hsize; Intros; apply andp_right; [|simpl; apply derives_refl].
      apply prop_right; match goal with H : field_compatible _ _ _ |- _ =>
        destruct H as (? & ? & ? & ? & ? & ? & ? & ?) end; repeat split; simpl; auto.
      + unfold legal_alignas_type, tarray, nested_pred, local_legal_alignas_type; simpl.
        rewrite andb_true_r, Z.leb_le; apply Z.ge_le; auto.
      + setoid_rewrite Hsize; auto.
      + unfold size_compatible in *; simpl.
        destruct p; try contradiction.
        setoid_rewrite Hsize; auto.
      + unfold align_compatible; simpl.
        unfold align_attr; simpl.
        destruct p; try contradiction.
        apply Z.divide_1_l.
    - rewrite data_at__eq.
      unfold default_val, reptype_gen; simpl.
      rewrite repeat_list_repeat, Z.sub_0_r; apply derives_refl. }
  - forward.
    repeat match goal with H : _ /\ _ |- _ => destruct H end; assert (c <= Int.max_unsigned).
    { etransitivity; eauto; unfold Int.max_unsigned; simpl; computable. }
    rewrite zero_ext_inrange; rewrite zero_ext_inrange; rewrite ?Int.unsigned_repr; try omega.
    rewrite upd_init_const; [|omega].
    entailer!.
  - forward.
    rewrite Zminus_diag, app_nil_r; apply derives_refl.
Qed.

Lemma lock_struct_array_sub : forall sh z i (v : val) p,
  field_at sh (tarray (tptr (Tstruct _lock_t noattr)) z) [ArraySubsc i] v p =
  field_at sh (tarray (tptr tlock) z) [ArraySubsc i] v p.
Proof.
  intros.
  unfold field_at, at_offset; rewrite !data_at_rec_eq; simpl; f_equal.
Qed.

Lemma body_atomic_exchange : semax_body Vprog Gprog f_simulate_atomic_exchange atomic_exchange_spec.
Proof.
 match goal with |- semax_body ?V ?G ?F ?spec =>
    let s := fresh "spec" in
    pose (s:=spec); hnf in s;
    match goal with
    | s :=  (DECLARE _ WITH u : unit
               PRE  [] main_pre _ nil u
               POST [ tint ] main_post _ nil u) |- _ => idtac
    | s := ?spec' |- _ => check_canonical_funspec spec'
   end;
   change (semax_body V G F s); subst s
 end.
 let DependedTypeList := fresh "DependedTypeList" in
 match goal with |- semax_body _ _ _ (pair _ (mk_funspec _ _ _ ?Pre _ _ _)) =>
   match Pre with 
   | (fun x => match x with (a,b) => _ end) => intros Espec DependedTypeList [a b] 
   | (fun i => _) => intros Espec DependedTypeList i
   end;
   simpl fn_body; simpl fn_params; simpl fn_return
 end.
 simpl functors.MixVariantFunctor._functor in *;
 simpl rmaps.dependent_type_functor_rec;
 repeat match goal with |- @semax _ _ _ (match ?p with (a,b) => _ end * _) _ _ =>
             destruct p as [a b]
           end;
 simplify_func_tycontext;
 repeat match goal with 
 | |- context [Sloop (Ssequence (Sifthenelse ?e Sskip Sbreak) ?s) Sskip] =>
       fold (Swhile e s)
 | |- context [Ssequence ?s1 (Sloop (Ssequence (Sifthenelse ?e Sskip Sbreak) ?s2) ?s3) ] =>
      match s3 with
      | Sset ?i _ => match s1 with Sset ?i' _ => unify i i' | Sskip => idtac end
      end;
      fold (Sfor s1 e s2 s3)
 end;
 try expand_main_pre;
 process_stackframe_of.
 repeat change_mapsto_gvar_to_data_at;  (* should really restrict this to only in main,
                                  but it needs to come after process_stackframe_of *)
 repeat rewrite <- data_at__offset_zero;
 try apply start_function_aux1;
 repeat (apply semax_extract_PROP; 
              match goal with
              | |- _ ?sh -> _ =>
                 match type of sh with
                 | share => intros ?SH 
                 | Share.t => intros ?SH 
                 | _ => intro
                 end
               | |- _ => intro
               end);
 first [ eapply eliminate_extra_return'; [ reflexivity | reflexivity | ]
        | eapply eliminate_extra_return; [ reflexivity | reflexivity | ]
        | idtac];
 abbreviate_semax.
  simpl; destruct ts as ((((((((((((ish, lsh), gsh1), gsh2), hsh), tgt), l), i), v), h), Rc), Rx), Rc').
(* start_function doesn't work for dependent specs? *)
  rewrite lock_inv_isptr; Intros.
  forward_call (l, lsh, AE_inv tgt i ish gsh2 Rx).
  unfold AE_inv at 2; Intros h' v'.
  gather_SEP 2 5; rewrite sepcon_comm.
  assert_PROP (list_incl h h').
  { go_lowerx; apply sepcon_derives_prop, ghost_inj. }
  rewrite ghost_share_join; auto.
  forward.
  forward.
  assert (apply_hist i (AE v' v :: h') = Some v) as Hh'.
  { simpl.
    match goal with H : apply_hist _ _ = _ |- _ => rewrite H end.
    destruct (eq_dec v' v'); auto; contradiction n; auto. }
  apply hist_add with (e := AE v' v).
  { rewrite Hh'; discriminate. }
  erewrite <- ghost_share_join with (sh1 := gsh1)(h1 := AE v' v :: h)(sh := hsh); eauto.
  forward_call (l, lsh, AE_inv tgt i ish gsh2 Rx).
  { rewrite ?sepcon_assoc; rewrite <- sepcon_emp at 1; rewrite sepcon_comm; apply sepcon_derives;
      [repeat apply andp_right; auto; eapply derives_trans; try apply positive_weak_positive; auto|].
    { apply AE_inv_precise; auto. }
    unfold AE_inv.
    Exists (AE v' v :: h') v; simpl; entailer!.
    rewrite !sepcon_assoc, <- (sepcon_assoc _ (Rc _ _)), (sepcon_comm _ (Rc _ _)).
    rewrite sepcon_comm, !sepcon_assoc, <- sepcon_assoc.
    eapply derives_trans; [apply sepcon_derives; [|apply derives_refl]|].
    { match goal with H : AE_spec _ _ _ _ |- _ => apply H end; auto. }
    cancel. }
  forward.
  Exists v'; entailer!.
  rewrite <- (sepcon_emp emp) at 3.
  apply sepcon_derives; apply andp_left2; auto.
Qed.

Lemma lock_struct_array : forall sh z (v : list val) p,
  data_at sh (tarray (tptr (Tstruct _lock_t noattr)) z) v p =
  data_at sh (tarray (tptr tlock) z) v p.
Proof.
  intros.
  unfold data_at, field_at, at_offset; rewrite !data_at_rec_eq; simpl; f_equal.
Qed.

(*Lemma body_initialize_channels : semax_body Vprog Gprog f_initialize_channels initialize_channels_spec.
Proof.
  start_function.
  rewrite <- seq_assoc.
  forward_for_simple_bound N (EX i : Z, PROP () LOCAL (gvar _comm comm; gvar _lock lock; gvar _bufs bufs)
    SEP (data_at_ Ews (tarray tint N) (offset_val (sizeof tint * i) comm);
         EX locks : list val, !!(Zlength locks = i) &&
          (data_at Ews (tarray (tptr tlock) N) (locks ++ repeat Vundef (Z.to_nat (N - i))) lock *
           fold_right sepcon emp (map (fun r => lock_inv Tsh (Znth r locks Vundef) (comm_inv comm r)) (upto (Z.to_nat i))) *
           fold_right sepcon emp (map (malloc_token Tsh (sizeof tlock)) locks));
         data_at_ Ews (tarray tbuffer B) bufs)).
  { unfold N; computable. }
  { unfold N; computable. }
  { Exists ([] : list val); repeat entailer!. }
  - Intros locks.
(*    forward.
    forward_call (sizeof tlock).
    { admit. }
    { simpl; computable. }
    Intro l.
    rewrite malloc_compat; auto; Intros.
    rewrite memory_block_data_at_; auto.
    rewrite <- lock_struct_array.
    forward.
    forward_call (l, Tsh, comm_inv comm i).
    forward_call (l, Tsh, comm_inv comm i).
    { lock_props.
      unfold comm_inv.*)
Admitted.*)

Lemma body_initialize_reader : semax_body Vprog Gprog f_initialize_reader initialize_reader_spec.
Proof.
  start_function.
  assert_PROP (0 <= r < N) as Hr.
  { go_lowerx; apply sepcon_derives_prop, field_at_array_inbounds. }
  forward.
  forward.
  forward.
Qed.

Lemma body_start_read : semax_body Vprog Gprog f_start_read start_read_spec.
Proof.
  start_function.
  assert_PROP (0 <= r < N) as Hr.
  { go_lowerx; apply sepcon_derives_prop, field_at_array_inbounds. }
  forward.
  rewrite lock_inv_isptr; Intros.
  rewrite <- lock_struct_array_sub.
  forward.
  (* Do the Rc's need all the arguments? *)
  forward_call (Tsh, sh2, gsh1, gsh2, sh2, c, l, -1, -1, h,
    fun (h : hist) (b : Z) => !!(b = -1) && EX v : Z, data_at sh tbuffer (vint v) (Znth b0 bufs Vundef),
    comm_R bufs sh, fun (h : hist) (b : Z) => !!(-1 <= b < B) &&
      EX v : Z, data_at sh tbuffer (vint v) (Znth (if eq_dec b (-1) then b0 else b) bufs Vundef)).
  { unfold comm_inv; entailer!.
    rewrite <- sepcon_emp at 1; rewrite sepcon_comm; apply sepcon_derives; [|cancel].
    apply andp_right; auto.
    eapply derives_trans; [|apply precise_weak_precise]; auto.
    apply derives_precise' with (Q := data_at_ sh tbuffer (Znth b0 bufs Vundef)); auto.
    clear; entailer!. }
  { repeat (split; auto); try computable.
    unfold AE_spec, comm_R; intros.
    Intros v1 v2; subst.
    destruct (eq_dec (-1) (-1)); [|contradiction n; auto].
    apply andp_right; [apply prop_right; omega|].
    unfold prev_read at 2; simpl.
    destruct (eq_dec vx (-1)).
    - Exists v1 v2; unfold prev_read at 1; cancel.
      apply andp_right; auto.
      eapply derives_trans; [|apply precise_weak_precise]; auto.
      destruct (prev_read (AE vx (-1) :: hx)).
      + apply derives_precise' with (Q := data_at_ sh tbuffer (Znth z bufs Vundef)); auto.
        clear; entailer!.
      + rewrite exp_trivial; auto.
        apply precise_andp2; auto.
    - destruct hx as [|[]]; simpl in *; [inv H0; contradiction n; auto|].
      destruct (apply_hist (-1) hx) eqn: Hh; [|discriminate].
      destruct (eq_dec z r0); [inv H0 | discriminate].
      destruct (eq_dec vx (-1)); [contradiction n; auto|].
      (* Here's where we need the relationship between last_read (i.e., b0) and the true history hx. *)
      Exists v2 v1; cancel.
      admit. }
  Intros b.
  assert (repable_signed b).
  { split; [transitivity (-1); [computable | omega]|].
    transitivity B; [omega | unfold B, N; computable]. }
  forward_if (PROP ()
   LOCAL (temp _t'2 (vint (if eq_dec b (-1) then 0 else 1)); temp _b (vint b); temp _r (vint r); gvar _reading reading; gvar _last_read last_read; 
   gvar _lock lock; gvar _comm comm)
   SEP (lock_inv sh2 l (AE_inv c (-1) Tsh gsh2 (comm_R bufs sh));
        ghost gsh1 (-1) (sh2, AE b (-1) :: h) c;
        EX v : Z,
          data_at sh tbuffer (vint v)
          (Znth (if eq_dec b (-1) then b0 else b) bufs Vundef);
        field_at_ Ews (tarray tint N) [ArraySubsc r] reading;
        field_at Ews (tarray tint N) [ArraySubsc r] (vint b0) last_read;
        field_at sh1 (tarray (tptr tint) N) [ArraySubsc r] c comm;
        field_at sh1 (tarray (tptr (Tstruct _lock_t noattr)) N) [ArraySubsc r] l lock)).
  { forward.
    destruct (eq_dec b (-1)); [omega|].
    entailer!.
    destruct (Int.lt (Int.repr b) (Int.repr (3 + 2))) eqn: Hlt; auto.
    apply lt_repr_false in Hlt; auto; unfold repable_signed; try computable.
    unfold B, N in *; omega. }
  { forward.
    destruct (eq_dec b (-1)); [|omega].
    entailer!. }
  forward_if (PROP () LOCAL (temp _b (vint (if eq_dec b (-1) then b0 else b)); temp _r (vint r);
      gvar _reading reading; gvar _last_read last_read; gvar _lock lock; gvar _comm comm)
    SEP (lock_inv sh2 l (AE_inv c (-1) Tsh gsh2 (comm_R bufs sh));
        ghost gsh1 (-1) (sh2, AE b (-1) :: h) c;
        EX v : Z,
          data_at sh tbuffer (vint v)
          (Znth (if eq_dec b (-1) then b0 else b) bufs Vundef);
        field_at_ Ews (tarray tint N) [ArraySubsc r] reading;
        field_at Ews (tarray tint N) [ArraySubsc r] (vint (if eq_dec b (-1) then b0 else b)) last_read;
        field_at sh1 (tarray (tptr tint) N) [ArraySubsc r] c comm;
        field_at sh1 (tarray (tptr (Tstruct _lock_t noattr)) N) [ArraySubsc r] l lock)).
  - forward.
    simpl eq_dec; destruct (eq_dec b (-1)); [contradiction H2; auto|].
    entailer!.
  - forward.
    simpl eq_dec; destruct (eq_dec b (-1)); [|discriminate].
    entailer!.
  - forward.
    forward.
    Exists (if eq_dec b (-1) then b0 else b) b v.
    repeat (apply andp_right; auto).
    unfold comm_inv; rewrite lock_struct_array_sub; cancel.
Admitted.

Lemma body_finish_read : semax_body Vprog Gprog f_finish_read finish_read_spec.
Proof.
  start_function.
  assert_PROP (0 <= r < N) as Hr.
  { go_lowerx; apply sepcon_derives_prop, field_at_array_inbounds. }
  forward.
  forward.
Qed.

Lemma body_initialize_writer : semax_body Vprog Gprog f_initialize_writer initialize_writer_spec.
Proof.
  start_function.
  forward.
  forward.
  forward_for_simple_bound N (EX i : Z, PROP ( )
   LOCAL (gvar _writing writing; gvar _last_given last_given; gvar _last_taken last_taken)
   SEP (field_at Ews tint [] (eval_unop Oneg tint (vint 1)) writing; field_at Ews tint [] (vint 0) last_given;
        data_at Ews (tarray tint N) (repeat (vint (-1)) (Z.to_nat i) ++ repeat Vundef (Z.to_nat (N - i))) last_taken)).
  { unfold N; computable. }
  { unfold N; computable. }
  { entailer!. }
  - forward.
    rewrite upd_init_const; auto.
    entailer!.
  - forward.
Qed.

Lemma list_Znth_eq : forall {A} d (l : list A), l = map (fun j => Znth j l d) (upto (length l)).
Proof.
  induction l; simpl; intros; auto.
  rewrite Znth_0_cons, IHl, map_map, map_length, upto_length.
  f_equal; apply map_ext_in; intros.
  rewrite Znth_pos_cons, <- IHl.
  unfold Z.succ; rewrite Z.add_simpl_r; auto.
  { rewrite In_upto in *; omega. }
Qed.

Lemma upd_Znth_eq : forall {A} {EqDec : EqDec A} (x d : A) (l : list A) i, 0 <= i < Zlength l ->
  upd_Znth i l x = map (fun j => if eq_dec j i then x else Znth j l d) (upto (length l)).
Proof.
  induction l; simpl; intros.
  { rewrite Zlength_nil in *; omega. }
  destruct (eq_dec 0 i).
  - subst; rewrite upd_Znth0, Zlength_cons, sublist_1_cons, sublist_same; auto; try omega.
    rewrite list_Znth_eq with (l0 := l)(d0 := d) at 1.
    rewrite map_map.
    f_equal; apply map_ext_in; intros.
    rewrite In_upto in *.
    destruct (eq_dec (Z.succ a0) 0); [omega|].
    rewrite Znth_pos_cons; [|omega].
    f_equal; omega.
  - rewrite Znth_0_cons, upd_Znth_cons; [|omega].
    rewrite Zlength_cons in *.
    rewrite IHl, map_map; [|omega].
    f_equal; apply map_ext_in; intros.
    rewrite In_upto in *.
    destruct (eq_dec a0 (i - 1)), (eq_dec (Z.succ a0) i); try omega; auto.
    rewrite Znth_pos_cons; [|omega].
    f_equal; omega.
Qed.

Lemma NoDup_filter : forall {A} (f : A -> bool) l, NoDup l -> NoDup (filter f l).
Proof.
  induction l; simpl; intros; auto.
  inv H.
  destruct (f a); auto.
  constructor; auto.
  rewrite filter_In; intros (? & ?); contradiction.
Qed.

Lemma list_in_count : forall {A} {A_eq : EqDec A} (l l' : list A), NoDup l' ->
  (length (filter (fun x => if in_dec eq_dec x l then true else false) l') <= length l)%nat.
Proof.
  intros.
  apply NoDup_incl_length; [apply NoDup_filter; auto|].
  intros ? Hin.
  rewrite filter_In in Hin; destruct Hin.
  destruct (in_dec eq_dec a l); [auto | discriminate].
Qed.

Lemma filter_length : forall {A} (f : A -> bool) l,
  length l = (length (filter f l) + length (filter (fun x => negb (f x)) l))%nat.
Proof.
  induction l; simpl; intros; auto.
  rewrite IHl.
  destruct (f a); simpl; omega.
Qed.

Lemma NoDup_upto : forall n, NoDup (upto n).
Proof.
  induction n; simpl; constructor.
  - rewrite in_map_iff.
    intros (? & ? & ?); rewrite In_upto in *; omega.
  - apply FinFun.Injective_map_NoDup; auto.
    intros ???; omega.
Qed.

Lemma list_pigeonhole : forall l n, Zlength l < n -> exists a, 0 <= a < n /\ ~In a l.
Proof.
  intros.
  pose proof (filter_length (fun x => if in_dec eq_dec x l then true else false) (upto (Z.to_nat n))) as Hlen.
  rewrite upto_length in Hlen.
  assert (length (filter (fun x => negb (if in_dec eq_dec x l then true else false)) (upto (Z.to_nat n))) > 0)%nat.
  { exploit (list_in_count l (upto (Z.to_nat n))).
    { apply NoDup_upto. }
    rewrite Zlength_correct in H.
    apply Z2Nat.inj_lt in H; try omega.
    rewrite Nat2Z.id in H; omega. }
  destruct (filter (fun x => negb (if in_dec eq_dec x l then true else false)) (upto (Z.to_nat n))) eqn: Hfilter;
    [simpl in *; omega|].
  assert (In z (filter (fun x => negb (if in_dec eq_dec x l then true else false)) (upto (Z.to_nat n)))) as Hin
    by (rewrite Hfilter; simpl; auto).
  rewrite filter_In, In_upto, Z2Nat.id in Hin; [|rewrite Zlength_correct in *; omega].
  destruct Hin; destruct (in_dec eq_dec z l); try discriminate; eauto.
Qed.

Opaque upto.

Lemma body_start_write : semax_body Vprog Gprog f_start_write start_write_spec.
Proof.
(*  start_function.
  rewrite <- seq_assoc.
  forward_for_simple_bound B (EX i : Z, PROP ( )
   LOCAL (lvar _available (tarray tint 5) lvar0; gvar _writing writing; gvar _last_given last_given;
   gvar _last_taken last_taken; gvar _reading reading)
   SEP (data_at Tsh (tarray tint 5) (repeat (vint 1) (Z.to_nat i) ++ repeat Vundef (Z.to_nat (B - i))) lvar0;
        data_at_ Ews tint writing; data_at Ews tint (vint b0) last_given;
        data_at Ews (tarray tint N) (map (fun x : Z => vint x) lasts) last_taken)).
  { unfold B, N; computable. }
  { entailer!. }
  { forward.
    rewrite upd_init_const; auto; entailer!. }
  rewrite Zminus_diag, app_nil_r.
  forward.
  forward.
  rewrite <- seq_assoc.
  assert_PROP (Zlength lasts = N).
  { gather_SEP 3.
    go_lowerx.
    apply sepcon_derives_prop.
    eapply derives_trans; [apply data_array_at_local_facts'; unfold N; omega|].
    apply prop_left; intros (? & ? & ?).
    unfold unfold_reptype in *; simpl in *.
    rewrite Zlength_map in *; apply prop_right; auto. }
  forward_for_simple_bound N (EX i : Z, PROP ( )
   LOCAL (temp _i (vint B); lvar _available (tarray tint 5) lvar0; 
   gvar _writing writing; gvar _last_given last_given; gvar _last_taken last_taken; gvar _reading reading)
   SEP (field_at Tsh (tarray tint 5) [] (map (fun x => vint (if eq_dec x b0 then 0
     else if in_dec eq_dec x (sublist 0 i lasts) then 0 else 1)) (upto (Z.to_nat B))) lvar0;
   data_at_ Ews tint writing; data_at Ews tint (vint b0) last_given;
   data_at Ews (tarray tint N) (map (fun x : Z => vint x) lasts) last_taken)).
  { unfold N; computable. }
  { unfold N; computable. }
  { entailer!.
    rewrite upd_Znth_eq with (d := Vundef); simpl; [|Omega0].
    unfold Znth; simpl.
    apply derives_refl'; f_equal.
    apply map_ext_in; intros ? Hin.
    rewrite In_upto in Hin.
    destruct (eq_dec a b0); auto.
    destruct (zlt a 0); [omega|].
    destruct Hin as (? & Hin); apply Z2Nat.inj_lt in Hin; auto; try omega.
    simpl in *; destruct (Z.to_nat a); auto.
    repeat (destruct n0; [solve [auto]|]).
    omega. }
  { assert (0 <= i < Zlength lasts) by omega.
    forward.
    { entailer!.
      apply Forall_Znth.
      { rewrite Zlength_map in *; omega. }
      rewrite Forall_forall; intros ? Hin.
      rewrite in_map_iff in Hin; destruct Hin as (? & ? & ?); subst; simpl; auto. }
    rewrite Znth_map with (d' := -1); auto.
    forward_if (PROP ( )
      LOCAL (temp _last (vint (Znth i lasts (-1))); temp _r (vint i); temp _i (vint B); lvar _available (tarray tint 5) lvar0; 
             gvar _writing writing; gvar _last_given last_given; gvar _last_taken last_taken; gvar _reading reading)
      SEP (field_at Tsh (tarray tint 5) [] (map (fun x => vint (if eq_dec x b0 then 0
             else if in_dec eq_dec x (sublist 0 (i + 1) lasts) then 0 else 1)) (upto (Z.to_nat B))) lvar0;
           data_at_ Ews tint writing; data_at Ews tint (vint b0) last_given;
           data_at Ews (tarray tint N) (map (fun x : Z => vint x) lasts) last_taken)).
    - assert (0 <= Znth i lasts (-1) < 5).
      { exploit (Forall_Znth(A := Z)); eauto.
        instantiate (1 := -1); intro.
        destruct (eq_dec (Znth i lasts (-1)) (-1)); [|unfold B, N in *; simpl in *; omega].
        match goal with H : Int.repr _ <> Int.neg _ |- _ => contradiction H; rewrite e; auto end. }
      forward.
      entailer!.
      rewrite upd_Znth_eq with (d := Vundef); auto.
      apply derives_refl'; erewrite map_ext_in; [reflexivity|].
      intros; rewrite In_upto, map_length, upto_length in *; simpl in *.
      rewrite Znth_map with (d' := 5), Znth_upto; simpl; auto; try omega.
      erewrite sublist_split with (mid := i)(hi := i + 1), sublist_len_1 with (d := -1); auto; try omega.
      destruct (in_dec eq_dec a (sublist 0 i lasts ++ [Znth i lasts (-1)])); rewrite in_app in *.
      + destruct (eq_dec a (Znth i lasts (-1))); destruct (eq_dec a b0); auto.
        destruct (in_dec eq_dec a (sublist 0 i lasts)); auto.
        destruct i0 as [? | [? | ?]]; subst; try contradiction.
        contradiction n; auto.
      + destruct (eq_dec a (Znth i lasts (-1))).
        { subst; contradiction n; simpl; auto. }
        destruct (eq_dec a b0); auto.
        destruct (in_dec eq_dec a (sublist 0 i lasts)); auto; contradiction n; auto.
    - forward.
      entailer!.
      apply derives_refl'; erewrite map_ext_in; [reflexivity|].
      intros; rewrite In_upto in *; simpl in *.
      destruct (eq_dec a b0); auto.
      erewrite sublist_split with (mid := i)(hi := i + 1), sublist_len_1 with (d := -1); auto; try omega.
      match goal with H : Int.repr _ = Int.neg _ |- _ => apply repr_inj_signed in H end.
      destruct (in_dec eq_dec a (sublist 0 i lasts ++ [Znth i lasts (-1)])); rewrite in_app in *.
      + destruct (in_dec eq_dec a (sublist 0 i lasts)); auto.
        destruct i0 as [? | [? | ?]]; subst; try contradiction.
        rewrite Int.unsigned_repr in *; try computable; omega.
      + destruct (in_dec eq_dec a (sublist 0 i lasts)); auto.
        contradiction n0; auto.
      + apply Forall_Znth; auto.
        eapply Forall_impl; [|eauto]; unfold repable_signed; intros.
        split; [transitivity (-1) | transitivity B]; unfold B, N in *; try computable; try omega.
      + unfold repable_signed; computable.
    - intros.
      unfold exit_tycon, overridePost.
      destruct (eq_dec ek EK_normal); [subst | apply drop_tc_environ].
      Intros; unfold POSTCONDITION, abbreviate, normal_ret_assert; entailer!. }
  rewrite sublist_same; auto.
  set (available := map (fun x => vint (if eq_dec x b0 then 0 else if in_dec eq_dec x lasts then 0 else 1))
         (upto (Z.to_nat B))).
  rewrite <- seq_assoc.
  unfold Sfor.
  forward.
  eapply semax_seq, semax_ff.
  eapply semax_pre with (P' := EX i : Z, PROP (0 <= i <= B; forall j, j < i -> Znth j available (vint 0) = vint 0)
    LOCAL (temp _i__1 (vint i); lvar _available (tarray tint 5) lvar0; gvar _writing writing;
           gvar _last_given last_given; gvar _last_taken last_taken; gvar _reading reading)
    SEP (field_at Tsh (tarray tint 5) [] available lvar0; data_at_ Ews tint writing;
         data_at Ews tint (vint b0) last_given; data_at Ews (tarray tint N) (map (fun x => vint x) lasts) last_taken)).
  { Exists 0; entailer!.
    intros; apply Znth_underflow; auto. }
  eapply semax_loop.
  + Intros i.
    assert (repable_signed i).
    { split; [transitivity 0 | transitivity B]; unfold B, N in *; try computable; try omega. }
    forward_if (PROP (i < B)
      LOCAL (temp _i__1 (vint i); lvar _available (tarray tint 5) lvar0; gvar _writing writing;
             gvar _last_given last_given; gvar _last_taken last_taken; gvar _reading reading)
      SEP (field_at Tsh (tarray tint 5) [] available lvar0; data_at_ Ews tint writing;
           data_at Ews tint (vint b0) last_given;
           data_at Ews (tarray tint N) (map (fun x : Z => vint x) lasts) last_taken)).
    { forward.
      entailer!. }
    { forward.
      exploit (list_pigeonhole (b0 :: lasts) B).
      { rewrite Zlength_cons; unfold B; omega. }
      intros (j & ? & Hout); exploit (H3 j); [unfold B, N in *; omega|].
      subst available.
      rewrite Znth_map with (d' := B); [|rewrite Zlength_upto; auto].
      rewrite Znth_upto; [|rewrite Z2Nat.id; omega].
      destruct (eq_dec j b0); [contradiction Hout; simpl; auto|].
      destruct (in_dec eq_dec j lasts); [contradiction Hout; simpl; auto|].
      discriminate. }
    Intros.
    forward.
    { entailer!.
      apply Forall_Znth; [rewrite Zlength_map, Zlength_upto; unfold B, N in *; simpl; omega|].
      rewrite Forall_forall; intros ? Hin.
      rewrite in_map_iff in Hin; destruct Hin as (? & ? & ?); subst; simpl; auto. }
    { unfold B, N in *; apply prop_right; omega. }
    forward_if (PROP (Znth i available (vint 0) = vint 0)
      LOCAL (temp _i__1 (vint i); lvar _available (tarray tint 5) lvar0; gvar _writing writing;
             gvar _last_given last_given; gvar _last_taken last_taken; gvar _reading reading)
      SEP (field_at Tsh (tarray tint 5) [] available lvar0; data_at_ Ews tint writing;
           data_at Ews tint (vint b0) last_given; data_at Ews (tarray tint N) (map (fun x : Z => vint x) lasts) last_taken)).
    { forward.
      forward.
      Exists lvar0 i; entailer!.
      unfold data_at_, field_at_; entailer!. }
    { forward.
      entailer!.
      subst available.
      rewrite Znth_map with (d' := 0) in *; try (rewrite Zlength_upto; unfold B, N in *; simpl in *; omega).
      unfold B, N; simpl; destruct (eq_dec _ _); auto.
      destruct (in_dec _ _ _); auto.
      unfold typed_false in *; simpl in *; discriminate. }
    intros.
    unfold exit_tycon, overridePost.
    destruct (eq_dec ek EK_normal); [subst | apply drop_tc_environ].
    Intros; unfold POSTCONDITION, abbreviate, normal_ret_assert, loop1_ret_assert.
    instantiate (1 := EX i : Z, PROP (0 <= i < B; Znth i available (vint 0) = vint 0;
      forall j : Z, j < i -> Znth j available (vint 0) = vint 0)
      LOCAL (temp _i__1 (vint i); lvar _available (tarray tint 5) lvar0; gvar _writing writing;
             gvar _last_given last_given; gvar _last_taken last_taken; gvar _reading reading)
      SEP (field_at Tsh (tarray tint 5) [] available lvar0; data_at_ Ews tint writing;
           data_at Ews tint (vint b0) last_given; data_at Ews (tarray tint N) (map (fun x : Z => vint x) lasts) last_taken)).
    Exists i; entailer!.
  - Intros i.
    forward.
    Exists (i + 1); entailer!.
    intros; destruct (eq_dec j i); subst; auto.
    assert (j < i) by omega; auto.
Qed.*)
Admitted.

Fixpoint extend {A} (l : list A) ls :=
  match l, ls with
  | x :: xs, y :: ys => (x :: y) :: extend xs ys
  | _, _ => ls
  end.

Lemma extract_nth_sepcon : forall l i, 0 <= i < Zlength l ->
  fold_right sepcon emp l = Znth i l FF * fold_right sepcon emp (remove_Znth i l).
Proof.
  intros.
  erewrite <- sublist_same with (al := l) at 1; auto.
  rewrite sublist_split with (mid := i); try omega.
  rewrite sublist_next with (i0 := i)(d := FF); try omega.
  rewrite sepcon_app; simpl.
  rewrite <- sepcon_assoc, (sepcon_comm _ (Znth i l FF)).
  unfold remove_Znth; rewrite sepcon_app, sepcon_assoc; auto.
Qed.

Lemma Zlength_extend : forall {A} (l : list A) ls, Zlength (extend l ls) = Zlength ls.
Proof.
  induction l; destruct ls; auto; simpl.
  rewrite !Zlength_cons, IHl; auto.
Qed.

Lemma Znth_extend_in : forall {A} (l : list A) ls i d d', 0 <= i < Zlength l -> Zlength l <= Zlength ls ->
  Znth i (extend l ls) d = Znth i l d' :: Znth i ls d.
Proof.
  induction l; destruct ls; simpl; intros; try rewrite Zlength_nil in *; try omega.
  rewrite !Zlength_cons in *.
  destruct (eq_dec i 0); subst; auto.
  rewrite !Znth_pos_cons; try omega.
  apply IHl; omega.
Qed.

Lemma Znth_extend_ge : forall {A} (l : list A) ls i d, Zlength l <= i ->
  Znth i (extend l ls) d = Znth i ls d.
Proof.
  induction l; destruct ls; auto; simpl; intros.
  destruct (zlt i 0); [rewrite !Znth_underflow; auto|].
  rewrite Zlength_cons in *.
  destruct (eq_dec i 0); [rewrite Zlength_correct in *; omega|].
  rewrite !Znth_pos_cons; try omega.
  apply IHl; omega.
Qed.

Lemma list_join_eq : forall (b : list share) a c c'
  (Hc : sepalg_list.list_join a b c) (Hc' : sepalg_list.list_join a b c'), c = c'.
Proof.
  induction b; intros; inv Hc; inv Hc'; auto.
  assert (w0 = w1) by (eapply sepalg.join_eq; eauto).
  subst; eapply IHb; eauto.
Qed.

Lemma make_shares_out : forall b lasts shs
  (Hb : ~In b lasts) (Hlen : Zlength lasts = Zlength shs), make_shares shs lasts b = shs.
Proof.
  induction lasts; auto; simpl; intros.
  { rewrite Zlength_nil in *; destruct shs; auto; rewrite Zlength_cons, Zlength_correct in *; omega. }
  destruct (eq_dec a b); [contradiction Hb; auto|].
  destruct shs; rewrite !Zlength_cons in *; [rewrite Zlength_nil, Zlength_correct in *; omega|].
  simpl; rewrite IHlasts; auto; omega.
Qed.

Lemma list_join_comm : forall (l1 l2 : list share) a b, sepalg_list.list_join a (l1 ++ l2) b ->
  sepalg_list.list_join a (l2 ++ l1) b.
Proof.
  induction l1; intros; [rewrite app_nil_r; auto|].
  inversion H as [|????? H1 H2]; subst.
  apply IHl1, sepalg_list.list_join_unapp in H2.
  destruct H2 as (c & Hl2 & Hl1).
  apply sepalg.join_comm in H1.
  destruct (sepalg_list.list_join_assoc1 H1 Hl2) as (? & ? & ?).
  eapply sepalg_list.list_join_app; eauto.
  econstructor; eauto.
Qed.

Lemma sublist_0_cons' : forall {A} i j (x : A) l, i <= 0 -> j > i -> sublist i j (x :: l) =
  x :: sublist i (j - 1) l.
Proof.
  intros; unfold sublist.
  replace (Z.to_nat i) with O; simpl.
  assert (0 < j - i) as Hgt by omega.
  rewrite Z2Nat.inj_lt in Hgt; try omega.
  destruct (Z.to_nat (j - i)) eqn: Hj; [omega|].
  simpl; f_equal; f_equal.
  replace (j - 1 - i) with (j - i - 1) by omega.
  rewrite Z2Nat.inj_sub; simpl; omega.
  destruct (eq_dec i 0); subst; auto.
  rewrite Z2Nat_neg; auto; omega.
Qed.

Lemma sublist_combine : forall {A B} (l1 : list A) (l2 : list B) i j,
  sublist i j (combine l1 l2) = combine (sublist i j l1) (sublist i j l2).
Proof.
  induction l1; simpl; intros.
  - unfold sublist; rewrite !skipn_nil, !firstn_nil; auto.
  - destruct l2.
    + unfold sublist at 1 3; rewrite !skipn_nil, !firstn_nil.
      destruct (sublist i j (a :: l1)); auto.
    + destruct (Z_le_dec j i); [rewrite !sublist_nil_gen; auto|].
      destruct (Z_le_dec i 0).
      * subst; rewrite !sublist_0_cons'; try omega.
        simpl; rewrite IHl1; auto.
      * rewrite !sublist_S_cons; try omega.
        apply IHl1; omega.
Qed.

Lemma extend_nil : forall {A} (l : list A), extend l [] = [].
Proof.
  destruct l; auto.
Qed.

Lemma extend_cons : forall {A} (l : list A) l1 ls, extend l (l1 :: ls) =
  match l with [] => l1 :: ls | a :: l' => (a :: l1) :: extend l' ls end.
Proof.
  destruct l; auto.
Qed.

Lemma sublist_extend : forall {A} (l : list A) ls i j,
  sublist i j (extend l ls) = extend (sublist i j l) (sublist i j ls).
Proof.
  induction l; simpl; intros.
  - unfold sublist; rewrite skipn_nil, firstn_nil; auto.
  - destruct ls.
    + unfold sublist; rewrite skipn_nil, firstn_nil, extend_nil; auto.
    + destruct (Z_le_dec j i); [rewrite !sublist_nil_gen; auto|].
      destruct (Z_le_dec i 0).
      * subst; rewrite !sublist_0_cons'; try omega.
        rewrite IHl; auto.
      * rewrite !sublist_S_cons; auto; omega.
Qed.

Lemma sublist_over : forall {A} (l : list A) i j, Zlength l <= i -> sublist i j l = [].
Proof.
  intros; unfold sublist.
  rewrite skipn_short, firstn_nil; auto.
  rewrite Zlength_correct in *; Omega0.
Qed.

Lemma body_finish_write : semax_body Vprog Gprog f_finish_write finish_write_spec.
Proof.
  start_function.
  forward.
  forward.
  assert_PROP (Zlength (map (fun i => vint i) lasts) = N) by entailer!.
  rewrite Zlength_map in *.
  rewrite <- seq_assoc.
  forward_for_simple_bound N (EX i : Z, PROP ( )
   LOCAL (temp _w (vint b); temp _last (vint b0); gvar _writing writing; gvar _last_given last_given;
          gvar _last_taken last_taken; gvar _comm comm; gvar _lock lock)
   SEP (data_at Ews tint (vint b) writing; data_at Ews tint (vint b0) last_given;
        data_at sh1 (tarray (tptr tint) N) comms comm; data_at sh1 (tarray (tptr tlock) N) locks lock;
        fold_right sepcon emp (map (fun r => lock_inv lsh (Znth r locks Vundef)
          (comm_inv (Znth r comms Vundef) bufs (Znth r shs Tsh) gsh2)) (upto (Z.to_nat N)));
        EX h' : list Z, !!(Zlength h' = i) && fold_right sepcon emp (map
          (fun x : val * hist => let '(c, h0) := x in ghost gsh1 (-1) (lsh, h0) c)
          (combine comms (extend (map (fun v => AE v b) h') h))) *
          let lasts' := map (fun i => if eq_dec (Znth i h' 0) (-1) then b0 else Znth i lasts 0)
                            (upto (Z.to_nat N)) in
            data_at Ews (tarray tint N) (map (fun i => vint i) lasts') last_taken *
            fold_right sepcon emp (map (fun a : Z => EX sh : share,
              !!(if eq_dec a b0 then sepalg_list.list_join sh0 (make_shares shs (sublist 0 i lasts') a) sh
                 else if eq_dec a b then sepalg_list.list_join sh0 (sublist i N shs) sh
                 else sepalg_list.list_join sh0 (make_shares shs lasts' a) sh) &&
              EX v : Z, @data_at CompSpecs sh tbuffer (vint v) (Znth a bufs Vundef)) (upto (Z.to_nat B))))).
  { unfold N; computable. }
  { unfold N; computable. }
  { Exists (@nil Z).
    replace (map (fun i => if eq_dec (Znth i [] 0) (-1) then b0 else Znth i lasts 0) (upto (Z.to_nat N)))
      with lasts.
    entailer!.
    apply derives_refl'; f_equal.
    apply map_ext; intro.
    f_equal; extensionality; f_equal; f_equal.
    apply prop_ext.
    destruct (eq_dec a b0); [|destruct (eq_dec a b); [|reflexivity]].
    - split; intro Hx; [subst; constructor | inv Hx; auto].
    - subst; rewrite sublist_same, make_shares_out; auto; try reflexivity.
      replace (Zlength lasts) with N; auto.
    - rewrite (list_Znth_eq 0 lasts) at 1.
      replace (length lasts) with (Z.to_nat N).
      apply map_ext.
      intro; rewrite Znth_nil; destruct (eq_dec 0 (-1)); auto; discriminate.
      { rewrite Zlength_correct in *; Omega0. } }
  - assert_PROP (Zlength comms = N) as Hcomms by entailer!.
    forward.
    { entailer!.
      apply Forall_Znth.
      { rewrite Hcomms; auto. }
      apply Forall_impl with (P := isptr); auto. }
    rewrite <- lock_struct_array.
    rewrite (extract_nth_sepcon (map _ (upto (Z.to_nat N))) i);
      [|rewrite Zlength_map; auto].
    rewrite Znth_map with (d' := N); [|rewrite Zlength_upto; auto].
    rewrite Znth_upto; [|rewrite Z2Nat.id; auto; omega].
    rewrite lock_inv_isptr; Intros.
    forward.
    Intros h'.
    assert (Zlength comms = Zlength (extend (map (fun v0 : Z => AE v0 b) h') h)).
    { rewrite Zlength_extend; omega. }
    assert (Zlength (combine comms (extend (map (fun v => AE v b) h') h)) = N) as Hlens.
    { rewrite Zlength_combine, Z.min_l; auto; omega. }
    rewrite <- Hlens in *.
    rewrite (extract_nth_sepcon (map _ (combine comms _)) i); [|rewrite Zlength_map; auto].
    rewrite Znth_map with (d' := (Vundef, [])), Znth_combine; auto.
    rewrite Znth_extend_ge; [|rewrite Zlength_map; omega].
    rewrite (extract_nth_sepcon (map _ (upto (Z.to_nat B))) b); [|rewrite Zlength_map, Zlength_upto; auto].
    rewrite Znth_map with (d' := B), Znth_upto; rewrite ?Zlength_upto, ?Z2Nat.id; auto; try omega.
    Intros bsh.
    destruct (eq_dec b b0); [absurd (b = b0); auto|].
    destruct (eq_dec b b); [|contradiction n0; auto].
    rewrite Hlens in *.
    match goal with H : sepalg_list.list_join _ (sublist i N shs) _ |- _ =>
      rewrite sublist_split with (mid := i + 1) in H; try omega;
      apply list_join_comm, sepalg_list.list_join_unapp in H; destruct H as (bsh' & ? & Hsh) end.
    rewrite sublist_len_1 with (d := Tsh), <- sepalg_list.list_join_1 in Hsh; [|omega].
    Intro v0.
    forward_call (Tsh, lsh, gsh1, gsh2, lsh, Znth i comms Vundef, Znth i locks Vundef, -1, b, Znth i h [],
      fun (h : hist) (b : Z) => !!(0 <= b < B) && EX v : Z, data_at (Znth i shs Tsh) tbuffer (vint v) (Znth b bufs Vundef),
      comm_R bufs (Znth i shs Tsh), fun (h : hist) (b : Z) => !!(-1 <= b < B) &&
        EX v : Z, data_at (Znth i shs Tsh) tbuffer (vint v) (Znth (if eq_dec b (-1) then Znth i lasts 0 else b) bufs Vundef)).
    { Exists v0; unfold comm_inv.
      rewrite <- (data_at_share_join _ _ _ _ _ _ Hsh).
      (* entailer! is slow *)
      rewrite true_eq, TT_andp; auto; cancel.
      rewrite <- sepcon_emp at 1; rewrite sepcon_comm; apply sepcon_derives; [|cancel].
      apply andp_right; auto.
      eapply derives_trans; [|apply precise_weak_precise]; auto.
      apply derives_precise' with (Q := data_at_ (Znth i shs Tsh) tbuffer (Znth b bufs Vundef)); auto.
      clear; entailer!. }
    { repeat (split; auto).
      { transitivity 0; try computable; omega. }
      { transitivity B; unfold B, N in *; try computable; omega. }
      unfold AE_spec, comm_R; intros.
      Intros v1 v2.
      destruct (eq_dec vc (-1)); [omega|].
      apply andp_right; [apply prop_right; repeat split; auto; omega|].
      Exists v2 v1.
      destruct (eq_dec vx (-1)).
      + assert (prev_read hx = Some (Znth i lasts 0)) as Hprev by admit.
        rewrite Hprev; cancel.
        apply andp_right; auto.
        eapply derives_trans; [|apply precise_weak_precise]; auto.
        apply derives_precise' with (Q := data_at_ (Znth i shs Tsh) tbuffer (Znth vc bufs Vundef)); auto.
        clear; entailer!.
      + cancel.
        apply andp_right; auto.
        eapply derives_trans; [|apply precise_weak_precise]; auto.
        apply derives_precise' with (Q := data_at_ (Znth i shs Tsh) tbuffer (Znth vc bufs Vundef)); auto.
        clear; entailer!. }
    Intros v'.
    gather_SEP 0 7; replace_SEP 0 (fold_right sepcon emp (map (fun r : Z =>
      lock_inv lsh (Znth r locks Vundef) (AE_inv (Znth r comms Vundef) (-1) Tsh gsh2 (comm_R bufs (Znth r shs Tsh))))
           (upto (Z.to_nat N)))).
    { go_lowerx.
      rewrite (extract_nth_sepcon (map _ (upto _)) i); [|rewrite Zlength_map, Zlength_upto; unfold N in *; auto].
      cancel.
      rewrite Znth_map with (d' := N), Znth_upto; rewrite ?Zlength_upto; unfold N in *; simpl; auto; omega. }
    gather_SEP 1 7; replace_SEP 0 (fold_right sepcon emp (map (fun x => let '(c, h0) := x in
      ghost gsh1 (-1) (lsh, h0) c) (combine comms (extend (map (fun v1 : Z => AE v1 b) (h' ++ [v'])) h)))).
    { go_lowerx.
      rewrite (extract_nth_sepcon (map _ (combine _ _)) i);
        [|rewrite Zlength_map, Zlength_combine, Zlength_extend, Z.min_l; omega].
      assert (Zlength comms = Zlength (extend (map (fun v0 : Z => AE v0 b) (h' ++ [v'])) h)).
      { rewrite Zlength_extend; omega. }
      assert (Zlength (combine comms (extend (map (fun v => AE v b) (h' ++ [v'])) h)) = N) as Hlens'.
      { rewrite Zlength_combine, Z.min_l; auto; omega. }
      rewrite <- Hlens' in *.
      rewrite Znth_map with (d' := (Vundef, [])), Znth_combine; auto.
      erewrite Znth_extend_in; rewrite ?Zlength_map, ?Zlength_app, ?Zlength_cons, ?Zlength_nil; try omega.
      rewrite Znth_map'.
      instantiate (1 := 0).
      subst; rewrite app_Znth2, Zminus_diag, Znth_0_cons; [|omega].
      cancel.
      apply derives_refl'; f_equal.
      unfold remove_Znth; f_equal; rewrite !sublist_map, !sublist_combine, !sublist_extend.
      + rewrite map_app, sublist_app1; rewrite ?Zlength_map; auto; omega.
      + rewrite !Zlength_map, !Hlens, !Hlens'.
        rewrite !sublist_over with (l := map _ _); auto;
          rewrite Zlength_map, ?Zlength_app, ?Zlength_cons, ?Zlength_nil; omega. }
    assert (repable_signed v').
    { split; [transitivity (-1) | transitivity B]; unfold B, N in *; try computable; omega. }
    match goal with |- semax _ (PROP () (LOCALx ?Q (SEPx (?p0 :: ?p1 :: ?p2 :: ?p3 :: ?p4 :: ?p5 :: ?p6 ::
      data_at _ _ ?l last_taken :: ?R2)))) _ _ =>
      forward_if (PROP () (LOCALx Q (SEPx (p0 :: p1 :: p2 :: p3 :: p4 :: p5 :: p6 ::
        data_at Ews (tarray tint N) (upd_Znth i l (vint (if eq_dec v' (-1) then b0 else Znth i lasts 0))) last_taken :: R2)))) end.
    + forward.
      match goal with H : Int.repr v' = _ |- _ => rewrite Int.neg_repr in H; apply repr_inj_signed in H end; subst;
        auto; [|split; try computable].
      destruct (eq_dec (- (1)) (-1)); [|contradiction n0; auto].
      apply drop_tc_environ.
    + forward.
      destruct (eq_dec v' (-1)); [subst; absurd (Int.repr (-1) = Int.neg (Int.repr 1)); auto|].
      erewrite upd_Znth_triv.
      apply drop_tc_environ.
      * rewrite !Zlength_map, Zlength_upto; auto.
      * rewrite !Znth_map', Znth_upto; [|rewrite Z2Nat.id; omega].
        rewrite Znth_overflow; [|omega].
        destruct (eq_dec 0 (-1)); [clear - e0; omega | auto].
    + intros.
      unfold exit_tycon, overridePost.
      destruct (eq_dec ek EK_normal); [subst | apply drop_tc_environ].
      Intros; unfold POSTCONDITION, abbreviate, normal_ret_assert.
      do 2 (apply andp_right; [apply prop_right; auto|]).
      Exists (h' ++ [v']).
      go_lower.
      repeat (apply andp_right; [apply prop_right; repeat split; auto; omega|]).
      rewrite lock_struct_array; unfold comm_inv; cancel.
      rewrite !sepcon_andp_prop'.
      rewrite Zlength_app, Zlength_cons, Zlength_nil; apply andp_right;
        [apply prop_right; auto|].
      cancel.
      rewrite (sepcon_comm (exp _)), !sepcon_assoc; apply sepcon_derives.
      * apply derives_refl'; f_equal.
        erewrite upd_Znth_eq, !map_length, upto_length, !map_map;
          [|rewrite !Zlength_map, Zlength_upto; unfold N in *; auto].
        apply map_ext_in; intros; rewrite In_upto in *.
        destruct (eq_dec a (Zlength h')).
        -- subst; rewrite app_Znth2, Zminus_diag, Znth_0_cons; auto; clear; omega.
        -- rewrite Znth_map', Znth_upto; [|omega].
           destruct (zlt a (Zlength h')); [rewrite app_Znth1 | rewrite Znth_overflow]; auto.
           rewrite Znth_overflow with (al := _ ++ _); auto.
           rewrite Zlength_app, Zlength_cons, Zlength_nil; omega.
      * admit.
  - forward.
    forward.
    forward.
    rewrite sublist_nil, sublist_same; rewrite ?Zlength_map; auto.
    Exists (map (fun i => if eq_dec (Znth i h' 0) (-1) then b0 else Znth i lasts 0) (upto (Z.to_nat N)))
      (extend (map (fun v => AE v b) h') h); entailer!.
    + split.
      * rewrite Forall_map, Forall_forall; intros; simpl.
        destruct (eq_dec (Znth x h' 0) (-1)); [omega|].
        rewrite In_upto, Z2Nat.id in *; unfold N; try omega.
        apply Forall_Znth; [omega | auto].
      * assert (Zlength h' = Zlength h) as Hlen by omega; clear - Hlen; revert dependent h; induction h';
          destruct h; rewrite ?Zlength_nil, ?Zlength_cons in *; simpl; intros; auto; try omega.
        { rewrite Zlength_correct in *; omega. }
        constructor; eauto.
        apply IHh'; omega.
    + apply derives_refl'; f_equal.
      apply map_ext; intro.
      f_equal; extensionality; f_equal; f_equal; apply prop_ext.
      destruct (eq_dec a b).
      * destruct (eq_dec a b0); [absurd (b = b0); subst; auto|].
        split; intro Hx; [inv Hx; auto | subst; constructor].
      * destruct (eq_dec a b0); reflexivity.
Admitted.
