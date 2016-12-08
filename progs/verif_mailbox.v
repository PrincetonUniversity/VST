Require Import veric.rmaps.
Require Import progs.conclib.
Require Import floyd.library.
Require Import floyd.sublist.
Require Import progs.mailbox.

Set Bullet Behavior "Strict Subproofs".

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

(* This is an overapproximation of IRIS's concept of view shift. *)
Definition view_shift A B := forall {CS : compspecs} {Espec : OracleKind} D P Q R C P',
  semax D (PROPx P (LOCALx Q (SEPx (B :: R)))) C P' ->
  semax D (PROPx P (LOCALx Q (SEPx (A :: R)))) C P'.

(* ghost histories *)
Parameter ghost :
  forall (sh : share) (i : Z) (f : share * hist) (p : val), mpred.

Axiom new_ghost : forall t i v p,
  view_shift (data_at Tsh t v p) (ghost Tsh i (Tsh, []) p * data_at Tsh t v p).

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
Axiom hist_add : forall i h e p, apply_hist i (e :: h) <> None ->
  view_shift (ghost Tsh i (Tsh, h) p) (ghost Tsh i (Tsh, e :: h) p).
Axiom ghost_inj : forall sh1 sh2 i sh h1 h2 p, ghost sh1 i (sh, h1) p * ghost sh2 i (Tsh, h2) p
  |-- !!(list_incl h1 h2).
Axiom ghost_inj_Tsh : forall sh1 sh2 i h1 h2 p, ghost sh1 i (Tsh, h1) p * ghost sh2 i (Tsh, h2) p
  |-- !!(h1 = h2).
(* Should this be an axiom? *)
Axiom ghost_feasible : forall sh i h p, ghost sh i (Tsh, h) p |-- !!(apply_hist i h <> None).
Axiom ghost_conflict : forall sh1 sh2 i v1 v2 p,
  ghost sh1 i v1 p * ghost sh2 i v2 p |-- !!sepalg.joins sh1 sh2.

(* ghost variables *)
Parameter ghost_var : forall (sh : share) (t : type) (v : reptype t) (p : val), mpred.

Axiom ghost_var_share_join : forall sh1 sh2 sh t v p, sepalg.join sh1 sh2 sh ->
  ghost_var sh1 t v p * ghost_var sh2 t v p = ghost_var sh t v p.
Axiom change_ghost_var : forall t v p v',
  view_shift (ghost_var Tsh t v p) (ghost_var Tsh t v' p).
Axiom ghost_var_inj : forall sh1 sh2 t v1 v2 p, ghost_var sh1 t v1 p * ghost_var sh2 t v2 p
  |-- !!(v1 = v2).
Axiom ghost_var_conflict : forall sh1 sh2 t1 t2 v1 v2 p,
  ghost_var sh1 t1 v1 p * ghost_var sh2 t2 v2 p |-- !!sepalg.joins sh1 sh2.
Axiom ghost_var_precise : forall sh t p, precise (EX v : reptype t, ghost_var sh t v p).

Definition AE_inv x i sh gsh R := EX h : hist, EX v : Z,
  !!(apply_hist i h = Some v /\ repable_signed v) &&
  (data_at sh tint (vint v) x * ghost gsh i (Tsh, h) x * R h v * (weak_precise_mpred (R h v) && emp)).

Axiom ghost_inj' : forall sh i p h1 h2 r1 r2 r
  (Hp1 : predicates_hered.app_pred (ghost sh i (Tsh, h1) p) r1)
  (Hp1 : predicates_hered.app_pred (ghost sh i (Tsh, h2) p) r2)
  (Hr1 : sepalg.join_sub r1 r) (Hr2 : sepalg.join_sub r2 r),
  r1 = r2 /\ h1 = h2.

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
  view_shift (Rx hx vx * Rc hc vc)
  (Rx (AE vx vc :: hx) vc * (weak_precise_mpred (Rx (AE vx vc :: hx) vc) && emp) * Rc' (AE vx vc :: hc) vx).

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
    (* This is probably provable for derives, but might need to be assumed for view shift. *)
    admit.
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

Fixpoint find_read h :=
  match h with
  | [] => None
  | AE r w :: rest => if eq_dec w (-1) then if eq_dec r (-1) then find_read rest
                      else Some (r, rest) else find_read rest
  end.

Lemma find_read0 : forall h, find_read (h ++ [AE 0 (-1)]) =
  match find_read h with Some (v, rest) => Some (v, rest ++ [AE 0 (-1)]) | None => Some (0, []) end.
Proof.
  induction h; simpl; eauto.
  destruct a.
  destruct (eq_dec w (-1)); auto.
  destruct (eq_dec r (-1)); eauto.
Qed.

Definition last_two_reads h := match find_read (h ++ [AE 0 (-1)]) with
  | Some (b1, rest) => match find_read rest with Some (b2, _) => (b1, b2) | None => (b1, -1) end
  | None => (-1, -1) (*impossible*) end.

Fixpoint find_write h :=
  match h with
  | [] => None
  | AE r w :: rest => if eq_dec w (-1) then find_write rest else Some (w, rest)
  end.

Definition prev_taken h := match find_write h with Some (_, rest) =>
  match find_read rest with Some (b, _) => b | None => 0 end | None => -1 end.

Definition last_write h := match find_write h with Some (w, _) => w | None => 0 end.

(* The ghost variables are the last value read, the last value written, and the last value read before
   the last write (i.e., last_taken). The first is updated by the reader, the rest by the writer. *)

(* We can't use tokens because we need to consistently get the same share for each reader
   (so that the communication invariant is precise). *)
Definition comm_R bufs sh gsh p h b :=
  !!(-1 <= b < B /\ Forall (fun a => match a with AE r w => -1 <= r < B /\ -1 <= w < B end) h) &&
  let '(b1, b2) := last_two_reads h in
  ghost_var gsh tint (vint b1) p * ghost_var gsh tint (vint (last_write h)) (offset_val 1 p) *
  ghost_var gsh tint (vint (prev_taken h)) (offset_val 2 p) *
  if eq_dec b (-1) then
    if eq_dec b2 (-1) then emp else EX v : Z, data_at sh tbuffer (vint v) (Znth b2 bufs Vundef)
  else EX v : Z, data_at sh tbuffer (vint v) (Znth b bufs Vundef).

Definition comm_inv comm bufs sh gsh := AE_inv comm (-1) Tsh gsh (comm_R bufs sh gsh comm).

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
        data_at Tsh tbuffer (vint 0) (Znth 0 bufs Vundef);
        fold_right sepcon emp (map (data_at_ Tsh tbuffer) (sublist 1 (Zlength bufs) bufs))).
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
   PROP (0 <= b0 < B; readable_share sh; readable_share sh1; readable_share sh2; sepalg.join gsh1 gsh2 Tsh;
         isptr c; fst (last_two_reads h) = b0)
   LOCAL (temp _r (vint r); gvar _reading reading; gvar _last_read last_read; gvar _lock lock; gvar _comm comm)
   SEP (field_at_ Ews (tarray tint N) [ArraySubsc r] reading;
        field_at Ews (tarray tint N) [ArraySubsc r] (vint b0) last_read;
        field_at sh1 (tarray (tptr tint) N) [ArraySubsc r] c comm;
        field_at sh1 (tarray (tptr tlock) N) [ArraySubsc r] l lock;
        lock_inv sh2 l (comm_inv c bufs sh gsh2);
        EX v : Z, data_at sh tbuffer (vint v) (Znth b0 bufs Vundef);
        ghost gsh1 (-1) (sh2, h) c;
        ghost_var gsh1 tint (vint (fst (last_two_reads h))) c)
  POST [ tvoid ]
   EX b : Z, EX v0 : Z, EX v : Z,
   PROP (0 <= b < B; fst (last_two_reads (AE v0 (-1) :: h)) = b)
   LOCAL ()
   SEP (field_at Ews (tarray tint N) [ArraySubsc r] (vint b) reading;
        field_at Ews (tarray tint N) [ArraySubsc r] (vint b) last_read;
        field_at sh1 (tarray (tptr tint) N) [ArraySubsc r] c comm;
        field_at sh1 (tarray (tptr tlock) N) [ArraySubsc r] l lock;
        lock_inv sh2 l (comm_inv c bufs sh gsh2);
        data_at sh tbuffer (vint v) (Znth b bufs Vundef);
        ghost gsh1 (-1) (sh2, AE v0 (-1) :: h) c;
        ghost_var gsh1 tint (vint (fst (last_two_reads (AE v0 (-1) :: h)))) c).
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
   LOCAL (gvar _writing writing; gvar _last_given last_given; gvar _last_taken last_taken)
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
         readable_share sh1; readable_share lsh; readable_share sh0; Forall readable_share shs;
         sepalg_list.list_join sh0 shs Tsh; sepalg.join gsh1 gsh2 Tsh;
         Forall isptr comms; b <> b0; ~In b lasts; ~In b0 lasts)
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
        fold_right sepcon emp (map (fun r => ghost_var gsh1 tint (vint b0) (offset_val 1 (Znth r comms Vundef)) *
          ghost_var gsh1 tint (vint (Znth r lasts (-1)))
            (offset_val 2 (Znth r comms Vundef))) (upto (Z.to_nat N)));
        fold_right sepcon emp (map (fun i => EX sh : share,
          !!(if eq_dec i b0 then sh = sh0 else sepalg_list.list_join sh0 (make_shares shs lasts i) sh) &&
          EX v : Z, data_at sh tbuffer (vint v) (Znth i bufs Vundef)) (upto (Z.to_nat B))))
  POST [ tvoid ]
   EX lasts' : list Z, EX h' : list hist,
   PROP (Forall (fun x => -1 <= x < B) lasts'; Forall2 (fun h1 h2 => exists v, h2 = AE v b :: h1) h h';
         ~In b lasts')
   LOCAL ()
   SEP (data_at Ews tint (vint (-1)) writing; data_at Ews tint (vint b) last_given;
        data_at Ews (tarray tint N) (map (fun x => vint x) lasts') last_taken;
        data_at sh1 (tarray (tptr tint) N) comms comm;
        data_at sh1 (tarray (tptr tlock) N) locks lock;
        fold_right sepcon emp (map (fun r =>
          lock_inv lsh (Znth r locks Vundef) (comm_inv (Znth r comms Vundef) bufs (Znth r shs Tsh) gsh2))
          (upto (Z.to_nat N)));
        fold_right sepcon emp (map (fun x => let '(c, h) := x in ghost gsh1 (-1) (lsh, h) c) (combine comms h'));
        fold_right sepcon emp (map (fun r => ghost_var gsh1 tint (vint b) (offset_val 1 (Znth r comms Vundef)) *
          ghost_var gsh1 tint (vint (Znth r lasts' (-1)))
            (offset_val 2 (Znth r comms Vundef))) (upto (Z.to_nat N)));
        fold_right sepcon emp (map (fun i => EX sh : share,
          !!(if eq_dec i b then sh = sh0 else sepalg_list.list_join sh0 (make_shares shs lasts' i) sh) &&
          EX v : Z, data_at sh tbuffer (vint v) (Znth i bufs Vundef)) (upto (Z.to_nat B)))).

Definition reader_spec :=
 DECLARE _reader
  WITH arg : val, x : Z * val * val * val * val * val * val * val * list val * share * share * share * share * share
  PRE [ _arg OF tptr tvoid ]
   let '(r, reading, last_read, lock, comm, buf, c, l, bufs, sh1, sh2, sh, gsh1, gsh2) := x in
   PROP (readable_share sh; readable_share sh1; readable_share sh2; sepalg.join gsh1 gsh2 Tsh; isptr c)
   LOCAL (gvar _reading reading; gvar _last_read last_read; gvar _lock lock; gvar _comm comm; gvar _bufs buf)
   SEP (data_at Tsh tint (vint r) arg;
        field_at_ Ews (tarray tint N) [ArraySubsc r] reading;
        field_at_ Ews (tarray tint N) [ArraySubsc r] last_read;
        field_at sh1 (tarray (tptr tint) N) [ArraySubsc r] c comm;
        field_at sh1 (tarray (tptr tlock) N) [ArraySubsc r] l lock;
        data_at sh1 (tarray (tptr tbuffer) N) bufs buf;
        lock_inv sh2 l (comm_inv c bufs sh gsh2);
        EX v : Z, data_at sh tbuffer (vint v) (Znth 0 bufs Vundef);
        ghost gsh1 (-1) (sh2, []) c; ghost_var gsh1 tint (vint 0) c)
  POST [ tptr tvoid ] PROP () LOCAL () SEP (emp).

Definition writer_spec :=
 DECLARE _writer
  WITH arg : val, x : Z * val * val * val * val * val * val * list val * list val * list val *
                      share * share * share * list share * share * share
  PRE [ _arg OF tptr tvoid ]
   let '(r, writing, last_given, last_taken, lock, comm, buf, locks, comms, bufs, sh1, lsh, sh0, shs, gsh1, gsh2) := x in
   PROP (Zlength shs = N; readable_share sh1; readable_share lsh; readable_share sh0; Forall readable_share shs;
         sepalg_list.list_join sh0 shs Tsh; sepalg.join gsh1 gsh2 Tsh; Forall isptr comms)
   LOCAL (gvar _writing writing; gvar _last_given last_given; gvar _last_taken last_taken;
          gvar _lock lock; gvar _comm comm; gvar _bufs buf)
   SEP (data_at_ Ews tint writing; data_at_ Ews tint last_given; data_at_ Ews (tarray tint N) last_taken;
        data_at sh1 (tarray (tptr tint) N) comms comm;
        data_at sh1 (tarray (tptr tlock) N) locks lock;
        data_at sh1 (tarray (tptr tbuffer) N) bufs buf;
        fold_right sepcon emp (map (fun r =>
          lock_inv lsh (Znth r locks Vundef) (comm_inv (Znth r comms Vundef) bufs (Znth r shs Tsh) gsh2))
          (upto (Z.to_nat N)));
        fold_right sepcon emp (map (fun c => ghost gsh1 (-1) (lsh, []) c) comms);
        fold_right sepcon emp (map (fun r => ghost_var gsh1 tint (vint 0) (offset_val 1 (Znth r comms Vundef)) *
          ghost_var gsh1 tint (vint (-1)) (offset_val 2 (Znth r comms Vundef))) (upto (Z.to_nat N)));
        fold_right sepcon emp (map (fun i => EX sh : share, !!(if eq_dec i 0 then sh = sh0 else sh = Tsh) &&
          EX v : Z, data_at sh tbuffer (vint v) (Znth i bufs Vundef)) (upto (Z.to_nat B))))
  POST [ tptr tvoid ] PROP () LOCAL () SEP (emp).

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog [] u
  POST [ tint ] main_post prog [] u.

Definition Gprog : funspecs := ltac:(with_library prog [acquire_spec; release_spec; makelock_spec;
  surely_malloc_spec; memset_spec; atomic_exchange_spec; initialize_channels_spec; initialize_reader_spec;
  start_read_spec; finish_read_spec; initialize_writer_spec; start_write_spec; finish_write_spec;
  reader_spec; writer_spec; main_spec]).

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
    entailer!.
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
    apply eq_dec_refl. }
  apply hist_add with (e := AE v' v).
  { rewrite Hh'; discriminate. }
  erewrite <- ghost_share_join with (sh1 := gsh1)(h1 := AE v' v :: h)(sh := hsh); eauto.
  gather_SEP 3 5.
  match goal with H : AE_spec _ _ _ _ |- _ => apply H; auto end.
  forward_call (l, lsh, AE_inv tgt i ish gsh2 Rx).
  { rewrite ?sepcon_assoc; rewrite <- sepcon_emp at 1; rewrite sepcon_comm; apply sepcon_derives;
      [repeat apply andp_right; auto; eapply derives_trans; try apply positive_weak_positive; auto|].
    { apply AE_inv_precise; auto. }
    unfold AE_inv.
    Exists (AE v' v :: h') v; entailer!. }
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

Lemma body_initialize_channels : semax_body Vprog Gprog f_initialize_channels initialize_channels_spec.
Proof.
  start_function.
  rewrite <- seq_assoc.
  forward_for_simple_bound B (EX i : Z, PROP () LOCAL (gvar _comm comm; gvar _lock lock; gvar _bufs buf)
    SEP (data_at_ Ews (tarray (tptr tint) N) comm; data_at_ Ews (tarray (tptr tlock) N) lock;
         EX bufs : list val, !!(Zlength bufs = i /\ Forall isptr bufs) &&
           data_at Ews (tarray (tptr tbuffer) B) (bufs ++ repeat Vundef (Z.to_nat (B - i))) buf *
           fold_right sepcon emp (map (data_at_ Tsh tbuffer) bufs) *
           fold_right sepcon emp (map (malloc_token Tsh (sizeof tbuffer)) bufs))).
  { unfold B, N; computable. }
  { unfold B, N; computable. }
  { entailer!.
    Exists ([] : list val); simpl; entailer!. }
  { forward_call (sizeof tbuffer).
    { simpl; computable. }
    Intros b bufs.
    rewrite malloc_compat; auto; Intros.
    rewrite memory_block_data_at_; auto.
    forward.
    rewrite upd_init; auto; try omega.
    entailer!.
    Exists (bufs ++ [b]); rewrite Zlength_app, <- app_assoc, !map_app, !sepcon_app, Forall_app; simpl; entailer!.
    { exists 2; auto. } }
  Intros bufs; rewrite Zminus_diag, app_nil_r.
  rewrite <- seq_assoc.
  forward_for_simple_bound N (EX i : Z, PROP () LOCAL (gvar _comm comm; gvar _lock lock; gvar _bufs buf)
    SEP (EX locks : list val, EX comms : list val, !!(Zlength locks = i /\ Zlength comms = i /\
         Forall isptr comms) &&
          (data_at Ews (tarray (tptr tlock) N) (locks ++ repeat Vundef (Z.to_nat (N - i))) lock *
           data_at Ews (tarray (tptr tint) N) (comms ++ repeat Vundef (Z.to_nat (N - i))) comm *
           fold_right sepcon emp (map (fun r => lock_inv Tsh (Znth r locks Vundef)
             (comm_inv (Znth r comms Vundef) bufs (Znth r shs Tsh) gsh2)) (upto (Z.to_nat i))) *
           fold_right sepcon emp (map (malloc_token Tsh (sizeof tlock)) locks)) *
           fold_right sepcon emp (map (ghost gsh1 (-1) (Tsh, [])) comms) *
           fold_right sepcon emp (map (malloc_token Tsh (sizeof tint)) comms);
         @data_at CompSpecs Ews (tarray (tptr tbuffer) B) bufs buf;
         fold_right sepcon emp (map (data_at_ Tsh tbuffer) bufs);
         fold_right sepcon emp (map (malloc_token Tsh (sizeof tbuffer)) bufs))).
  { unfold N; computable. }
  { unfold N; computable. }
  { Exists ([] : list val) ([] : list val); rewrite !data_at__eq; entailer!. }
  { Intros locks comms.
    forward_call (sizeof tint).
    { simpl; computable. }
    Intro c.
    rewrite malloc_compat; auto; Intros.
    rewrite memory_block_data_at_; auto.
    forward.
    forward.
    forward_call (sizeof tlock).
    { admit. }
    { simpl; computable. }
    Intro l.
    rewrite malloc_compat; auto; Intros.
    rewrite memory_block_data_at_; auto.
    rewrite <- lock_struct_array.
    forward.
    forward_call (l, Tsh, comm_inv c bufs (Znth i shs Tsh) gsh2).
    (* make ghost vars here *)
    gather_SEP 3; eapply new_ghost with (i := -1).
    (* Actually, i should probably be forced to match the current value in general. *)
    erewrite <- ghost_share_join with (sh := Tsh); eauto.
    forward_call (l, Tsh, comm_inv c bufs (Znth i shs Tsh) gsh2).
    { unfold comm_inv; rewrite ?sepcon_assoc; rewrite <- sepcon_emp at 1; rewrite sepcon_comm;
        apply sepcon_derives;
        [repeat apply andp_right; auto; eapply derives_trans; try apply positive_weak_positive; auto|].
      { apply AE_inv_precise; auto. }
      unfold AE_inv.
      Exists ([] : hist) (-1); unfold comm_R at 3.
      unfold last_two_reads, last_write, prev_taken; simpl; entailer!.
      { split; computable. }
      match goal with |- ?P |-- _ => subst Frame; instantiate (1 := [P]); simpl; cancel end.
      admit. }
    Exists (locks ++ [l]) (comms ++ [c]); rewrite !upd_init; try omega.
    rewrite !Zlength_app, !Zlength_cons, !Zlength_nil; rewrite <- !app_assoc.
    go_lower.
    apply andp_right; [apply prop_right; split; auto; omega|].
    apply andp_right; [apply prop_right; auto|].
    rewrite !sepcon_andp_prop'; apply andp_right; [apply prop_right; rewrite Forall_app; repeat split; auto; omega|].
    rewrite Z2Nat.inj_add, upto_app, !map_app, !sepcon_app; try omega; simpl.
    rewrite Z2Nat.id, Z.add_0_r; [|omega].
    rewrite !Znth_app1; auto.
    replace (Z.to_nat (N - (Zlength locks + 1))) with (Z.to_nat (N - (i + 1))) by (subst; clear; Omega0).
    subst; rewrite Zlength_correct, Nat2Z.id.
    rewrite <- lock_struct_array; unfold comm_inv, AE_inv.
    erewrite map_ext_in; [cancel|].
    intros; rewrite In_upto, <- Zlength_correct in *.
    rewrite !app_Znth1; try omega; reflexivity.
    { exists 2; auto. }
    { exists 2; auto. } }
  forward.
  { entailer!.
    apply Forall_Znth, Forall_impl with (P := isptr); try (unfold B, N in *; omega); auto. }
  replace (fold_right sepcon emp (map (data_at_ Tsh tbuffer) bufs)) with
    (fold_right sepcon emp (map (data_at_ Tsh tbuffer) (sublist 0 (Zlength bufs) bufs)))
    by (rewrite sublist_same; auto).
  rewrite sublist_next with (d := Vundef); try (unfold B, N in *; omega); simpl.
  assert_PROP (field_compatible tbuffer [] (Znth 0 bufs Vundef)) by entailer!.
  forward_call (Tsh, tbuffer, Znth 0 bufs Vundef, 0, sizeof tbuffer).
  { repeat split; simpl; auto; computable. }
  forward.
  rewrite !app_nil_r.
  Exists comms locks bufs; entailer!.
  admit.
Admitted.

Lemma body_initialize_reader : semax_body Vprog Gprog f_initialize_reader initialize_reader_spec.
Proof.
  start_function.
  assert_PROP (0 <= r < N) as Hr.
  { go_lowerx; apply sepcon_derives_prop, field_at_array_inbounds. }
  forward.
  forward.
  forward.
Qed.

Lemma ghost_var_precise' : forall sh t v p, precise (ghost_var sh t v p).
Proof.
  intros; apply derives_precise' with (Q := EX v : reptype t, ghost_var sh t v p);
    [Exists v; auto | apply ghost_var_precise].
Qed.
Hint Resolve ghost_var_precise ghost_var_precise'.

Lemma last_two_reads_cons : forall r w h, last_two_reads (AE r w :: h) =
  if eq_dec w (-1) then if eq_dec r (-1) then last_two_reads h else (r, fst (last_two_reads h))
  else last_two_reads h.
Proof.
  intros; unfold last_two_reads; simpl.
  destruct (eq_dec w (-1)); auto.
  destruct (eq_dec r (-1)); auto.
  destruct (find_read (h ++ [AE 0 (-1)])) as [(?, ?)|]; auto.
  destruct (find_read l) as [(?, ?)|]; auto.
Qed.

Lemma prev_taken_cons : forall r w h, prev_taken (AE r w :: h) =
  if eq_dec w (-1) then prev_taken h else match find_read h with Some (b, _) => b | None => 0 end.
Proof.
  intros; unfold prev_taken; simpl.
  destruct (eq_dec w (-1)); auto.
Qed.

Lemma find_read_pos : forall h v rest, find_read h = Some (v, rest) -> v <> -1.
Proof.
  induction h; [discriminate|]; simpl; intros.
  destruct a.
  destruct (eq_dec w (-1)); eauto.
  destruct (eq_dec r (-1)); eauto.
  inv H; auto.
Qed.

Lemma last_two_reads_fst : forall h, fst (last_two_reads h) <> -1.
Proof.
  intro; unfold last_two_reads.
  rewrite find_read0.
  destruct (find_read h) as [(?, ?)|] eqn: Hfind; simpl; [|discriminate].
  pose proof (find_read_pos _ _ _ Hfind).
  destruct (find_read (l ++ [AE 0 (-1)])) as [(?, ?)|]; auto.
Qed.

Lemma find_read_In : forall h b rest, find_read h = Some (b, rest) -> In (AE b (-1)) h.
Proof.
  induction h; simpl; intros; try discriminate.
  destruct a.
  destruct (eq_dec w (-1)); [|right; eapply IHh; eauto].
  destruct (eq_dec r (-1)); [right; eapply IHh; eauto|].
  inv H; auto.
Qed.

Corollary last_two_reads_In : forall h, In (AE (fst (last_two_reads h)) (-1)) (h ++ [AE 0 (-1)]).
Proof.
  unfold last_two_reads; intros.
  rewrite find_read0.
  destruct (find_read h) as [(?, ?)|] eqn: Hfind; simpl.
  - apply find_read_In in Hfind.
    destruct (find_read (l ++ [AE 0 (-1)])) as [(?, ?)|]; rewrite in_app; auto.
  - rewrite in_app; simpl; auto.
Qed.

Lemma repable_buf : forall a, -1 <= a < B -> repable_signed a.
Proof.
  intros ? (? & ?).
  split; [transitivity (-1) | transitivity B]; unfold B, N in *; try computable; auto; omega.
Qed.

Lemma SEPx_sepcon : forall A B R, SEPx (A * B :: R) = SEPx (A :: B :: R).
Proof.
  intros; unfold SEPx; simpl.
  rewrite sepcon_assoc; auto.
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
    fun h b => !!(b = -1 /\ fst (last_two_reads h) = b0) &&
      (EX v : Z, data_at sh tbuffer (vint v) (Znth b0 bufs Vundef)) * ghost_var gsh1 tint (vint b0) c,
    comm_R bufs sh gsh2 c, fun h b => !!(-1 <= b < B) &&
      (EX v : Z, data_at sh tbuffer (vint v) (Znth (if eq_dec b (-1) then b0 else b) bufs Vundef)) *
      ghost_var gsh1 tint (vint (fst (last_two_reads h))) c).
  { unfold comm_inv; entailer!.
    rewrite <- sepcon_emp at 1; rewrite sepcon_comm; apply sepcon_derives; [|cancel].
    apply andp_right; auto.
    eapply derives_trans; [|apply precise_weak_precise]; auto.
    apply derives_precise' with (Q := data_at_ sh tbuffer (Znth (fst (last_two_reads h)) bufs Vundef) *
      EX v : val, ghost_var gsh1 tint v c); [|apply precise_sepcon; [auto |
      apply ghost_var_precise with (t := tint)]].
    clear; Exists (vint (fst (last_two_reads h))); entailer!. }
  { repeat (split; auto); try computable.
    unfold AE_spec, comm_R; intros.
    intros ???????? Ha.
    rewrite !last_two_reads_cons, prev_taken_cons in Ha.
    unfold last_write in *; simpl in *.
    pose proof (last_two_reads_fst hx).
    destruct (last_two_reads hx) as (b1', b2') eqn: Hlast.
    rewrite !sepcon_andp_prop', !sepcon_andp_prop.
    erewrite extract_prop_in_SEP with (n := O); simpl; eauto.
    erewrite extract_prop_in_SEP with (n := O); simpl; eauto.
    Intros; subst.
    rewrite sepcon_comm, <- !sepcon_assoc, 3sepcon_assoc.
    assert_PROP (b1' = fst (last_two_reads h)).
    { go_lowerx.
      do 2 apply sepcon_derives_prop.
      eapply derives_trans; [apply ghost_var_inj|].
      apply prop_left; intro; apply prop_right.
      apply repr_inj_signed; try congruence.
      + pose proof (last_two_reads_In hx) as Hin.
        rewrite in_app in Hin; destruct Hin as [Hin | [Hin | ?]]; [| inv Hin | contradiction].
        * match goal with H : Forall _ _ |- _ => rewrite Forall_forall in H; specialize (H _ Hin) end.
          rewrite Hlast in *; simpl in *; apply repable_buf; omega.
        * rewrite Hlast in *; simpl in *; subst; split; computable.
      + apply repable_buf; omega. }
    subst; erewrite ghost_var_share_join; eauto.
    rewrite SEPx_sepcon.
    apply change_ghost_var with (v' := vint (if eq_dec vx (-1) then fst (last_two_reads h) else vx)).
    eapply semax_pre, Ha.
    go_lowerx.
    rewrite !sepcon_andp_prop', !sepcon_andp_prop, !sepcon_andp_prop'.
    apply andp_right.
    { apply prop_right; repeat split; try constructor; auto; omega. }
    apply andp_right; [apply prop_right; auto|].
    erewrite <- ghost_var_share_join; eauto.
    rewrite !eq_dec_refl in Ha.
    destruct (eq_dec vx (-1)).
    - replace (fst (last_two_reads hc)) with (fst (last_two_reads h)) by auto; cancel.
      apply andp_right; auto.
      eapply derives_trans; [|apply precise_weak_precise]; auto.
      apply precise_andp2; repeat apply precise_sepcon; auto.
      destruct (eq_dec b2' (-1)); auto.
      apply derives_precise' with (Q := @data_at_ CompSpecs sh tbuffer (Znth b2' bufs Vundef)); auto.
      entailer!.
    - simpl in *; destruct (eq_dec (fst (last_two_reads h)) (-1)); [absurd (fst (last_two_reads h) = -1); auto|].
      subst; cancel.
      apply andp_right; auto.
      eapply derives_trans; [|apply precise_weak_precise]; auto.
      apply precise_andp2; repeat apply precise_sepcon; auto.
      eapply derives_precise' with (Q := @data_at_ CompSpecs sh tbuffer _); auto.
      entailer!. }
  Intros b.
  exploit repable_buf; eauto; intro.
  match goal with |- semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROP () (LOCALx (temp _t'2 (vint (if eq_dec b (-1) then 0 else 1)) :: Q) (SEPx R))) end.
  { forward.
    destruct (eq_dec b (-1)); [omega|].
    entailer!.
    simpl.
    rewrite add_repr.
    destruct (Int.lt (Int.repr b) (Int.repr (3 + 2))) eqn: Hlt; auto.
    apply lt_repr_false in Hlt; auto; unfold repable_signed; try computable.
    unfold B, N in *; omega. }
  { forward.
    destruct (eq_dec b (-1)); [|omega].
    entailer!. }
  forward_if (PROP () LOCAL (temp _b (vint (if eq_dec b (-1) then b0 else b)); temp _r (vint r);
      gvar _reading reading; gvar _last_read last_read; gvar _lock lock; gvar _comm comm)
    SEP (lock_inv sh2 l (AE_inv c (-1) Tsh gsh2 (comm_R bufs sh gsh2 c));
         ghost gsh1 (-1) (sh2, AE b (-1) :: h) c;
         EX v : Z, data_at sh tbuffer (vint v) (Znth (if eq_dec b (-1) then b0 else b) bufs Vundef);
         ghost_var gsh1 tint (vint (fst (last_two_reads (AE b (-1) :: h)))) c;
         field_at_ Ews (tarray tint N) [ArraySubsc r] reading;
         field_at Ews (tarray tint N) [ArraySubsc r] (vint (if eq_dec b (-1) then b0 else b)) last_read;
         field_at sh1 (tarray (tptr tint) N) [ArraySubsc r] c comm;
         field_at sh1 (tarray (tptr (Tstruct _lock_t noattr)) N) [ArraySubsc r] l lock)).
  - forward.
    simpl eq_dec; destruct (eq_dec b (-1)); [match goal with H : _ <> _ |- _ => contradiction H; auto end|].
    entailer!.
  - forward.
    simpl eq_dec; destruct (eq_dec b (-1)); [|discriminate].
    entailer!.
  - forward.
    forward.
    Exists (if eq_dec b (-1) then fst (last_two_reads h) else b) b v.
    apply andp_right.
    { apply prop_right.
      split; [destruct (eq_dec b (-1)); auto; omega|].
      rewrite last_two_reads_cons, eq_dec_refl.
      destruct (eq_dec b (-1)); auto. }
    rewrite TT_andp; unfold comm_inv; rewrite lock_struct_array_sub; cancel.
Qed.

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

Opaque upto.

Lemma body_start_write : semax_body Vprog Gprog f_start_write start_write_spec.
Proof.
  start_function.
  rewrite <- seq_assoc.
  forward_for_simple_bound B (EX i : Z, PROP ( )
   LOCAL (lvar _available (tarray tint B) lvar0; gvar _writing writing; gvar _last_given last_given;
   gvar _last_taken last_taken)
   SEP (data_at Tsh (tarray tint B) (repeat (vint 1) (Z.to_nat i) ++ repeat Vundef (Z.to_nat (B - i))) lvar0;
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
   LOCAL (temp _i (vint B); lvar _available (tarray tint B) lvar0; 
   gvar _writing writing; gvar _last_given last_given; gvar _last_taken last_taken)
   SEP (field_at Tsh (tarray tint B) [] (map (fun x => vint (if eq_dec x b0 then 0
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
             gvar _writing writing; gvar _last_given last_given; gvar _last_taken last_taken)
      SEP (field_at Tsh (tarray tint B) [] (map (fun x => vint (if eq_dec x b0 then 0
             else if in_dec eq_dec x (sublist 0 (i + 1) lasts) then 0 else 1)) (upto (Z.to_nat B))) lvar0;
           data_at_ Ews tint writing; data_at Ews tint (vint b0) last_given;
           data_at Ews (tarray tint N) (map (fun x : Z => vint x) lasts) last_taken)).
    - assert (0 <= Znth i lasts (-1) < B).
      { exploit (Forall_Znth(A := Z)); eauto.
        instantiate (1 := -1); intro.
        destruct (eq_dec (Znth i lasts (-1)) (-1)); [|unfold B, N in *; simpl in *; omega].
        match goal with H : Int.repr _ <> Int.neg _ |- _ => contradiction H; rewrite e; auto end. }
      forward.
      entailer!.
      rewrite upd_Znth_eq with (d := Vundef); auto.
      apply derives_refl'; erewrite map_ext_in; [reflexivity|].
      intros; rewrite In_upto, map_length, upto_length in *; simpl in *.
      erewrite Znth_map, Znth_upto; simpl; auto; try omega.
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
           gvar _last_given last_given; gvar _last_taken last_taken)
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
             gvar _last_given last_given; gvar _last_taken last_taken)
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
    erewrite Znth_map, Znth_upto; rewrite ?Zlength_upto, ?Z2Nat.id; try assumption; try omega.
    forward_if (PROP (Znth i available (vint 0) = vint 0)
      LOCAL (temp _i__1 (vint i); lvar _available (tarray tint B) lvar0; gvar _writing writing;
             gvar _last_given last_given; gvar _last_taken last_taken)
      SEP (field_at Tsh (tarray tint B) [] available lvar0; data_at_ Ews tint writing;
           data_at Ews tint (vint b0) last_given; data_at Ews (tarray tint N) (map (fun x : Z => vint x) lasts) last_taken)).
    { forward.
      forward.
      Exists lvar0 i; entailer!.
      { destruct (eq_dec i b0); [|destruct (in_dec eq_dec i lasts)]; auto;
          match goal with H : Int.repr 0 <> Int.zero |- _ => contradiction H; auto end. }
      unfold data_at_, field_at_; entailer!. }
    { forward.
      entailer!.
      subst available.
      erewrite Znth_map, Znth_upto; rewrite ?Zlength_upto, ?Z2Nat.id; try assumption; try omega.
      destruct (eq_dec _ _); auto.
      destruct (in_dec _ _ _); auto; discriminate. }
    intros.
    unfold exit_tycon, overridePost.
    destruct (eq_dec ek EK_normal); [subst | apply drop_tc_environ].
    Intros; unfold POSTCONDITION, abbreviate, normal_ret_assert, loop1_ret_assert.
    instantiate (1 := EX i : Z, PROP (0 <= i < B; Znth i available (vint 0) = vint 0;
      forall j : Z, j < i -> Znth j available (vint 0) = vint 0)
      LOCAL (temp _i__1 (vint i); lvar _available (tarray tint B) lvar0; gvar _writing writing;
             gvar _last_given last_given; gvar _last_taken last_taken)
      SEP (field_at Tsh (tarray tint B) [] available lvar0; data_at_ Ews tint writing;
           data_at Ews tint (vint b0) last_given; data_at Ews (tarray tint N) (map (fun x : Z => vint x) lasts) last_taken)).
    Exists i; entailer!.
  + Intros i.
    forward.
    Exists (i + 1); entailer!.
    intros; destruct (eq_dec j i); subst; auto.
    assert (j < i) by omega; auto.
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

Lemma find_write_rest : forall h b rest, find_write h = Some (b, rest) -> exists n, rest = skipn n h.
Proof.
  induction h; simpl; intros; try discriminate.
  destruct a.
  destruct (eq_dec w (-1)).
  - destruct (IHh _ _ H) as (n & ?); subst.
    exists (S n); auto.
  - inv H; exists 1%nat; auto.
Qed.

Corollary prev_taken_In : forall h, prev_taken h = -1 \/ prev_taken h = 0 \/ In (AE (prev_taken h) (-1)) h.
Proof.
  intros; unfold prev_taken.
  destruct (find_write h) as [(?, ?)|] eqn: Hfind; auto.
  apply find_write_rest in Hfind; destruct Hfind as (n & ?); subst.
  destruct (find_read (skipn n h)) as [(?, ?)|] eqn: Hfind; auto.
  pose proof (find_read_In _ _ _ Hfind).
  right; right; eapply skipn_In; eauto.
Qed.

Lemma write_val : forall w h rest v (Hw : find_write h = Some (w, rest))
  (Hh : apply_hist (-1) h = Some v), v = w \/ v = -1.
Proof.
  induction h; [discriminate|]; simpl; intros.
  destruct a.
  destruct (apply_hist (-1) h) eqn: Hh'; [|discriminate].
  destruct (eq_dec z r); inv Hh.
  destruct (eq_dec v (-1)); auto.
  inv Hw; auto.
Qed.

Lemma find_write_read : forall w h rest (Hw : find_write h = Some (w, rest))
  (Hread : apply_hist (-1) h = Some (-1)),
  exists rest', find_read h = Some (w, rest').
Proof.
  induction h; [discriminate|]; simpl; intros.
  destruct a.
  destruct (apply_hist (-1) h) eqn: Hh; [|discriminate].
  destruct (eq_dec z r); [subst | discriminate].
  inv Hread.
  rewrite eq_dec_refl; rewrite eq_dec_refl in Hw.
  destruct (eq_dec r (-1)); eauto.
  exploit write_val; eauto; intros [? | ?]; subst; eauto; contradiction n; auto.
Qed.

Lemma take_read : forall h v, apply_hist (-1) h = Some v ->
  prev_taken h = if eq_dec v (-1) then snd (last_two_reads h)
                 else fst (last_two_reads h).
Proof.
  induction h; simpl; intros.
  - inv H.
    rewrite eq_dec_refl; auto.
  - destruct a; rewrite prev_taken_cons, last_two_reads_cons.
    destruct (apply_hist (-1) h) eqn: Hh; [|discriminate].
    destruct (eq_dec z r); [subst | discriminate].
    inv H.
    erewrite IHh; eauto.
    destruct (eq_dec v (-1)).
    + destruct (eq_dec r (-1)); auto.
    + unfold last_two_reads; rewrite find_read0.
      destruct (find_read h) as [(?, ?)|]; auto.
      destruct (find_read (l ++ [AE 0 (-1)])) as [(?, ?)|]; auto.
Qed.

Lemma find_write_In : forall h b rest, find_write h = Some (b, rest) -> exists r, In (AE r b) h.
Proof.
  induction h; simpl; intros; try discriminate.
  destruct a.
  destruct (eq_dec w (-1)); [exploit IHh; eauto; intros (? & ?); eauto|].
  inv H; eauto.
Qed.

Lemma make_shares_app : forall i l1 l2 shs, Zlength l1 + Zlength l2 <= Zlength shs ->
  make_shares shs (l1 ++ l2) i =
  make_shares shs l1 i ++ make_shares (sublist (Zlength l1) (Zlength shs) shs) l2 i.
Proof.
  induction l1; simpl; intros.
  - rewrite sublist_same; auto.
  - rewrite Zlength_cons in *.
    destruct shs.
    { rewrite Zlength_nil, !Zlength_correct in *; omega. }
    rewrite Zlength_cons in *; simpl; rewrite IHl1; [|omega].
    rewrite sublist_S_cons with (i0 := Z.succ _); [|rewrite Zlength_correct; omega].
    unfold Z.succ; rewrite !Z.add_simpl_r.
    destruct (eq_dec a i); auto.
Qed.

Lemma make_shares_ext : forall i d l l' shs (Hlen : Zlength l = Zlength l')
  (Hi : forall j, 0 <= j < Zlength l -> Znth j l d = i <-> Znth j l' d = i),
  make_shares shs l i = make_shares shs l' i.
Proof.
  induction l; destruct l'; simpl; intros; rewrite ?Zlength_cons, ?Zlength_nil in *; auto;
    try (rewrite Zlength_correct in *; omega).
  exploit (Hi 0); [rewrite Zlength_correct; omega|].
  rewrite !Znth_0_cons; intro Hiff.
  rewrite (IHl l'); try omega.
  - destruct (eq_dec a i), (eq_dec z i); tauto.
  - intros; exploit (Hi (j + 1)); [omega|].
    rewrite !Znth_pos_cons, !Z.add_simpl_r; auto; omega.
Qed.

Lemma find_read_write : forall h v, apply_hist (-1) h = Some v -> find_write h = None -> find_read h = None.
Proof.
  induction h; auto; simpl; intros.
  destruct a.
  destruct (apply_hist (-1) h) eqn: Hh; [|discriminate].
  destruct (eq_dec z r); [inv H | discriminate].
  destruct (eq_dec v (-1)); [|discriminate].
  destruct (eq_dec r (-1)); eauto.
  destruct h; [inv Hh; contradiction n; auto | simpl in *].
  destruct h.
  destruct (eq_dec w (-1)); [|discriminate].
  destruct (apply_hist (-1) h0); [|discriminate].
  destruct (eq_dec z r0); [|discriminate].
  inv Hh; omega.
Qed.

Fixpoint make_shares_inv shs (lasts : list Z) i {struct lasts} : list share :=
  match lasts with
  | [] => []
  | b :: rest => if eq_dec b i then hd Share.bot shs :: make_shares_inv (tl shs) rest i
                 else make_shares_inv (tl shs) rest i
  end.

Lemma make_shares_minus : forall i lasts sh0 shs sh' sh1 (Hsh' : sepalg_list.list_join sh0 shs sh')
  (Hsh1 : sepalg_list.list_join sh0 (make_shares shs lasts i) sh1)
  (Hlen : Zlength shs = Zlength lasts),
  sepalg_list.list_join sh1 (make_shares_inv shs lasts i) sh'.
Proof.
  induction lasts; destruct shs; simpl; intros; rewrite ?Zlength_cons, ?Zlength_nil in *;
    try (rewrite Zlength_correct in *; omega).
  - inv Hsh1; inv Hsh'; constructor.
  - inversion Hsh' as [|????? Hj1 Hj2]; subst.
    destruct (eq_dec a i).
    + apply sepalg.join_comm in Hj1; destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (x & ? & Hx).
      exploit IHlasts; eauto; [omega|].
      intro Hj'; destruct (sepalg_list.list_join_assoc2 Hj' Hx) as (? & ? & ?).
      econstructor; eauto.
    + inversion Hsh1 as [|????? Hja]; inversion Hsh' as [|????? Hjb]; subst.
      pose proof (sepalg.join_eq Hja Hjb); subst.
      eapply IHlasts; eauto; omega.
Qed.

Lemma make_shares_add : forall i i' d lasts j shs (Hj : 0 <= j < Zlength lasts)
  (Hi : Znth j lasts d = i) (Hi' : i' <> i) (Hlen : Zlength shs >= Zlength lasts),
  exists shs1 shs2, make_shares shs lasts i = shs1 ++ shs2 /\
    make_shares shs (upd_Znth j lasts i') i = shs1 ++ Znth j shs Tsh :: shs2.
Proof.
  induction lasts; destruct shs; simpl; intros; rewrite ?Zlength_cons, ?Zlength_nil in *; try omega.
  destruct (eq_dec j 0).
  - subst; rewrite Znth_0_cons in Hi', IHlasts; rewrite !Znth_0_cons.
    rewrite eq_dec_refl, upd_Znth0, Zlength_cons, sublist_1_cons, sublist_same; auto; try omega; simpl.
    destruct (eq_dec i' a); [contradiction Hi'; auto|].
    eexists [], _; simpl; split; eauto.
  - rewrite Znth_pos_cons in Hi; [|omega].
    rewrite Znth_pos_cons; [|omega].
    exploit (IHlasts (j - 1) shs); try omega.
    intros (shs1 & shs2 & Heq1 & Heq2).
    rewrite upd_Znth_cons; [simpl | omega].
    exists (if eq_dec a i then shs1 else t :: shs1), shs2; rewrite Heq1, Heq2; destruct (eq_dec a i); auto.
Qed.

Lemma make_shares_In : forall i lasts x shs (Hx : 0 <= x < Zlength lasts) (Hi : Znth x lasts 0 <> i)
  (Hlen : Zlength shs >= Zlength lasts),
  In (Znth x shs Tsh) (make_shares shs lasts i).
Proof.
  induction lasts; simpl; intros.
  - rewrite Zlength_nil in *; omega.
  - destruct shs; rewrite !Zlength_cons in *; [rewrite Zlength_nil, Zlength_correct in *; omega|].
    destruct (eq_dec x 0).
    + subst; rewrite Znth_0_cons in Hi; rewrite Znth_0_cons.
      destruct (eq_dec a i); [contradiction Hi | simpl]; auto.
    + rewrite Znth_pos_cons in Hi; [|omega].
      rewrite Znth_pos_cons; [|omega].
      exploit (IHlasts (x - 1) shs); eauto; try omega.
      destruct (eq_dec a i); simpl; auto.
Qed.

Lemma readable_share_list_join : forall sh shs sh', sepalg_list.list_join sh shs sh' ->
  readable_share sh \/ Exists readable_share shs -> readable_share sh'.
Proof.
  induction 1; intros [? | Hexists]; try inv Hexists; auto.
  - apply IHfold_rel; left; eapply readable_share_join; eauto.
  - apply IHfold_rel; left; eapply readable_share_join; eauto.
Qed.

Lemma make_shares_inv_In : forall i lasts x shs (Hx : 0 <= x < Zlength lasts) (Hi : Znth x lasts 0 = i)
  (Hlen : Zlength shs >= Zlength lasts),
  In (Znth x shs Tsh) (make_shares_inv shs lasts i).
Proof.
  induction lasts; simpl; intros.
  - rewrite Zlength_nil in *; omega.
  - destruct shs; rewrite !Zlength_cons in *; [rewrite Zlength_nil, Zlength_correct in *; omega|].
    destruct (eq_dec x 0).
    + subst; rewrite Znth_0_cons in *; rewrite Znth_0_cons; subst.
      rewrite eq_dec_refl; simpl; auto.
    + rewrite Znth_pos_cons in Hi; [|omega].
      rewrite Znth_pos_cons; [|omega].
      exploit (IHlasts (x - 1) shs); eauto; try omega.
      destruct (eq_dec a i); simpl; auto.
Qed.

Lemma replace_nth_sepcon : forall P l i, P * fold_right sepcon emp (upd_Znth i l emp) =
  fold_right sepcon emp (upd_Znth i l P).
Proof.
  intros; unfold upd_Znth.
  rewrite !sepcon_app; simpl.
  rewrite emp_sepcon, <- !sepcon_assoc, (sepcon_comm P); auto.
Qed.

Lemma list_join_eq : forall shs (sh sh1 sh2 : share)
  (Hsh1 : sepalg_list.list_join sh shs sh1) (Hsh2 : sepalg_list.list_join sh shs sh2), sh1 = sh2.
Proof.
  induction 1; intros; inv Hsh2; auto.
  assert (w1 = w3) by (eapply sepalg.join_eq; eauto); subst; auto.
Qed.

Lemma make_shares_sub : forall i lasts shs sh0 sh1 sh2 (Hlen : Zlength shs >= Zlength lasts)
  (Hsh1 : sepalg_list.list_join sh0 shs sh1) (Hsh2 : sepalg_list.list_join sh0 (make_shares shs lasts i) sh2),
  sepalg.join_sub sh2 sh1.
Proof.
  induction lasts; destruct shs; simpl; intros; rewrite ?Zlength_nil, ?Zlength_cons in *;
    try (rewrite Zlength_correct in *; omega).
  - inv Hsh1; inv Hsh2; apply sepalg.join_sub_refl.
  - inversion Hsh1 as [|????? Hj1 Hj2]; inv Hsh2.
    destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (? & ? & ?); eexists; eauto.
  - inversion Hsh1 as [|????? Hj1 Hj2]; subst.
    destruct (eq_dec a i).
    + apply sepalg.join_comm in Hj1; destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (? & ? & ?).
      exploit IHlasts; eauto; [omega|].
      intro; eapply sepalg.join_sub_trans; eauto; eexists; eauto.
    + inversion Hsh2 as [|????? Hj1']; subst.
      pose proof (sepalg.join_eq Hj1 Hj1'); subst.
      eapply IHlasts; eauto; omega.
Qed.

Lemma make_shares_join : forall i d lasts shs sh0 j sh1 sh2 (Hlen : Zlength shs >= Zlength lasts)
  (Hsh1 : sepalg_list.list_join sh0 shs sh1) (Hsh2 : sepalg_list.list_join sh0 (make_shares shs lasts i) sh2)
  (Hin : 0 <= j < Zlength shs) (Hj : Znth j lasts d = i), exists sh', sepalg.join sh2 (Znth j shs Tsh) sh'.
Proof.
  induction lasts; destruct shs; simpl; intros; rewrite ?Zlength_nil, ?Zlength_cons in *;
    try (rewrite Zlength_correct in *; omega); try omega.
  { rewrite Znth_overflow in Hj; [|rewrite Zlength_nil; omega].
    inv Hsh2.
    exploit (Znth_In j (t :: shs) Tsh); [rewrite Zlength_cons; auto|].
    intro Hin'; apply in_split in Hin'.
    destruct Hin' as (? & ? & Heq); rewrite Heq in Hsh1.
    apply list_join_comm in Hsh1; inv Hsh1; eauto. }
  destruct (eq_dec j 0).
  - subst j; rewrite Znth_0_cons in Hj; rewrite Znth_0_cons; subst.
    rewrite eq_dec_refl in Hsh2.
    inversion Hsh1 as [|????? Hj1 Hj2]; subst.
    apply sepalg.join_comm in Hj1; destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (? & ? & ?).
    exploit make_shares_sub; eauto; [omega|].
    intro; eapply sepalg.join_sub_joins_trans; eauto.
  - rewrite Znth_pos_cons in Hj; [|omega].
    rewrite Znth_pos_cons; [|omega].
    inversion Hsh1 as [|????? Hj1 Hj2].
    destruct (eq_dec a i); subst.
    + apply sepalg.join_comm in Hj1; destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (? & ? & ?).
      eapply IHlasts; eauto; omega.
    + inversion Hsh2 as [|????? Hj1']; subst.
      pose proof (sepalg.join_eq Hj1 Hj1'); subst.
      eapply IHlasts; eauto; omega.
Qed.

Lemma upd_Znth_twice : forall {A} i l (x y : A), 0 <= i < Zlength l ->
  upd_Znth i (upd_Znth i l x) y = upd_Znth i l y.
Proof.
  intros; unfold upd_Znth.
  rewrite !sublist_app; rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_sublist; try omega.
  rewrite 2Z.min_l, 2Z.min_r, 2Z.max_r, 2Z.max_l; try omega.
  rewrite !sublist_nil, app_nil_r; simpl.
  rewrite sublist_S_cons, !sublist_sublist; try omega.
  f_equal; f_equal; [|f_equal]; omega.
Qed.

Lemma hd_Znth : forall {A} d (l : list A), hd d l = Znth 0 l d.
Proof.
  destruct l; auto.
Qed.

Lemma upd_write_shares : forall bufs b b0 lasts shs sh0 (Hb : 0 <= b < B) (Hb0 : 0 <= b0 < B)
  (Hlasts : Forall (fun x : Z => -1 <= x < B) lasts) (Hshs : Zlength shs = N)
  (Hread0 : readable_share sh0) (Hread : Forall readable_share shs) (Hsh0 : sepalg_list.list_join sh0 shs Tsh)
  (Hdiff : b <> b0) (Hout : ~ In b lasts) (Hout0 : ~ In b0 lasts) (Hlasts : Zlength lasts = N)
  bsh' v' (Hv' : -1 <= v' < B) h' (Hh' : 0 <= Zlength h' < N)
  (Hbsh' : sepalg_list.list_join sh0 (sublist (Zlength h' + 1) N shs) bsh')
  bsh (Hbsh : sepalg.join bsh' (Znth (Zlength h') shs Tsh) bsh),
  (if eq_dec v' (-1) then if eq_dec (Znth (Zlength h') lasts 0) (-1) then emp else
   EX v0 : Z, data_at (Znth (Zlength h') shs Tsh) tbuffer (vint v0) (Znth (Znth (Zlength h') lasts 0) bufs Vundef)
   else !! (v' = b0) && (EX v'0 : Z, data_at (Znth (Zlength h') shs Tsh) tbuffer (vint v'0) (Znth v' bufs Vundef))) *
  ((EX v0 : Z, data_at bsh' tbuffer (vint v0) (Znth b bufs Vundef)) *
  fold_right sepcon emp (upd_Znth b (map (fun a => EX sh : share, !! (if eq_dec a b0 then
    sepalg_list.list_join sh0 (make_shares shs (sublist 0 (Zlength h')
      (map (fun i : Z => if eq_dec (Znth i h' 0) (-1) then b0 else Znth i lasts 0) (upto (Z.to_nat N)))) a) sh
      else if eq_dec a b then sepalg_list.list_join sh0 (sublist (Zlength h') N shs) sh
      else sepalg_list.list_join sh0 (make_shares shs
      (map (fun i : Z => if eq_dec (Znth i h' 0) (-1) then b0 else Znth i lasts 0) (upto (Z.to_nat N))) a) sh) &&
      (EX v0 : Z, data_at sh tbuffer (vint v0) (Znth a bufs Vundef))) (upto (Z.to_nat B))) emp))
  |-- fold_right sepcon emp (map (fun a => EX sh : share, !! (if eq_dec a b0 then
        sepalg_list.list_join sh0 (make_shares shs (sublist 0 (Zlength h' + 1)
          (map (fun i : Z => if eq_dec (Znth i (h' ++ [v']) 0) (-1) then b0 else Znth i lasts 0) (upto (Z.to_nat N)))) a) sh
          else if eq_dec a b then sepalg_list.list_join sh0 (sublist (Zlength h' + 1) N shs) sh
          else sepalg_list.list_join sh0 (make_shares shs
          (map (fun i : Z => if eq_dec (Znth i (h' ++ [v']) 0) (-1) then b0 else Znth i lasts 0) (upto (Z.to_nat N))) a) sh) &&
          (EX v0 : Z, data_at sh tbuffer (vint v0) (Znth a bufs Vundef))) (upto (Z.to_nat B))).
Proof.
  intros; set (shi := Znth (Zlength h') shs Tsh).
  assert (readable_share shi).
  { apply Forall_Znth; auto; omega. }
  set (lasti := Znth (Zlength h') lasts 0).
  exploit (Znth_In (Zlength h') lasts 0); [omega | intro Hini].
  assert (lasti <> b) as Hneq.
  { intro; match goal with H : ~In b lasts |- _ => contradiction H end; subst b lasti; auto. }
  assert (lasti <> b0) as Hneq0.
  { intro; match goal with H : ~In b0 lasts |- _ => contradiction H end; subst b0 lasti; auto. }
  set (l0 := upd_Znth b (map (fun a => EX sh : share, !!(if eq_dec a b0 then
             sepalg_list.list_join sh0 (make_shares shs (sublist 0 (Zlength h')
               (map (fun i => if eq_dec (Znth i h' 0) (-1) then b0 else Znth i lasts 0) (upto (Z.to_nat N)))) a) sh
           else if eq_dec a b then sepalg_list.list_join sh0 (sublist (Zlength h') N shs) sh
           else sepalg_list.list_join sh0 (make_shares shs (map (fun i => if eq_dec (Znth i h' 0) (-1) then b0
                                           else Znth i lasts 0) (upto (Z.to_nat N))) a) sh) &&
          (EX v1 : Z, @data_at CompSpecs sh tbuffer (vint v1) (Znth a bufs Vundef))) (upto (Z.to_nat B)))
          (EX v1 : Z, @data_at CompSpecs bsh' tbuffer (vint v1) (Znth b bufs Vundef))).
  assert (Zlength l0 = B).
  { subst l0; rewrite upd_Znth_Zlength; rewrite Zlength_map, Zlength_upto; auto. }
  assert (lasti <> -1 -> 0 <= lasti < B).
  { intro; rewrite Forall_forall in Hlasts; specialize (Hlasts _ Hini); subst lasti; omega. }
  apply derives_trans with (fold_right sepcon emp (
    if eq_dec v' (-1) then if eq_dec lasti (-1) then l0 else upd_Znth lasti l0
            (EX sh : share, !!(exists sh', sepalg_list.list_join sh0 (make_shares shs
             (map (fun i => if eq_dec (Znth i h' 0) (-1) then b0 else Znth i lasts 0) (upto (Z.to_nat N))) lasti) sh' /\
             sepalg.join sh' shi sh) &&
            (EX v1 : Z, @data_at CompSpecs sh tbuffer (vint v1) (Znth lasti bufs Vundef)))
          else upd_Znth b0 l0 (EX sh : share, !!(exists sh', sepalg_list.list_join sh0 (make_shares shs
            (sublist 0 (Zlength h') (map (fun i => if eq_dec (Znth i h' 0) (-1) then b0 else Znth i lasts 0)
            (upto (Z.to_nat N)))) b0) sh' /\ sepalg.join sh' shi sh) &&
            (EX v1 : Z, @data_at CompSpecs sh tbuffer (vint v1) (Znth b0 bufs Vundef))))).
  { rewrite replace_nth_sepcon.
    destruct (eq_dec v' (-1)).
    - destruct (eq_dec lasti (-1)); [rewrite emp_sepcon; auto|].
      rewrite extract_nth_sepcon with (i := lasti); [|subst l0; omega].
      erewrite upd_Znth_diff, Znth_map, Znth_upto; rewrite ?Z2Nat.id; auto; try omega.
      destruct (eq_dec lasti b0); [contradiction Hneq0; auto|].
      destruct (eq_dec lasti b); [contradiction Hneq; auto|].
      Intros v1 ish v2.
      eapply derives_trans; [apply sepcon_derives; [apply data_at_value_cohere; auto | apply derives_refl]|].
      { eapply readable_share_list_join; eauto. }
      assert (exists sh', sepalg.join ish shi sh') as (sh' & ?).
      { eapply make_shares_join; eauto.
        + setoid_rewrite Hshs; rewrite Zlength_map, Zlength_upto, Z2Nat.id; omega.
        + setoid_rewrite Hshs; auto.
        + rewrite Znth_map', Znth_upto; [|rewrite Z2Nat.id; omega].
          rewrite Znth_overflow; auto; omega. }
      erewrite data_at_share_join; [|eapply sepalg.join_comm; eauto].
      rewrite (extract_nth_sepcon (upd_Znth lasti l0 (EX sh : share, _)) lasti); [|rewrite upd_Znth_Zlength; omega].
      rewrite upd_Znth_twice; [|omega].
      apply sepcon_derives; [|apply derives_refl].
      rewrite upd_Znth_same; [|omega].
      Exists sh'; apply andp_right; [|Exists v1; auto].
      apply prop_right; eauto.
    - Intros; subst.
      rewrite extract_nth_sepcon with (i := b0); [|subst l0; omega].
      erewrite upd_Znth_diff, Znth_map, Znth_upto; rewrite ?Z2Nat.id; auto; try omega.
      destruct (eq_dec b0 b0); [|contradiction n0; auto].
      Intros v1 ish v2.
      eapply derives_trans; [apply sepcon_derives; [apply data_at_value_cohere; auto | apply derives_refl]|].
      { eapply readable_share_list_join; eauto. }
      assert (exists sh', sepalg.join ish shi sh') as (sh' & ?).
      { eapply make_shares_join; eauto.
        + setoid_rewrite Hshs; rewrite Zlength_sublist; rewrite ?Zlength_map, ?Zlength_upto, ?Z2Nat.id; omega.
        + setoid_rewrite Hshs; auto.
        + rewrite Znth_overflow; auto.
          rewrite Zlength_sublist; rewrite ?Zlength_map, ?Zlength_upto, ?Z2Nat.id; omega. }
      erewrite data_at_share_join; [|eapply sepalg.join_comm; eauto].
      rewrite (extract_nth_sepcon (upd_Znth b0 l0 (EX sh : share, _)) b0); [|rewrite upd_Znth_Zlength; omega].
      rewrite upd_Znth_twice; [|omega].
      apply sepcon_derives; [|apply derives_refl].
      rewrite upd_Znth_same; [|omega].
      Exists sh'; apply andp_right; [|Exists v1; auto].
      apply prop_right; eauto. }
  apply derives_refl'; f_equal.
  match goal with |- ?l = _ => assert (Zlength l = B) as Hlen end.
  { destruct (eq_dec v' (-1)); [destruct (eq_dec lasti (-1))|]; auto; rewrite upd_Znth_Zlength; auto; omega. }
  apply list_Znth_eq' with (d := FF).
  { rewrite Hlen, Zlength_map, Zlength_upto; auto. }
  rewrite Hlen; intros.
  assert (0 <= j <= B) by omega.
  erewrite Znth_map, Znth_upto; auto.
  destruct (eq_dec j lasti); [|destruct (eq_dec j b0)]; subst.
  - destruct (eq_dec v' (-1)).
    destruct (eq_dec lasti (-1)); [omega|].
    + rewrite upd_Znth_same; [|omega].
      destruct (eq_dec lasti b0); [contradiction Hneq0; auto|].
      destruct (eq_dec lasti b); [contradiction Hneq; auto|].
      exploit (make_shares_add lasti b0 0 (map (fun i => if eq_dec (Znth i h' 0) (-1) then b0
        else Znth i lasts 0) (upto (Z.to_nat N))) (Zlength h') shs); auto.
      { erewrite Znth_map, Znth_upto; rewrite ?Zlength_upto, ?Z2Nat.id; try omega.
        rewrite Znth_overflow; [|omega].
        destruct (eq_dec 0 (-1)); [discriminate | auto]. }
      { setoid_rewrite Hshs; rewrite Zlength_map, Zlength_upto, Z2Nat.id; omega. }
      simpl; intros (shsa & shsb & Hshs1 & Hshs2).
      f_equal; extensionality; f_equal; f_equal.
      rewrite Hshs1.
      erewrite make_shares_ext, Hshs2.
      apply prop_ext; split.
      * intros (? & Hj1 & Hj2).
        apply list_join_comm.
        apply sepalg.join_comm in Hj2; destruct (sepalg_list.list_join_assoc2 Hj1 Hj2) as (? & ? & ?).
        econstructor; eauto.
        apply list_join_comm; auto.
      * intro Hj; apply list_join_comm in Hj.
        inversion Hj as [|????? Hj1 Hj2]; subst.
        apply sepalg.join_comm in Hj1; destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (? & ? & ?).
        do 2 eexists; eauto; apply list_join_comm; auto.
      * rewrite upd_Znth_Zlength; rewrite !Zlength_map; auto.
      * rewrite Zlength_map, Zlength_upto; intros.
        rewrite Znth_map', Znth_upto; [|omega].
        destruct (zlt j (Zlength h')); [|destruct (eq_dec j (Zlength h'))].
        -- rewrite app_Znth1, upd_Znth_diff; auto; try omega.
           erewrite Znth_map, Znth_upto; auto; [reflexivity | omega].
        -- subst; rewrite Znth_app1, eq_dec_refl, upd_Znth_same; auto; reflexivity.
        -- rewrite Znth_overflow, upd_Znth_diff; auto; [|rewrite Zlength_app, Zlength_cons, Zlength_nil; omega].
           erewrite Znth_map, Znth_upto; auto; [|omega].
           rewrite Znth_overflow with (al := h'); [reflexivity | omega].
    + subst l0; rewrite 2upd_Znth_diff; auto; try omega.
      erewrite Znth_map, Znth_upto; try assumption.
      destruct (eq_dec lasti b0); [contradiction Hneq0; auto|].
      destruct (eq_dec lasti b); [contradiction Hneq; auto|].
      simpl; erewrite make_shares_ext; eauto.
      rewrite Zlength_map, Zlength_upto; intros.
      erewrite Znth_map', Znth_map, !Znth_upto; auto; try omega.
      destruct (zlt j (Zlength h')); [|destruct (eq_dec j (Zlength h'))].
      * rewrite app_Znth1; auto; omega.
      * subst; rewrite Znth_overflow, Znth_app1; auto.
        destruct (eq_dec 0 (-1)); [discriminate|].
        destruct (eq_dec v' (-1)); [contradiction n; auto | reflexivity].
      * rewrite Znth_overflow, Znth_overflow with (al := h' ++ [v']); auto; [reflexivity|].
        rewrite Zlength_app, Zlength_cons, Zlength_nil; omega.
  - assert (Zlength (sublist 0 (Zlength h') (map (fun i : Z => if eq_dec (Znth i h' 0) (-1) then b0
      else Znth i lasts 0) (upto (Z.to_nat N)))) = Zlength h') as Hlenh.
    { rewrite Zlength_sublist; try omega.
      rewrite Zlength_map, Zlength_upto, Z2Nat.id; omega. }
    assert (Zlength (sublist 0 (Zlength h') (map (fun i : Z => if eq_dec (Znth i (h' ++ [v']) 0) (-1) then b0
      else Znth i lasts 0) (upto (Z.to_nat N)))) = Zlength h') as Hlenh'.
    { rewrite Zlength_sublist; try omega.
      rewrite Zlength_map, Zlength_upto, Z2Nat.id; omega. }
    simpl in *.
    destruct (eq_dec v' (-1)).
    + assert (EX sh : share, !! sepalg_list.list_join sh0 (make_shares shs (sublist 0 (Zlength h')
          (map (fun i : Z => if eq_dec (Znth i h' 0) (-1) then b0 else Znth i lasts 0) (upto (Z.to_nat N)))) b0)
          sh && (EX v1 : Z, data_at sh tbuffer (vint v1) (Znth b0 bufs Vundef)) =
        EX sh : share, !! sepalg_list.list_join sh0 (make_shares shs (sublist 0 (Zlength h' + 1)
          (map (fun i : Z => if eq_dec (Znth i (h' ++ [v']) 0) (-1) then b0 else Znth i lasts 0)
          (upto (Z.to_nat N)))) b0) sh && (EX v0 : Z, data_at sh tbuffer (vint v0) (Znth b0 bufs Vundef))).
      { erewrite sublist_split with (mid := Zlength h')(hi := Zlength h' + 1), sublist_len_1, Znth_map', Znth_upto;
          auto; rewrite ?Zlength_map, ?Zlength_upto, ?Z2Nat.id; try omega.
        rewrite Znth_app1; auto.
        subst; rewrite eq_dec_refl, make_shares_app; simpl.
        rewrite eq_dec_refl, app_nil_r.
        erewrite make_shares_ext; eauto; [omega|].
        rewrite Hlenh; intros; erewrite !Znth_sublist, Znth_map', Znth_map, !Znth_upto; auto;
          rewrite ?Zlength_upto; simpl; try (unfold N in *; omega).
        rewrite app_Znth1; [reflexivity | omega].
        { setoid_rewrite Hshs; rewrite Hlenh', Zlength_cons, Zlength_nil; omega. } }
      destruct (eq_dec lasti (-1)); subst l0; [rewrite upd_Znth_diff | rewrite 2upd_Znth_diff]; auto; try omega;
        erewrite Znth_map, Znth_upto; auto; destruct (eq_dec b0 b0); auto; absurd (b0 = b0); auto.
    + rewrite upd_Znth_same; [|omega].
      erewrite sublist_split with (mid := Zlength h')(hi := Zlength h' + 1), sublist_len_1, Znth_map', Znth_upto;
        auto; rewrite ?Zlength_map, ?Zlength_upto, ?Z2Nat.id; simpl; try (unfold N in *; omega).
      rewrite Znth_app1; auto.
      destruct (eq_dec v' (-1)); [contradiction n0; auto|].
      rewrite make_shares_app; simpl.
      destruct (eq_dec _ b0); [contradiction n; auto|].
      rewrite hd_Znth, Znth_sublist; rewrite ?Hlenh'; try setoid_rewrite Hshs; try omega.
      f_equal; extensionality; f_equal; f_equal.
      erewrite make_shares_ext.
      apply prop_ext; split.
      * intros (? & Hj1 & Hj2).
        apply sepalg.join_comm in Hj2; destruct (sepalg_list.list_join_assoc2 Hj1 Hj2) as (? & ? & ?).
        apply list_join_comm; econstructor; eauto.
        erewrite Znth_indep; eauto.
        setoid_rewrite Hshs; auto.
      * intro Hj; apply list_join_comm in Hj; inversion Hj as [|????? Hj1 Hj2]; subst.
        apply sepalg.join_comm in Hj1; destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (? & ? & ?).
        do 2 eexists; eauto.
        subst shi; erewrite Znth_indep; eauto.
        setoid_rewrite Hshs; auto.
      * omega.
      * rewrite Hlenh; intros; erewrite !Znth_sublist, Znth_map', Znth_map, !Znth_upto;
          rewrite ?Zlength_upto; simpl; try (unfold N in *; omega).
        rewrite app_Znth1; [reflexivity | omega].
      * rewrite Hlenh', Zlength_cons, Zlength_nil; setoid_rewrite Hshs; omega.
  - transitivity (Znth j l0 FF).
    { destruct (eq_dec v' (-1)); [|rewrite upd_Znth_diff; auto; omega].
      destruct (eq_dec lasti (-1)); [|rewrite upd_Znth_diff]; auto; omega. }
    subst l0.
    destruct (eq_dec j b).
    + subst; rewrite upd_Znth_same; auto.
      apply mpred_ext; intros ? HP.
      * exists bsh'; split; auto.
      * destruct HP as (x & HshP & ?).
        assert (x = bsh') by (eapply list_join_eq; eauto; apply HshP).
        subst; auto.
    + rewrite upd_Znth_diff; auto.
      erewrite Znth_map, Znth_upto; auto.
      destruct (eq_dec j b0); [contradiction n0; auto|].
      destruct (eq_dec j b); [contradiction n1; auto|].
      simpl; erewrite make_shares_ext; eauto.
      rewrite Zlength_map, Zlength_upto; intros.
      erewrite Znth_map', Znth_map, !Znth_upto; auto; try omega.
      destruct (zlt j0 (Zlength h')); [|destruct (eq_dec j0 (Zlength h'))].
      * rewrite app_Znth1; auto; omega.
      * subst; rewrite Znth_overflow, Znth_app1; auto.
        destruct (eq_dec 0 (-1)); [discriminate|].
        destruct (eq_dec v' (-1)); [|reflexivity].
        split; intro; subst; tauto.
      * rewrite Znth_overflow, Znth_overflow with (al := h' ++ [v']); auto; [reflexivity|].
        rewrite Zlength_app, Zlength_cons, Zlength_nil; omega.
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
            fold_right sepcon emp (map (fun r =>
              ghost_var gsh1 tint (vint (if zlt r i then b else b0)) (offset_val 1 (Znth r comms Vundef)) *
              ghost_var gsh1 tint (vint (Znth r lasts' (-1))) (offset_val 2 (Znth r comms Vundef))) (upto (Z.to_nat N))) *
            fold_right sepcon emp (map (fun a => EX sh : share,
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
    apply derives_refl'; f_equal; f_equal.
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
    match goal with H : if eq_dec b b then _ else _ |- _ => rewrite eq_dec_refl in H end.
    rewrite Hlens in *.
    match goal with H : sepalg_list.list_join _ (sublist i N shs) _ |- _ =>
      rewrite sublist_split with (mid := i + 1) in H; try omega;
      apply list_join_comm, sepalg_list.list_join_unapp in H; destruct H as (bsh' & ? & Hsh) end.
    rewrite sublist_len_1 with (d := Tsh), <- sepalg_list.list_join_1 in Hsh; [|omega].
    rewrite (extract_nth_sepcon (map _ (upto (Z.to_nat N))) i); [|rewrite Zlength_map; auto].
    erewrite !Znth_map; rewrite ?Znth_upto; rewrite ?Znth_upto, ?Zlength_upto; rewrite ?Z2Nat.id; auto; try omega.
    rewrite Znth_overflow with (al := h'); [|omega].
    destruct (eq_dec 0 (-1)); [discriminate|].
    destruct (zlt i i); [clear - l; omega|].
    forward_call (Tsh, lsh, gsh1, gsh2, lsh, Znth i comms Vundef, Znth i locks Vundef, -1, b, Znth i h [],
      fun (h : hist) (v : Z) => !!(v = b) &&
        ghost_var gsh1 tint (vint b0) (offset_val 1 (Znth i comms Vundef)) *
        ghost_var gsh1 tint (vint (Znth i lasts 0)) (offset_val 2 (Znth i comms Vundef)) *
        EX v : Z, data_at (Znth i shs Tsh) tbuffer (vint v) (Znth b bufs Vundef),
      comm_R bufs (Znth i shs Tsh) gsh2 (Znth i comms Vundef), fun (h : hist) (v : Z) => !!(-1 <= v < B) &&
        ghost_var gsh1 tint (vint b) (offset_val 1 (Znth i comms Vundef)) *
        ghost_var gsh1 tint (vint (if eq_dec v (-1) then b0 else Znth i lasts 0))
          (offset_val 2 (Znth i comms Vundef)) *
        if eq_dec v (-1) then if eq_dec (Znth i lasts 0) (-1) then emp
          else EX v : Z, data_at (Znth i shs Tsh) tbuffer (vint v) (Znth (Znth i lasts 0) bufs Vundef)
        else !!(v = b0) && EX v' : Z, data_at (Znth i shs Tsh) tbuffer (vint v') (Znth v bufs Vundef)).
    { unfold comm_inv.
      Intro v0; Exists v0.
      rewrite <- (data_at_share_join _ _ _ _ _ _ Hsh).
      (* entailer! is slow *)
      rewrite true_eq, TT_andp; auto; cancel.
      subst Frame; instantiate (1 := [_ * _ * _ * _ * _ * _ * _ * _ *
        (EX v0 : Z, data_at bsh' tbuffer (vint v0) (Znth b bufs Vundef)) * _]).
      rewrite <- sepcon_emp at 1; rewrite sepcon_comm; apply sepcon_derives; [|simpl; rewrite sepcon_emp;
        repeat (apply sepcon_derives; try apply derives_refl); Exists v0; auto].
      apply andp_right; auto.
      eapply derives_trans; [|apply precise_weak_precise]; auto.
      eapply derives_precise' with (Q := _ * data_at_ (Znth i shs Tsh) tbuffer (Znth b bufs Vundef));
        [apply sepcon_derives; [apply derives_refl|] | repeat apply precise_sepcon; auto].
      clear; entailer!. }
    { repeat (split; auto).
      { transitivity 0; try computable; omega. }
      { transitivity B; unfold B, N in *; try computable; omega. }
      unfold AE_spec, comm_R; intros.
      intros ???????? Ha.
      rewrite last_two_reads_cons, prev_taken_cons in Ha.
      rewrite !sepcon_andp_prop', !sepcon_andp_prop.
      erewrite extract_prop_in_SEP with (n := O); simpl; eauto.
      erewrite extract_prop_in_SEP with (n := O); simpl; eauto.
      Intros.
      destruct (eq_dec vc (-1)); [omega|].
      destruct (last_two_reads hx) as (b1, b2) eqn: Hlast.
      apply semax_pre with (P' := PROPx P (LOCALx Q (SEPx (
        (ghost_var gsh1 tint (vint b0) (offset_val 1 (Znth i comms Vundef)) *
         ghost_var gsh2 tint (vint (last_write hx)) (offset_val 1 (Znth i comms Vundef))) ::
        (ghost_var gsh1 tint (vint (Znth i lasts 0)) (offset_val 2 (Znth i comms Vundef)) *
         ghost_var gsh2 tint (vint (prev_taken hx)) (offset_val 2 (Znth i comms Vundef))) ::
        (ghost_var gsh2 tint (vint b1) (Znth i comms Vundef) *
         (if eq_dec vx (-1) then if eq_dec b2 (-1) then emp
          else EX v1 : Z, @data_at CompSpecs (Znth i shs Tsh) tbuffer (vint v1) (Znth b2 bufs Vundef)
          else EX v1 : Z, @data_at CompSpecs (Znth i shs Tsh) tbuffer (vint v1) (Znth vx bufs Vundef)) *
         (EX v1 : Z, @data_at CompSpecs (Znth i shs Tsh) tbuffer (vint v1) (Znth b bufs Vundef))) :: R)))).
      { go_lowerx; cancel. }
      assert_PROP (b0 = last_write hx).
      { go_lowerx; apply sepcon_derives_prop.
        eapply derives_trans; [apply ghost_var_inj|].
        apply prop_left; intro; apply prop_right.
        apply repr_inj_signed; try congruence.
        + apply repable_buf; omega.
        + unfold last_write.
          destruct (find_write hx) as [(?, ?)|] eqn: Hfind; [|split; computable].
          apply find_write_In in Hfind; destruct Hfind as (? & Hin).
          match goal with H : Forall _ _ |- _ => rewrite Forall_forall in H; specialize (H _ Hin) end.
          simpl in *; apply repable_buf; tauto. }
      assert_PROP (prev_taken hx = Znth i lasts 0) as Hprev.
      { go_lowerx.
        rewrite <- sepcon_assoc, (sepcon_comm (_ * _) (_ * ghost_var _ _ _ _)).
        do 2 apply sepcon_derives_prop.
        eapply derives_trans; [apply ghost_var_inj|].
        apply prop_left; intro; apply prop_right.
        apply repr_inj_signed; try congruence.
        + destruct (prev_taken_In hx) as [Hin | [Hin | Hin]]; try (rewrite Hin; split; computable).
          match goal with H : Forall _ _ |- _ => rewrite Forall_forall in H; specialize (H _ Hin) end.
          simpl in *; apply repable_buf; omega.
        + apply Forall_Znth; [omega|].
          eapply Forall_impl; [|eauto]; intros.
          apply repable_buf; auto. }
      subst; rewrite <- Hprev in *.
      erewrite !ghost_var_share_join; eauto.
      apply change_ghost_var with (v' := vint b).
      rewrite <- flatten_sepcon_in_SEP, sepcon_comm, flatten_sepcon_in_SEP.
      apply change_ghost_var with (v' := vint (if eq_dec vx (-1) then last_write hx else prev_taken hx)).
      rewrite <- !(ghost_var_share_join _ _ _ _ _ _ SH3).
      eapply semax_pre, Ha.
      go_lowerx.
      rewrite !sepcon_andp_prop', !sepcon_andp_prop, !sepcon_andp_prop'.
      apply andp_right; [apply prop_right; repeat split; try constructor; auto; omega|].
      apply andp_right; [apply prop_right; auto|].
      erewrite take_read, Hlast; eauto; simpl.
      unfold last_write in *; simpl in *.
      destruct (eq_dec vx (-1)); subst; cancel.
      + destruct (eq_dec b (-1)); [contradiction n1; auto | cancel].
        rewrite <- sepcon_emp at 1; apply sepcon_derives.
        destruct (find_write hx) as [(?, ?)|] eqn: Hwrite.
        * exploit find_write_read; eauto; intros (? & Hread); rewrite Hread; auto.
        * eapply find_read_write in Hwrite; eauto.
          rewrite Hwrite; auto.
        * apply andp_right; auto.
          eapply derives_trans; [|apply precise_weak_precise]; auto.
          apply precise_andp2; repeat apply precise_sepcon; auto.
          apply derives_precise' with
            (Q := @data_at_ CompSpecs (Znth (Zlength h') shs Tsh) tbuffer (Znth b bufs Vundef)); auto.
          clear; entailer!.
      + assert (exists rest, find_write hx = Some (vx, rest)) as (? & Hwrite).
        { destruct hx; simpl in *.
          { match goal with H : Some (-1) = Some vx |- _ => inv H; contradiction n2; auto end. }
          destruct h0.
          destruct (apply_hist (-1) hx) eqn: Hh'; [|discriminate].
          destruct (eq_dec z r); [match goal with H : Some _ = Some vx |- _ => inv H end | discriminate].
          destruct(eq_dec vx (-1)); [contradiction n2; auto | eauto]. }
        rewrite Hwrite in *.
        destruct (eq_dec b (-1)); [contradiction n1; auto|].
        rewrite !sepcon_andp_prop; apply andp_right; [apply prop_right; auto | cancel].
        rewrite <- sepcon_emp at 1; apply sepcon_derives.
        * unfold last_two_reads in Hlast; rewrite find_read0 in Hlast.
          destruct (find_read hx) as [(?, ?)|]; [|inv Hlast; auto].
          destruct (find_read (l ++ [AE 0 (-1)])) as [(?, ?)|]; inv Hlast; auto.
        * apply andp_right; auto.
          eapply derives_trans; [|apply precise_weak_precise]; auto.
          apply precise_andp2; repeat apply precise_sepcon; auto.
          apply derives_precise' with
            (Q := @data_at_ CompSpecs (Znth (Zlength h') shs Tsh) tbuffer (Znth b bufs Vundef)); auto.
          clear; entailer!. }
    Intros v'.
    gather_SEP 0 9; replace_SEP 0 (fold_right sepcon emp (map (fun r =>
      lock_inv lsh (Znth r locks Vundef) (AE_inv (Znth r comms Vundef) (-1) Tsh gsh2
        (comm_R bufs (Znth r shs Tsh) gsh2 (Znth r comms Vundef)))) (upto (Z.to_nat N)))).
    { go_lowerx.
      rewrite (extract_nth_sepcon (map _ (upto _)) i);
        [cancel | rewrite Zlength_map, Zlength_upto; unfold N in *; auto].
      rewrite Znth_map with (d' := N), Znth_upto; rewrite ?Zlength_upto; unfold N in *; simpl; auto; omega. }
    gather_SEP 1 9; replace_SEP 0 (fold_right sepcon emp (map (fun x => let '(c, h0) := x in
      ghost gsh1 (-1) (lsh, h0) c) (combine comms (extend (map (fun v1 : Z => AE v1 b) (h' ++ [v'])) h)))).
    { go_lowerx.
      rewrite (extract_nth_sepcon (map _ (combine _ _)) i);
        [|rewrite Zlength_map, Zlength_combine, Zlength_extend, Z.min_l; omega].
      assert (Zlength comms = Zlength (extend (map (fun v0 => AE v0 b) (h' ++ [v'])) h)).
      { rewrite Zlength_extend; omega. }
      assert (Zlength (combine comms (extend (map (fun v => AE v b) (h' ++ [v'])) h)) = N) as Hlens'.
      { rewrite Zlength_combine, Z.min_l; auto; omega. }
      rewrite <- Hlens' in *.
      rewrite Znth_map with (d' := (Vundef, [])), Znth_combine; auto.
      erewrite Znth_extend_in; rewrite ?Zlength_map, ?Zlength_app, ?Zlength_cons, ?Zlength_nil; try omega.
      rewrite Znth_map'.
      instantiate (1 := 0).
      subst; rewrite app_Znth2, Zminus_diag, Znth_0_cons; [cancel | omega].
      apply derives_refl'; f_equal.
      unfold upd_Znth; f_equal; rewrite !sublist_map, !sublist_combine, !sublist_extend.
      + rewrite map_app, sublist_app1; rewrite ?Zlength_map; auto; omega.
      + rewrite !Zlength_map, !Hlens, !Hlens'.
        rewrite !sublist_over with (l := map _ _); auto;
          rewrite Zlength_map, ?Zlength_app, ?Zlength_cons, ?Zlength_nil; omega. }
    gather_SEP 2 3 10; replace_SEP 0 (fold_right sepcon emp (map (fun r =>
      ghost_var gsh1 tint (vint (if zlt r (i + 1) then b else b0)) (offset_val 1 (Znth r comms Vundef)) *
      ghost_var gsh1 tint (vint (Znth r (map (fun i0 => if eq_dec (Znth i0 (h' ++ [v']) 0) (-1) then b0
        else Znth i0 lasts 0) (upto (Z.to_nat N))) (-1))) (offset_val 2 (Znth r comms Vundef))) 
      (upto (Z.to_nat N)))).
    { go_lowerx.
      rewrite (extract_nth_sepcon (map _ (upto (Z.to_nat N))) i);
        [|rewrite Zlength_map, Zlength_upto; auto].
      erewrite Znth_map, Znth_upto, Znth_map, Znth_upto; rewrite ?Zlength_upto, ?Z2Nat.id; simpl; auto;
        try (unfold N in *; auto; omega).
      destruct (zlt i (i + 1)); [|clear - g0; omega].
      subst; rewrite app_Znth2, Zminus_diag, Znth_0_cons; [cancel | omega].
      apply derives_refl'; f_equal.
      unfold upd_Znth; f_equal; rewrite !sublist_map.
      + apply map_ext_in; intros ? Hin.
        apply In_sublist_upto in Hin; try omega.
        clear - Hin; destruct Hin as ((? & ?) & ?).
        erewrite !Znth_map, !Znth_upto; rewrite ?Zlength_upto; try (split; auto; omega).
        destruct (zlt a (Zlength h')); [|omega].
        destruct (zlt a (Zlength h' + 1)); [|omega].
        rewrite app_Znth1; auto.
      + f_equal; apply map_ext_in; intros ? Hin.
        apply In_sublist_upto in Hin; try omega.
        rewrite Zlength_map, Zlength_upto in Hin.
        destruct Hin as ((? & ?) & _).
        erewrite !Znth_map, !Znth_upto; rewrite ?Zlength_upto; try (split; auto; omega).
        destruct (zlt a (Zlength h')); [omega|].
        destruct (zlt a (Zlength h' + 1)); [omega|].
        rewrite Znth_overflow with (al := h'), Znth_overflow with (al := h' ++ [v']);
          rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; auto. }
    assert (repable_signed v').
    { split; [transitivity (-1) | transitivity B]; unfold B, N in *; try computable; omega. }
    match goal with |- semax _ (PROP () (LOCALx ?Q (SEPx (?p0 :: ?p1 :: ?p2 :: ?p3 :: ?p4 :: ?p5 :: ?p6 :: ?p7 ::
      data_at _ _ ?l last_taken :: ?R2)))) _ _ =>
      forward_if (PROP () (LOCALx Q (SEPx (p0 :: p1 :: p2 :: p3 :: p4 :: p5 :: p6 :: p7 ::
        data_at Ews (tarray tint N) (upd_Znth i l (vint (if eq_dec v' (-1) then b0 else Znth i lasts 0))) last_taken :: R2)))) end.
    + forward.
      match goal with H : Int.repr v' = _ |- _ => rewrite Int.neg_repr in H; apply repr_inj_signed in H end; subst;
        auto; [|split; try computable].
      destruct (eq_dec (- (1)) (-1)); [|contradiction n1; auto].
      apply drop_tc_environ.
    + forward.
      destruct (eq_dec v' (-1)); [subst; absurd (Int.repr (-1) = Int.neg (Int.repr 1)); auto|].
      erewrite upd_Znth_triv with (i0 := i).
      apply drop_tc_environ.
      * rewrite !Zlength_map, Zlength_upto; auto.
      * rewrite !Znth_map', Znth_upto; [|simpl; unfold N in *; omega].
        rewrite Znth_overflow; [|omega].
        destruct (eq_dec 0 (-1)); [discriminate | auto].
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
      rewrite (sepcon_comm _ (data_at _ _ _ last_taken)), !sepcon_assoc; apply sepcon_derives.
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
      * eapply upd_write_shares; eauto.
  - forward.
    forward.
    forward.
    rewrite sublist_nil, sublist_same; rewrite ?Zlength_map; auto.
    Exists (map (fun i => if eq_dec (Znth i h' 0) (-1) then b0 else Znth i lasts 0) (upto (Z.to_nat N)))
      (extend (map (fun v => AE v b) h') h); entailer!.
    + repeat split.
      * rewrite Forall_map, Forall_forall; intros; simpl.
        destruct (eq_dec (Znth x h' 0) (-1)); [omega|].
        rewrite In_upto, Z2Nat.id in *; unfold N; try omega.
        apply Forall_Znth; [omega | auto].
      * assert (Zlength h' = Zlength h) as Hlen by omega; clear - Hlen; revert dependent h; induction h';
          destruct h; rewrite ?Zlength_nil, ?Zlength_cons in *; simpl; intros; auto; try omega.
        { rewrite Zlength_correct in *; omega. }
        constructor; eauto.
        apply IHh'; omega.
      * rewrite in_map_iff; intros (i & ? & ?); subst.
        rewrite In_upto, Z2Nat.id in *; try (unfold N; omega).
        destruct (eq_dec (Znth i h' 0) (-1)); [absurd (b0 = b0); auto|].
        match goal with H : ~In _ lasts |- _ => contradiction H; apply Znth_In; omega end.
    + apply derives_refl'; f_equal; f_equal.
      apply map_ext; intro.
      f_equal; extensionality; f_equal; f_equal; apply prop_ext.
      destruct (eq_dec a b).
      * destruct (eq_dec a b0); [absurd (b = b0); subst; auto|].
        split; intro Hx; [inv Hx; auto | subst; constructor].
      * destruct (eq_dec a b0); reflexivity.
Qed.

Lemma body_reader : semax_body Vprog Gprog f_reader reader_spec.
Proof.
  start_function.
  
Admitted.

Lemma body_writer : semax_body Vprog Gprog f_writer writer_spec.
Proof.
  start_function.
Admitted.