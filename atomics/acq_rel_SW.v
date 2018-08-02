Require Import VST.veric.rmaps.
Require Import VST.veric.compcert_rmaps.
Require Import VST.progs.conclib.
Require Import VST.progs.ghosts.
Require Import VST.floyd.library.
Require Import VST.floyd.sublist.
Require Import atomics.general_atomics.
Require Import atomics.acq_rel_atomics.

Set Bullet Behavior "Strict Subproofs".

Section atomics.

Context {CS : compspecs}.

Section protocols.

Context {state : Type}.

Parameter protocol_piece : share -> val -> state -> (state -> state -> Prop) ->
  ((state -> Z -> mpred) * (state -> Z -> mpred)) -> mpred.

Definition protocol_R := protocol_piece Share.bot.
Definition protocol_W := protocol_piece gsh2.

Context (ord : state -> state -> Prop) `{RelationClasses.PreOrder _ ord}
  (Tread Tfull : state -> Z -> mpred).

Axiom protocol_piece_nonexpansive : forall sh l s ord Tread1 Tfull1 Tread2 Tfull2,
  (ALL s : state, ALL v : Z, (Tread1 s v <=> Tread2 s v) && (Tfull1 s v <=> Tfull2 s v)) |--
  protocol_piece sh l s ord (Tread1, Tfull1) <=> protocol_piece sh l s ord (Tread2, Tfull2).

Lemma protocol_piece_super_non_expansive : forall n sh l s ord Tread Tfull,
  approx n (protocol_piece sh l s ord (Tread, Tfull)) =
  approx n (protocol_piece sh l s ord (fun s v => approx n (Tread s v), fun s v => approx n (Tfull s v))).
Proof.
  intros.
  apply approx_eq_i'.
  intros m ?.
  apply protocol_piece_nonexpansive.
  intros ??; split; apply fash_equiv_approx; auto.
Qed.

Notation T := (Tread, Tfull).

Axiom make_protocol_R : forall sh l s,
  protocol_piece sh l s ord T |-- |==> protocol_piece sh l s ord T * protocol_R l s ord T.

Corollary protocol_R_duplicable : forall l s, duplicable (protocol_R l s ord T).
Proof.
  intros; apply make_protocol_R.
Qed.

Corollary protocol_W_R : forall l s,
  protocol_W l s ord T |-- |==> protocol_W l s ord T * protocol_R l s ord T.
Proof.
  intros; apply make_protocol_R.
Qed.

Axiom protocol_R_absorb : forall sh l s s', sh <> Share.bot ->
  protocol_piece sh l s ord T * protocol_R l s' ord T |-- |==> !!(ord s' s) && protocol_piece sh l s ord T.

Corollary protocol_R_W : forall l s s',
  protocol_W l s ord T * protocol_R l s' ord T |-- |==> !!(ord s' s) && protocol_W l s ord T.
Proof.
  intros; apply protocol_R_absorb; auto.
Qed.

Axiom protocol_R_join' : forall l s1 s2,
  protocol_R l s1 ord T * protocol_R l s2 ord T |--
  EX s : _, !!(ord s1 s /\ ord s2 s) && protocol_R l s ord T.

Axiom make_protocol : forall {P : protocol Tread Tfull} l v s, repable_signed v ->
  data_at Tsh tint (vint v) l * |> Tfull s v |-- |==> protocol_W l s ord T.

Axiom protocol_piece_share_join : forall sh1 sh2 sh l s1 s2 (Hsh : sepalg.join sh1 sh2 sh)
  (Hsh1 : sh1 <> Share.bot) (Hsh2 : sh2 <> Share.bot),
  protocol_piece sh1 l s1 ord T * protocol_piece sh2 l s2 ord T =
  !!(s1 = s2) && protocol_piece sh l s1 ord T.

Axiom protocol_later : forall sh l s,
  protocol_piece sh l s ord (|>Tread, |>Tfull) |-- |>protocol_piece sh l s ord T.

Axiom protocol_delay : forall sh l s,
  protocol_piece sh l s ord T |-- protocol_piece sh l s ord (|>Tread, |>Tfull).

End protocols.

Definition OrdType s := ArrowType s (ArrowType s (ConstType Prop)).
Definition PredType s := ArrowType s (ArrowType (ConstType Z) Mpred).

Program Definition load_acq_spec := TYPE LA_type
  WITH l : val, s : _, st_ord : _ -> _ -> Prop, T : ((_ -> Z -> mpred) * (_ -> Z -> mpred)),
       P : mpred, E : _, Q : _ -> Z -> mpred
  PRE [ 1%positive OF tptr tint ]
   PROP ()
   LOCAL (temp 1%positive l)
   SEP (ALL s' : _, !!(st_ord s s') --> ALL v : _,
          weak_fview_shift E E (fst T s' v * P * protocol_R l s' st_ord T) (Q s' v) && emp;
        P; protocol_R l s st_ord T)
  POST [ tint ]
   EX v : Z, EX s' : _,
   PROP (repable_signed v; st_ord s s')
   LOCAL (temp ret_temp (vint v))
   SEP (Q s' v).
Next Obligation.
Proof.
  repeat intro.
  destruct x as ((((((?, s), ?), (?, ?)), P), ?), Q); simpl.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; f_equal;
    f_equal; rewrite !sepcon_emp, ?approx_sepcon, ?approx_idem.
  unfold protocol_R; rewrite protocol_piece_super_non_expansive; f_equal.
  rewrite !approx_allp by auto; f_equal; extensionality.
  setoid_rewrite approx_imp; f_equal; f_equal.
  rewrite !(approx_allp _ _ _ 0); f_equal; extensionality.
  rewrite !approx_andp; f_equal.
  rewrite fview_shift_nonexpansive.
  setoid_rewrite fview_shift_nonexpansive at 2.
  rewrite !approx_sepcon, !approx_idem, protocol_piece_super_non_expansive; auto.
Qed.
Next Obligation.
Proof.
  repeat intro.
  destruct x as ((((((?, ?), ?), ?), ?), ?), ?); simpl.
  rewrite !approx_exp; apply f_equal; extensionality.
  rewrite !approx_exp; apply f_equal; extensionality.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 apply f_equal;
    rewrite !sepcon_emp, ?approx_sepcon, ?approx_idem; auto.
Qed.

Program Definition store_rel_spec := TYPE SR_type
  WITH l : val, v : Z, s : _, s'' : _, st_ord : _ -> _ -> Prop, T : ((_ -> Z -> mpred) * (_ -> Z -> mpred)),
       P : mpred, E : _, Q : mpred
  PRE [ 1%positive OF tptr tint, 2%positive OF tint ]
   PROP (repable_signed v; st_ord s s'')
   LOCAL (temp 1%positive l; temp 2%positive (vint v))
   SEP (ALL v0 : Z, weak_fview_shift E E
          (P * snd T s v0 * protocol_W l s'' st_ord T) (Q * |> snd T s'' v) && emp;
        P; protocol_W l s st_ord T)
  POST [ tvoid ]
   PROP ()
   LOCAL ()
   SEP (protocol_W l s'' st_ord T; Q).
Next Obligation.
Proof.
  repeat intro.
  destruct x as ((((((((?, ?), ?), ?), ?), (?, ?)), ?), ?), ?); simpl.
  unfold PROPx; simpl; rewrite !approx_andp; f_equal.
  unfold LOCALx; simpl; rewrite !approx_andp; apply f_equal.
  unfold SEPx; simpl; rewrite !sepcon_emp, !approx_sepcon, !approx_idem.
  unfold protocol_W; rewrite protocol_piece_super_non_expansive; f_equal.
  rewrite !approx_allp by auto; f_equal; extensionality.
  rewrite !approx_andp; f_equal.
  rewrite fview_shift_nonexpansive.
  setoid_rewrite fview_shift_nonexpansive at 2.
  rewrite !approx_sepcon, !approx_idem, protocol_piece_super_non_expansive; f_equal; f_equal; f_equal.
  destruct n; [rewrite !approx_0; auto|].
  setoid_rewrite approx_later.
  etransitivity; [rewrite <- approx_oo_approx' with (n' := S n)|]; auto.
Qed.
Next Obligation.
Proof.
  repeat intro.
  destruct x as ((((((((?, ?), ?), ?), ?), (?, ?)), ?), ?), ?); simpl.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 apply f_equal;
    rewrite !sepcon_emp, ?approx_sepcon, ?approx_idem.
  unfold protocol_W; rewrite protocol_piece_super_non_expansive; auto.
Qed.

(* There's no need for a CAS because anyone with write permission knows the current value already. *)

End atomics.

(*(* Witnesses for common use cases *)
(* simple load_acq with read assertion *)
Definition load_acq_witness {state} l (s : state) st_ord T P Q := (l, s, st_ord, T, protocol_R l s st_ord T * P,
  fun _ : Z => FF, @nil Z, P, fun s' (v' : Z) => protocol_R l s' st_ord T * Q s' v').

(* simple load_acq with write assertion *)
Definition load_acq_W_witness {state} l (s : state) st_ord T P Q := (l, s, st_ord, T, protocol_W l s st_ord T * P,
  fun _ : Z => FF, @nil Z, protocol_W l s st_ord T * P,
  fun s' (v' : Z) => !!(s' = s) && protocol_W l s st_ord T * Q s' v').

(* simple store_rel recovering write assertion *)
Definition store_rel_witness {state} l (v : Z) (s s'' : state) st_ord T P Q := (l, v, s, s'', st_ord, T,
  protocol_W l s st_ord T * P, fun _ : Z => FF, @nil Z, P, protocol_W l s'' st_ord T * Q).*)
