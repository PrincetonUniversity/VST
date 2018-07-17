Require Import VST.veric.juicy_extspec. (* We should probably move has_ext into Separation Logic.v *)
Require Import VST.progs.ghosts.
Require Import VST.progs.io.
Require Import VST.floyd.proofauto.
Require Import DeepWeb.Free.Monad.Free.
Import MonadNotations.
Require Import DeepWeb.Free.Monad.Common.
Require Import DeepWeb.Free.Monad.Verif.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Inductive IO_event : Type -> Type :=
| ERead : IO_event int
| EWrite (c : int) : IO_event unit.

Definition read : M IO_event int := embed ERead.

Definition write (c : int) : M IO_event unit := embed (EWrite c).

Definition IO_itree := M IO_event unit.

(* We need a layer of equivalence to allow us to use the monad laws. *)
Definition ITREE (tr : IO_itree) := EX tr' : _, !!(EquivUpToTau tr tr') &&
  has_ext tr'.

Definition putchar_spec :=
 DECLARE _putchar
  WITH c : int, k : IO_itree
  PRE [ _c OF tint ]
    PROP ()
    LOCAL (temp _c (Vint c))
    SEP (ITREE (write c ;; k))
  POST [ tint ]
    PROP ()
    LOCAL (temp ret_temp (Vint c))
    SEP (ITREE k).

Definition getchar_spec :=
 DECLARE _getchar
  WITH k : int -> IO_itree
  PRE [ ]
    PROP ()
    LOCAL ()
    SEP (ITREE (r <- read ;; k r))
  POST [ tint ]
   EX i : int,
    PROP (- two_p 7 <= Int.signed i <= two_p 7 - 1)
    LOCAL (temp ret_temp (Vint i))
    SEP (ITREE (k i)).

Fixpoint write_list l : IO_itree :=
  match l with
  | nil => Ret tt
  | c :: rest => write c ;; write_list rest
  end.

Definition char0 : Z := 48.

Program Fixpoint chars_of_nat n { measure n } : list int :=
  match (n / 10)%nat with
  | O => [Int.repr (Z.of_nat n + char0)]
  | n' => chars_of_nat n' ++ [Int.repr (Z.of_nat (n mod 10) + char0)]
  end.
Next Obligation.
Proof.
  apply (Nat.div_lt n 10); try omega.
  destruct n; [contradiction | omega].
Defined.

Definition chars_of_Z z := chars_of_nat (Z.to_nat z).

(* The function computed by print_intr *)
Program Fixpoint intr n { measure n } : list int :=
  match n with
  | O => []
  | _ => intr (n / 10) ++ [Int.repr (Z.of_nat (n mod 10) + char0)]
  end.
Next Obligation.
Proof.
  apply (Nat.div_lt n 10); try omega.
Defined.

Definition print_intr_spec :=
 DECLARE _print_intr
  WITH i : Z, tr : IO_itree
  PRE [ _i OF tuint ]
    PROP (0 <= i <= Int.max_unsigned)
    LOCAL (temp _i (Vint (Int.repr i)))
    SEP (ITREE (write_list (intr (Z.to_nat i)) ;; tr))
  POST [ tvoid ]
    PROP ()
    LOCAL ()
    SEP (ITREE tr).

Definition print_int_spec :=
 DECLARE _print_int
  WITH i : Z, tr : IO_itree
  PRE [ _i OF tuint ]
    PROP (0 <= i <= Int.max_unsigned)
    LOCAL (temp _i (Vint (Int.repr i)))
    SEP (ITREE (write_list (chars_of_Z i) ;; tr))
  POST [ tvoid ]
    PROP ()
    LOCAL ()
    SEP (ITREE tr).

Definition newline := 10.

CoFixpoint read_sum n : IO_itree :=
  write_list (chars_of_Z n);; write (Int.repr newline);;
  c <- read;; read_sum (n + (Int.unsigned c - char0)).

Definition main_itree := c <- read;; read_sum (Int.unsigned c - char0).

(* Note nonstandard main_spec; in general, we probably want floyd to support
   a version of main_pre with a starting has_ext assertion. *)
Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] PROP () LOCAL () SEP (ITREE main_itree)
  POST [ tint ] PROP () LOCAL () SEP (TT).

Definition Gprog : funspecs := ltac:(with_library prog [putchar_spec; getchar_spec;
  print_intr_spec; print_int_spec; main_spec]).

Lemma ITREE_impl : forall tr tr', EquivUpToTau tr tr' ->
  ITREE tr |-- ITREE tr'.
Proof.
  intros.
  unfold ITREE.
  Intros tr1; Exists tr1; entailer!.
  etransitivity; eauto.
  symmetry; auto.
Qed.

Lemma ITREE_ext : forall tr tr', EquivUpToTau tr tr' ->
  ITREE tr = ITREE tr'.
Proof.
  intros; apply pred_ext; apply ITREE_impl; auto.
  symmetry; auto.
Qed.

Lemma divu_repr : forall x y,
  0 <= x <= Int.max_unsigned -> 0 <= y <= Int.max_unsigned ->
  Int.divu (Int.repr x) (Int.repr y) = Int.repr (x / y).
Proof.
  intros; unfold Int.divu.
  rewrite !Int.unsigned_repr; auto.
Qed.

Opaque bind.

Lemma write_list_app : forall l1 l2,
  EquivUpToTau (write_list (l1 ++ l2)) (write_list l1;; write_list l2).
Proof.
  induction l1; simpl; intros.
  - symmetry; apply leftId.
  - rewrite <- bindAssoc.
    Transparent bind.
    simpl.
    apply cong_bind; [reflexivity|].
    intro; apply IHl1.
Qed.

Opaque Nat.div Nat.modulo.

Lemma intr_eq : forall n, intr n =
  match n with
  | O => []
  | _ => intr (n / 10) ++ [Int.repr (Z.of_nat (n mod 10) + char0)]
  end.
Proof.
  intros.
  unfold intr at 1.
  rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold intr.
  destruct n; reflexivity.
Qed.

Lemma body_print_intr: semax_body Vprog Gprog f_print_intr print_intr_spec.
Proof.
  start_function.
  forward_if (PROP () LOCAL () SEP (ITREE tr)).
  - forward.
    forward.
    rewrite modu_repr, divu_repr by (omega || computable).
    rewrite intr_eq.
    destruct (Z.to_nat i) eqn: Hi.
    { apply Z2Nat_inj_0 in Hi; omega. }
    rewrite <- Hi, mod_Zmod, Z2Nat.id by omega; simpl; clear dependent n.
    erewrite ITREE_ext
      by (apply cong_bind with (k' := fun _ => tr); [apply write_list_app | reflexivity]).
    change (bindM _ _) with ((write_list (intr (Z.to_nat i / 10));; write_list [Int.repr (i mod 10 + char0)]);; tr).
    erewrite ITREE_ext by (symmetry; apply bindAssoc).
    forward_call (i / 10, write_list [Int.repr (i mod 10 + char0)];; tr).
    { replace (Z.to_nat i / 10)%nat with (Z.to_nat (i / 10)); [cancel|].
      rewrite <- (Z2Nat.id i) at 1 by omega.
      rewrite <- (div_Zdiv _ 10) by omega.
      rewrite Nat2Z.id; auto. }
    { split; [apply Z.div_pos; omega | apply Z.div_le_upper_bound; omega]. }
    forward_call (Int.repr (i mod 10 + char0), tr).
    { rewrite <- sepcon_emp at 1; apply sepcon_derives; [|cancel].
      erewrite ITREE_ext; [apply derives_refl|].
      unfold write_list.
      apply cong_bind; [|reflexivity].
      simpl.
      replace (fun _ => Ret tt) with (fun x : unit => Ret(Event := IO_event) x)
        by (extensionality x; destruct x; auto).
      apply (rightId(s := write (Int.repr (i mod 10 + char0)))). }
    entailer!.
  - forward.
    subst; entailer!.
    erewrite ITREE_ext; [apply derives_refl|].
    apply (leftId tt (fun _ => tr)).
  - forward.
Qed.

Lemma chars_of_nat_eq : forall n, chars_of_nat n =
  match (n / 10)%nat with
  | O => [Int.repr (Z.of_nat n + char0)]
  | n' => chars_of_nat n' ++ [Int.repr (Z.of_nat (n mod 10) + char0)]
  end.
Proof.
  intros.
  unfold chars_of_nat at 1.
  rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold chars_of_nat.
  destruct (n / 10)%nat; reflexivity.
Qed.

Lemma chars_of_nat_intr : forall n, (0 < n)%nat ->
  chars_of_nat n = intr n.
Proof.
  induction n using (well_founded_induction lt_wf); intro.
  rewrite chars_of_nat_eq, intr_eq.
  destruct n; [omega|].
  forget (S n) as m.
  destruct (_ / _)%nat eqn: Hdiv.
  - rewrite mod_Zmod by omega; simpl.
    rewrite Zmod_small; auto.
    split; try omega.
    apply Z2Nat.inj_lt; try omega.
    rewrite Nat2Z.id; simpl.
    destruct (lt_dec m 10); auto.
    exploit (Nat.div_str_pos m 10); omega.
  - rewrite H; auto; try omega.
    rewrite <- Hdiv; apply Nat.div_lt; auto; omega.
Qed.

Lemma body_print_int: semax_body Vprog Gprog f_print_int print_int_spec.
Proof.
  start_function.
  forward_if (PROP () LOCAL () SEP (ITREE tr)).
  - subst.
    forward_call (Int.repr char0, tr).
    { unfold chars_of_Z; rewrite chars_of_nat_eq.
      change (_ / _)%nat with O; simpl.
      erewrite <- sepcon_emp at 1; apply sepcon_derives; [|cancel].
      erewrite ITREE_ext; [apply derives_refl|].
      apply cong_bind; [|reflexivity].
      replace (fun _ => Ret tt) with (fun x : unit => Ret(Event := IO_event) x)
        by (extensionality x; destruct x; auto).
      apply (rightId(s := write (Int.repr char0))). }
    entailer!.
  - forward_call (i, tr).
    { unfold chars_of_Z.
      rewrite chars_of_nat_intr; [cancel|].
      destruct (Z.to_nat i) eqn: Hi; [|omega].
      apply Z2Nat_inj_0 in Hi; omega. }
    entailer!.
  - forward.
Qed.

Opaque bind.

Lemma read_sum_eq : forall n, read_sum n =
  (write_list (chars_of_Z n);; write (Int.repr newline);;
   c <- read;; read_sum (n + (Int.unsigned c - char0))).
Proof.
  intro.
  rewrite matchM; simpl.
  rewrite <- matchM; auto.
Qed.

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  forward.
  unfold main_itree.
  rewrite <- !seq_assoc. (* Without this, forward_call gives a type error! *)
  forward_call (fun c => read_sum (Int.unsigned c - char0)).
  Intros c.
  forward.
  rewrite sign_ext_inrange by auto.
  set (Inv := EX n : Z, EX c : int,
    PROP (0 <= n < 1009)
    LOCAL (temp _c (Vint c); temp _n (Vint (Int.repr n)))
    SEP (ITREE (read_sum (n + (Int.unsigned c - char0))))).
  unfold Swhile; forward_loop Inv break: Inv.
  { Exists 0 c; entailer!.
    apply derives_refl. }
  subst Inv.
  clear dependent c; Intros n c.
  forward_if.
  forward.
  forward_if.
  { forward.
    Exists n c; entailer!. }
  forward.
  rewrite read_sum_eq.
  rewrite <- (Int.repr_unsigned c) in H1.
  rewrite sub_repr in H1.
  pose proof (Int.unsigned_range c).
  destruct (zlt (Int.unsigned c) char0).
  { rewrite Int.unsigned_repr_eq in H1.
    rewrite <- Z_mod_plus_full with (b := 1), Zmod_small in H1; unfold char0 in *; rep_omega. }
  rewrite Int.unsigned_repr in H1 by (unfold char0 in *; rep_omega).
  forward_call (n + (Int.unsigned c - char0),
    write (Int.repr newline);; c' <- read;; read_sum (n + (Int.unsigned c - char0) + (Int.unsigned c' - char0))).
  { entailer!.
    rewrite <- (Int.repr_unsigned c) at 1.
    rewrite sub_repr, add_repr; auto. }
  { unfold char0 in *; rep_omega. }
  forward_call (Int.repr newline, c' <- read;; read_sum (n + (Int.unsigned c - char0) + (Int.unsigned c' - char0))).
  forward_call (fun c' => read_sum (n + (Int.unsigned c - char0) + (Int.unsigned c' - char0))).
  Intros c'.
  forward.
  rewrite sign_ext_inrange by auto.
  Exists (n + (Int.unsigned c - char0)) c'; entailer!.
  split; [unfold char0 in *; omega|].
  rewrite <- (Int.repr_unsigned c) at 2; rewrite sub_repr, add_repr; auto.
  { forward.
    Exists n c; entailer!. }
  subst Inv.
  Intros n c'.
  forward.
Qed.
