Require Import VST.progs.io.
Require Import VST.progs.io_specs.
Require Import VST.floyd.proofauto.
Require Import DeepWeb.Free.Monad.Free.
Import MonadNotations.
Require Import DeepWeb.Free.Monad.Common.
Require Import DeepWeb.Free.Monad.Verif.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition putchar_spec := DECLARE _putchar putchar_spec.
Definition getchar_spec := DECLARE _getchar getchar_spec.

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

CoFixpoint read_sum n d : IO_itree :=
  if zlt n 1000 then if zlt d 10 then
    write_list (chars_of_Z (n + d));; write (Int.repr newline);;
    c <- read;; read_sum (n + d) (Int.unsigned c - char0)
  else ret tt else ret tt.

Definition main_itree := c <- read;; read_sum 0 (Int.unsigned c - char0).

Definition ext_link := ext_link_prog prog.

Instance IO_Espec : OracleKind := Build_OracleKind _ (IO_ext_spec ext_link).

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre_ext prog main_itree nil gv
  POST [ tint ] main_post prog nil gv.

Definition Gprog : funspecs := ltac:(with_library prog [putchar_spec; getchar_spec;
  print_intr_spec; print_int_spec; main_spec]).

Lemma divu_repr : forall x y,
  0 <= x <= Int.max_unsigned -> 0 <= y <= Int.max_unsigned ->
  Int.divu (Int.repr x) (Int.repr y) = Int.repr (x / y).
Proof.
  intros; unfold Int.divu.
  rewrite !Int.unsigned_repr; auto.
Qed.

Opaque bind.

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

Transparent bind.

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

Lemma read_sum_eq : forall n d, read_sum n d =
  (if zlt n 1000 then if zlt d 10 then
     write_list (chars_of_Z (n + d));; write (Int.repr newline);;
     c <- read;; read_sum (n + d) (Int.unsigned c - char0)
   else ret tt else ret tt).
Proof.
  intros.
  rewrite matchM; simpl.
  rewrite <- matchM; auto.
Qed.

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  replace_SEP 0 (ITREE main_itree).
  { go_lower.
    apply has_ext_ITREE. }
  forward.
  unfold main_itree.
  rewrite <- !seq_assoc. (* Without this, forward_call gives a type error! *)
  forward_call (fun c => read_sum 0 (Int.unsigned c - char0)).
  Intros c.
  forward.
  rewrite sign_ext_inrange by auto.
  set (Inv := EX n : Z, EX c : int,
    PROP (0 <= n < 1009)
    LOCAL (temp _c (Vint c); temp _n (Vint (Int.repr n)))
    SEP (ITREE (read_sum n (Int.unsigned c - char0)))).
  unfold Swhile; forward_loop Inv break: Inv.
  { Exists 0 c; entailer!. }
  subst Inv.
  clear dependent c; Intros n c.
  forward_if.
  forward.
  forward_if.
  { forward.
    Exists n c; entailer!. }
  forward.
  rewrite <- (Int.repr_unsigned c) in H1.
  rewrite sub_repr in H1.
  pose proof (Int.unsigned_range c).
  destruct (zlt (Int.unsigned c) char0).
  { rewrite Int.unsigned_repr_eq in H1.
    rewrite <- Z_mod_plus_full with (b := 1), Zmod_small in H1; unfold char0 in *; rep_omega. }
  rewrite Int.unsigned_repr in H1 by (unfold char0 in *; rep_omega).
  rewrite read_sum_eq.
  rewrite if_true by auto.
  destruct (zlt _ _); [|unfold char0 in *; omega].
  forward_call (n + (Int.unsigned c - char0),
    write (Int.repr newline);; c' <- read;; read_sum (n + (Int.unsigned c - char0)) (Int.unsigned c' - char0)).
  { entailer!.
    rewrite <- (Int.repr_unsigned c) at 1.
    rewrite sub_repr, add_repr; auto. }
  { unfold char0 in *; rep_omega. }
  forward_call (Int.repr newline, c' <- read;; read_sum (n + (Int.unsigned c - char0)) (Int.unsigned c' - char0)).
  forward_call (fun c' => read_sum (n + (Int.unsigned c - char0)) (Int.unsigned c' - char0)).
  Intros c'.
  forward.
  rewrite sign_ext_inrange by auto.
  Exists (n + (Int.unsigned c - char0)) c'; entailer!.
  rewrite <- (Int.repr_unsigned c) at 2; rewrite sub_repr, add_repr; auto.
  { forward.
    Exists n c; entailer!. }
  subst Inv.
  Intros n c'.
  forward.
Qed.

Instance Espec : OracleKind := add_funspecs IO_Espec (ext_link_prog prog) Gprog.

Lemma prog_correct:
  semax_prog_ext prog main_itree Vprog Gprog.
Proof.
prove_semax_prog.
repeat (apply semax_func_cons_ext_vacuous; [reflexivity | reflexivity | ]).
semax_func_cons_ext.
{ simpl; Intro i.
  apply typecheck_return_value; auto. }
semax_func_cons_ext.
semax_func_cons body_print_intr.
semax_func_cons body_print_int.
semax_func_cons body_main.
Qed.
