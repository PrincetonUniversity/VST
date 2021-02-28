Require Import VST.progs.io.
Require Import VST.progs.io_specs.
Require Import VST.floyd.proofauto.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition putchar_spec := DECLARE _putchar putchar_spec.
Definition getchar_spec := DECLARE _getchar getchar_spec.

Definition getchar_blocking_spec :=
 DECLARE _getchar_blocking
  WITH k : byte -> IO_itree
  PRE [ ]
    PROP ()
    PARAMS ()
    GLOBALS ()
    SEP (ITREE (r <- read stdin;; k r))
  POST [ tint ]
   EX i : byte,
    PROP ()
    LOCAL (temp ret_temp (Vubyte i))
    SEP (ITREE (k i)).

Definition putchar_blocking_spec :=
 DECLARE _putchar_blocking
  WITH c : byte, k : IO_itree
  PRE [ tint ]
    PROP ()
    PARAMS (Vubyte c)
    GLOBALS ()
    SEP (ITREE (r <- write stdout c ;; k))
  POST [ tint ]
    PROP ()
    LOCAL (temp ret_temp (Vubyte c))
    SEP (ITREE k).

Lemma div_10_dec : forall n, 0 < n ->
  (Z.to_nat (n / 10) < Z.to_nat n)%nat.
Proof.
  intros.
  change 10 with (Z.of_nat 10).
  rewrite <- (Z2Nat.id n) by lia.
  rewrite <- div_Zdiv by discriminate.
  rewrite !Nat2Z.id.
  apply Nat2Z.inj_lt.
  rewrite div_Zdiv, Z2Nat.id by lia; simpl.
  apply Z.div_lt; auto; lia.
Qed.

Program Fixpoint chars_of_Z (n : Z) { measure (Z.to_nat n) } : list byte :=
  let n' := n / 10 in
  match n' <=? 0 with true => [Byte.repr (n + char0)] | false => chars_of_Z n' ++ [Byte.repr (n mod 10 + char0)] end.
Next Obligation.
Proof.
  apply div_10_dec.
  symmetry in Heq_anonymous; apply Z.leb_nle in Heq_anonymous.
  eapply Z.lt_le_trans, Z_mult_div_ge with (b := 10); lia.
Defined.

(* The function computed by print_intr *)
Program Fixpoint intr n { measure (Z.to_nat n) } : list byte :=
  match n <=? 0 with
  | true => []
  | false => intr (n / 10) ++ [Byte.repr (n mod 10 + char0)]
  end.
Next Obligation.
Proof.
  apply div_10_dec.
  symmetry in Heq_anonymous; apply Z.leb_nle in Heq_anonymous; lia.
Defined.

Definition print_intr_spec :=
 DECLARE _print_intr
  WITH i : Z, tr : IO_itree
  PRE [ tuint ]
    PROP (0 <= i <= Int.max_unsigned)
    PARAMS (Vint (Int.repr i))
    GLOBALS ()
    SEP (ITREE (write_list stdout (intr i) ;; tr))
  POST [ tvoid ]
    PROP ()
    LOCAL ()
    SEP (ITREE tr).

Definition print_int_spec :=
 DECLARE _print_int
  WITH i : Z, tr : IO_itree
  PRE [ tuint ]
    PROP (0 <= i <= Int.max_unsigned)
    PARAMS (Vint (Int.repr i))
    GLOBALS ()
    SEP (ITREE (write_list stdout (chars_of_Z i) ;; tr))
  POST [ tvoid ]
    PROP ()
    LOCAL ()
    SEP (ITREE tr).

Definition read_sum n d : IO_itree :=
   ITree.iter (fun '(n, d) =>
       if zlt n 1000 then if zlt d 10 then
         write_list stdout (chars_of_Z (n + d));; write stdout (Byte.repr newline);;
              c <- read stdin;;
              Ret (inl (n + d, Byte.unsigned c - char0)) (* loop again with these parameters *)
       else Ret (inr tt) else Ret (inr tt)) (* inr to end the loop *)
     (n, d).

Definition main_itree := c <- read stdin;; read_sum 0 (Byte.unsigned c - char0).

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog main_itree gv
  POST [ tint ] main_post prog gv.

Definition Gprog : funspecs := ltac:(with_library prog [putchar_spec; getchar_spec;
  print_intr_spec; print_int_spec; getchar_blocking_spec; putchar_blocking_spec; main_spec]).

Lemma divu_repr : forall x y,
  0 <= x <= Int.max_unsigned -> 0 <= y <= Int.max_unsigned ->
  Int.divu (Int.repr x) (Int.repr y) = Int.repr (x / y).
Proof.
  intros; unfold Int.divu.
  rewrite !Int.unsigned_repr; auto.
Qed.

Opaque Nat.div Nat.modulo.

Lemma intr_eq : forall n, intr n =
  match n <=? 0 with
  | true => []
  | false => intr (n / 10) ++ [Byte.repr (n mod 10 + char0)]
  end.
Proof.
  intros.
  unfold intr at 1.
  rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold intr.
  destruct n; reflexivity.
Qed.

Lemma body_getchar_blocking: semax_body Vprog Gprog f_getchar_blocking getchar_blocking_spec.
Proof.
  start_function.
  forward.
  forward_while (EX i : int, PROP (-1 <= Int.signed i <= two_p 8 - 1) LOCAL (temp _r (Vint i))
    SEP (ITREE (if eq_dec (Int.signed i) (-1) then (r <- read stdin;; k r) else k (Byte.repr (Int.signed i))))).
  - Exists (Int.neg (Int.repr 1)); entailer!.
    { simpl; lia. }
    rewrite if_true; auto.
  - entailer!.
  - subst; rewrite Int.signed_repr by rep_lia.
    rewrite if_true by auto.
    forward_call k.
    Intros i.
    forward.
    Exists i; entailer!.
  - assert (Int.signed i <> -1).
    { intro X.
      apply f_equal with (f := Int.repr) in X.
      rewrite Int.repr_signed in X; auto. }
    rewrite if_false by auto.
    forward.
    Exists (Byte.repr (Int.signed i)); entailer!.
    unfold Vubyte; rewrite Byte.unsigned_repr, Int.repr_signed; auto.
    split; try lia.
    etransitivity; [apply H|].
    simpl; rep_lia.
Qed.

Lemma body_putchar_blocking: semax_body Vprog Gprog f_putchar_blocking putchar_blocking_spec.
Proof.
  start_function.
  forward.
  forward_while (EX i : int, PROP (Int.signed i = -1 \/ Int.signed i = Byte.unsigned c) LOCAL (temp _r (Vint i); temp _c (Vubyte c))
    SEP (ITREE (if eq_dec (Int.signed i) (-1) then (r <- write stdout c;; k) else k))).
  - Exists (Int.neg (Int.repr 1)); entailer!.
    rewrite if_true; auto.
  - entailer!.
  - subst; rewrite Int.signed_repr by rep_lia.
    rewrite if_true by auto.
    forward_call (c, k).
    Intros i.
    forward.
    Exists i; entailer!.
  - assert (Int.signed i <> -1).
    { intro X.
      apply f_equal with (f := Int.repr) in X.
      rewrite Int.repr_signed in X; auto. }
    rewrite if_false by auto.
    destruct H; [contradiction | subst].
    forward.
    entailer!.
    unfold Vubyte.
    rewrite <- H, Int.repr_signed; auto.
Qed.

Lemma body_print_intr: semax_body Vprog Gprog f_print_intr print_intr_spec.
Proof.
  start_function.
  forward_if (PROP () LOCAL () SEP (ITREE tr)).
  - forward.
    forward.
    rewrite modu_repr, divu_repr by (lia || computable).
    rewrite intr_eq.
    destruct (Z.leb_spec i 0); try lia.
    rewrite write_list_app, bind_bind.
    forward_call (i / 10, write_list stdout [Byte.repr (i mod 10 + char0)];; tr).
    { split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]. }
    simpl write_list.
    forward_call (Byte.repr (i mod 10 + char0), tr).
    { entailer!.
      unfold Vubyte; rewrite Byte.unsigned_repr; auto.
      pose proof (Z_mod_lt i 10); unfold char0; rep_lia. }
    { rewrite <- sepcon_emp at 1; apply sepcon_derives; [|cancel].
      rewrite bind_ret'; auto. }
    entailer!.
  - forward.
    subst; entailer!.
    simpl.
    rewrite bind_ret_l; auto.
Qed.

Lemma chars_of_Z_eq : forall n, chars_of_Z n =
  let n' := n / 10 in
  match n' <=? 0 with true => [Byte.repr (n + char0)] | false => chars_of_Z n' ++ [Byte.repr (n mod 10 + char0)] end.
Proof.
  intros.
  unfold chars_of_Z at 1.
  rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold chars_of_Z.
  destruct (_ <=? _); reflexivity.
Qed.

Lemma chars_of_Z_intr : forall n, 0 < n ->
  chars_of_Z n = intr n.
Proof.
  induction n using (well_founded_induction (Zwf.Zwf_well_founded 0)); intro.
  rewrite chars_of_Z_eq, intr_eq.
  destruct (n <=? 0) eqn: Hn; [apply Zle_bool_imp_le in Hn; lia|].
  simpl.
  destruct (n / 10 <=? 0) eqn: Hdiv.
  - apply Zle_bool_imp_le in Hdiv.
    assert (0 <= n / 10).
    { apply Z.div_pos; lia. }
    assert (n / 10 = 0) as Hz by lia.
    rewrite Hz; simpl.
    apply Z.div_small_iff in Hz as [|]; try lia.
    rewrite Zmod_small; auto.
  - apply Z.leb_nle in Hdiv.
    rewrite H; auto; try lia.
    split; try lia.
    apply Z.div_lt; auto; lia.
Qed.

Lemma body_print_int: semax_body Vprog Gprog f_print_int print_int_spec.
Proof.
  start_function.
  forward_if (PROP () LOCAL () SEP (ITREE tr)).
  - subst.
    forward_call (Byte.repr char0, tr).
    { rewrite chars_of_Z_eq; simpl.
      erewrite <- sepcon_emp at 1; apply sepcon_derives; [|cancel].
      rewrite bind_ret'; apply derives_refl. }
    entailer!.
  - forward_call (i, tr).
    { rewrite chars_of_Z_intr by lia; cancel. }
    entailer!.
Qed.

Lemma read_sum_eq : forall n d, read_sum n d ≈
  (if zlt n 1000 then if zlt d 10 then
     write_list stdout (chars_of_Z (n + d));; write stdout (Byte.repr newline);;
     c <- read stdin;; read_sum (n + d) (Byte.unsigned c - char0)
   else Ret tt else Ret tt).
Proof.
  intros.
  unfold read_sum; rewrite unfold_iter.
  unfold ITree.iter.
  if_tac; [|rewrite bind_ret_l; reflexivity].
  if_tac; [|rewrite bind_ret_l; reflexivity].
  repeat setoid_rewrite bind_bind.
  setoid_rewrite bind_ret_l.
  setoid_rewrite tau_eutt.
  reflexivity.
Qed.

Lemma signed_char_unsigned : forall c, Byte.unsigned c <= two_p 8 - 1.
Proof.
  intros.
  pose proof (Byte.unsigned_range c).
  unfold Byte.modulus, two_power_nat in H; simpl in *; lia.
Qed.

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  unfold main_pre.
  sep_apply (has_ext_ITREE(E := @IO_event nat)).
  forward.
  unfold main_itree.
  rewrite <- !seq_assoc. (* Without this, forward_call gives a type error! *)
  forward_call (fun c => read_sum 0 (Byte.unsigned c - char0)).
  Intros c.
  forward.
  rewrite zero_ext_inrange by (pose proof (signed_char_unsigned c); rewrite Int.unsigned_repr; rep_lia).
  set (Inv := EX n : Z, EX c : byte,
    PROP (0 <= n < 1009)
    LOCAL (temp _c (Vubyte c); temp _n (Vint (Int.repr n)))
    SEP (ITREE (read_sum n (Byte.unsigned c - char0)))).
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
  destruct (zlt (Byte.unsigned c) char0).
  { rewrite Int.unsigned_repr_eq in H1.
    rewrite <- Z_mod_plus_full with (b := 1), Zmod_small in H1; unfold char0 in *; rep_lia. }
  rewrite Int.unsigned_repr in H1 by (unfold char0 in *; rep_lia).
  rewrite read_sum_eq.
  rewrite if_true by auto.
  destruct (zlt _ _); [|unfold char0 in *; lia].
  forward_call (n + (Byte.unsigned c - char0),
    write stdout (Byte.repr newline);; c' <- read stdin;; read_sum (n + (Byte.unsigned c - char0)) (Byte.unsigned c' - char0)).
  forward_call (Byte.repr newline, c' <- read stdin;; read_sum (n + (Byte.unsigned c - char0)) (Byte.unsigned c' - char0)).
  forward_call (fun c' => read_sum (n + (Byte.unsigned c - char0)) (Byte.unsigned c' - char0)).
  Intros c'.
  forward.
  rewrite zero_ext_inrange by (pose proof (signed_char_unsigned c'); rewrite Int.unsigned_repr; rep_lia).
  Exists (n + (Byte.unsigned c - char0)) c'; entailer!.
  { forward.
    Exists n c; entailer!. }
  subst Inv.
  Intros n c'.
  forward.
Qed.

Definition ext_link := ext_link_prog prog.

Instance Espec : OracleKind := IO_Espec ext_link.

Lemma prog_correct:
  semax_prog prog main_itree Vprog Gprog.
Proof.
prove_semax_prog.
semax_func_cons_ext.
{ simpl; Intro i.
  apply typecheck_return_value with (t := Tint16signed); auto. }
semax_func_cons_ext.
{ simpl; Intro i'.
  apply typecheck_return_value with (t := Tint16signed); auto. }
semax_func_cons body_getchar_blocking.
semax_func_cons body_putchar_blocking.
semax_func_cons body_print_intr.
semax_func_cons body_print_int.
semax_func_cons body_main.
Qed.

Require Import VST.veric.SequentialClight.
Require Import VST.progs.io_dry.

Lemma init_mem_exists : { m | Genv.init_mem prog = Some m }.
Proof.
  unfold Genv.init_mem; simpl.
Ltac alloc_block m n := match n with
  | O => idtac
  | S ?n' => let m' := fresh "m" in let Hm' := fresh "Hm" in
    destruct (dry_mem_lemmas.drop_alloc m) as [m' Hm']; alloc_block m' n'
  end.
  alloc_block Mem.empty 59%nat.
  eexists; repeat match goal with H : ?a = _ |- match ?a with Some m' => _ | None => None end = _ => rewrite H end.
  reflexivity.
Qed.

Definition init_mem := proj1_sig init_mem_exists.

Definition main_block_exists : {b | Genv.find_symbol (Genv.globalenv prog) (AST.prog_main prog) = Some b}.
Proof.
  eexists; simpl.
  unfold Genv.find_symbol; simpl; reflexivity.
Qed.

Definition main_block := proj1_sig main_block_exists.

Theorem prog_ext_correct : exists q,
  semantics.initial_core (Clight_core.cl_core_sem (globalenv prog)) 0 init_mem q init_mem (Vptr main_block Ptrofs.zero) [] /\
  forall n, @step_lemmas.dry_safeN _ _ _ _ semax.genv_symb_injective (Clight_core.cl_core_sem (globalenv prog))
             (io_dry_spec ext_link) {| genv_genv := Genv.globalenv prog; genv_cenv := prog_comp_env prog |} n
            main_itree q init_mem.
Proof.
  edestruct whole_program_sequential_safety_ext with (V := Vprog) as (b & q & Hb & Hq & Hsafe).
  - repeat intro; hnf.
    apply I.
  - apply juicy_dry_specs.
  - apply dry_spec_mem.
  - apply CSHL_Sound.semax_prog_sound, prog_correct.
  - apply (proj2_sig init_mem_exists).
  - exists q.
    rewrite (proj2_sig main_block_exists) in Hb; inv Hb.
    split; auto.
Qed.

Require Import VST.progs.os_combine.
Require Import VST.progs.io_combine.
Require Import VST.progs.io_os_specs.
Require Import VST.progs.io_os_connection.

(* correctness down to OS traces, with relationship between syscall events and actual external reads/writes *)
Theorem prog_OS_correct : forall {H : io_os_specs.ThreadsConfigurationOps},
  exists q,
  semantics.initial_core (Clight_core.cl_core_sem (globalenv prog)) 0 init_mem q init_mem (Vptr main_block Ptrofs.zero) [] /\
     forall n s0, s0.(io_log) = [] -> s0.(console) = {| cons_buf := []; rpos := 0 |} ->
    exists traces, OS_safeN_trace prog n Traces.TEnd traces main_itree s0 q init_mem /\
     forall t s, Ensembles.In _ traces (t, s) -> exists z', consume_trace main_itree z' t /\ t = trace_of_ostrace s.(io_log) /\
      valid_trace_user s.(io_log).
Proof.
  intros.
  edestruct IO_OS_ext with (V := Vprog) as (b & q & Hb & Hq & Hsafe).
  - apply prog_correct.
  - apply (proj2_sig init_mem_exists).
  - exists q.
    rewrite (proj2_sig main_block_exists) in Hb; inv Hb.
    auto.
Qed.
