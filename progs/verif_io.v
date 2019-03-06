Require Import VST.progs.io.
Require Import VST.progs.io_specs.
Require Import VST.floyd.proofauto.
Require Import DeepWeb.Free.Monad.Free.
Import MonadNotations.
Require Import DeepWeb.Free.Monad.Common.
Require Import DeepWeb.Free.Monad.Eq.Utt.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition putchar_spec := DECLARE _putchar putchar_spec.
Definition getchar_spec := DECLARE _getchar getchar_spec.

Lemma div_10_dec : forall n, 0 < n ->
  (Z.to_nat (n / 10) < Z.to_nat n)%nat.
Proof.
  intros.
  change 10 with (Z.of_nat 10).
  rewrite <- (Z2Nat.id n) by omega.
  rewrite <- div_Zdiv by discriminate.
  rewrite !Nat2Z.id.
  apply Nat2Z.inj_lt.
  rewrite div_Zdiv, Z2Nat.id by omega; simpl.
  apply Z.div_lt; auto; omega.
Qed.

Program Fixpoint chars_of_Z (n : Z) { measure (Z.to_nat n) } : list int :=
  let n' := n / 10 in
  match n' <=? 0 with true => [Int.repr (n + char0)] | false => chars_of_Z n' ++ [Int.repr (n mod 10 + char0)] end.
Next Obligation.
Proof.
  apply div_10_dec.
  symmetry in Heq_anonymous; apply Z.leb_nle in Heq_anonymous.
  eapply Z.lt_le_trans, Z_mult_div_ge with (b := 10); omega.
Defined.

(* The function computed by print_intr *)
Program Fixpoint intr n { measure (Z.to_nat n) } : list int :=
  match n <=? 0 with
  | true => []
  | false => intr (n / 10) ++ [Int.repr (n mod 10 + char0)]
  end.
Next Obligation.
Proof.
  apply div_10_dec.
  symmetry in Heq_anonymous; apply Z.leb_nle in Heq_anonymous; omega.
Defined.

Definition print_intr_spec :=
 DECLARE _print_intr
  WITH i : Z, tr : IO_itree
  PRE [ _i OF tuint ]
    PROP (0 <= i <= Int.max_unsigned)
    LOCAL (temp _i (Vint (Int.repr i)))
    SEP (ITREE (write_list (intr i) ;; tr))
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
  match n <=? 0 with
  | true => []
  | false => intr (n / 10) ++ [Int.repr (n mod 10 + char0)]
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
    destruct (i <=? 0) eqn: Hi.
    { apply Zle_bool_imp_le in Hi; omega. }
    erewrite ITREE_ext by (apply bind_mor with (y0 := fun _ => tr); [apply write_list_app | reflexivity]).
    erewrite ITREE_ext by apply bind_bind.
    forward_call (i / 10, write_list [Int.repr (i mod 10 + char0)];; tr).
    { rewrite <- sepcon_emp at 1; apply sepcon_derives; cancel.
      apply derives_refl. }
    { split; [apply Z.div_pos; omega | apply Z.div_le_upper_bound; omega]. }
    simpl write_list.
    forward_call (Int.repr (i mod 10 + char0), tr).
    { rewrite <- sepcon_emp at 1; apply sepcon_derives; [|cancel].
      apply ITREE_impl.
      apply bind_mor; [|reflexivity].
      etransitivity; [|apply bind_ret].
      apply bind_mor; [|intros []]; reflexivity. }
    entailer!.
  - forward.
    subst; entailer!.
    erewrite ITREE_ext; [apply derives_refl|].
    simpl.
    rewrite ret_bind.
    apply pop_tau; reflexivity.
  - forward.
Qed.

Lemma chars_of_Z_eq : forall n, chars_of_Z n =
  let n' := n / 10 in
  match n' <=? 0 with true => [Int.repr (n + char0)] | false => chars_of_Z n' ++ [Int.repr (n mod 10 + char0)] end.
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
  destruct (n <=? 0) eqn: Hn; [apply Zle_bool_imp_le in Hn; omega|].
  simpl.
  destruct (n / 10 <=? 0) eqn: Hdiv.
  - apply Zle_bool_imp_le in Hdiv.
    assert (0 <= n / 10).
    { apply Z.div_pos; omega. }
    assert (n / 10 = 0) as Hz by omega.
    rewrite Hz; simpl.
    apply Z.div_small_iff in Hz as [|]; try omega.
    rewrite Zmod_small; auto.
  - apply Z.leb_nle in Hdiv.
    rewrite H; auto; try omega.
    split; try omega.
    apply Z.div_lt; auto; omega.
Qed.

Lemma body_print_int: semax_body Vprog Gprog f_print_int print_int_spec.
Proof.
  start_function.
  forward_if (PROP () LOCAL () SEP (ITREE tr)).
  - subst.
    forward_call (Int.repr char0, tr).
    { rewrite chars_of_Z_eq; simpl.
      erewrite <- sepcon_emp at 1; apply sepcon_derives; [|cancel].
      erewrite ITREE_ext; [apply derives_refl|].
      apply bind_mor; [|reflexivity].
      etransitivity; [|apply bind_ret].
      apply bind_mor; [|intros []]; reflexivity. }
    entailer!.
  - forward_call (i, tr).
    { rewrite chars_of_Z_intr by omega; cancel. }
    entailer!.
  - forward.
Qed.

Lemma read_sum_eq : forall n d, read_sum n d =
  (if zlt n 1000 then if zlt d 10 then
     write_list (chars_of_Z (n + d));; write (Int.repr newline);;
     c <- read;; read_sum (n + d) (Int.unsigned c - char0)
   else ret tt else ret tt).
Proof.
  intros.
  rewrite (match_itree (read_sum n d)); simpl.
  rewrite <- match_itree; auto.
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

Definition ext_link := ext_link_prog prog.

Instance Espec : OracleKind := IO_Espec ext_link.

Lemma prog_correct:
  semax_prog_ext prog main_itree Vprog Gprog.
Proof.
prove_semax_prog.
semax_func_cons_ext.
{ simpl; Intro i.
  apply typecheck_return_value; auto. }
semax_func_cons_ext.
semax_func_cons body_print_intr.
semax_func_cons body_print_int.
semax_func_cons body_main.
Qed.

Require Import VST.veric.SequentialClight.
Require Import VST.progs.io_dry.

Definition init_mem_exists : { m | Genv.init_mem prog = Some m }.
Proof.
  unfold Genv.init_mem; simpl.
Admitted. (* seems true, but hard to prove -- can we compute it? *)

Definition init_mem := proj1_sig init_mem_exists.

Definition main_block_exists : {b | Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b}.
Proof.
  eexists; simpl.
  unfold Genv.find_symbol; simpl; reflexivity.
Qed.

Definition main_block := proj1_sig main_block_exists.

Theorem prog_toplevel : exists q : Clight_new.corestate,
  semantics.initial_core (Clight_new.cl_core_sem (globalenv prog)) 0 init_mem q init_mem (Vptr main_block Ptrofs.zero) [] /\
  forall n, @step_lemmas.dry_safeN _ _ _ _ Clight_sim.genv_symb_injective (Clight_sim.coresem_extract_cenv (Clight_new.cl_core_sem (globalenv prog)) (prog_comp_env prog))
             (io_dry_spec ext_link) {| Clight_sim.CC.genv_genv := Genv.globalenv prog; Clight_sim.CC.genv_cenv := prog_comp_env prog |} n
            main_itree q init_mem.
Proof.
  edestruct whole_program_sequential_safety_ext with (V := Vprog)(G := Gprog) as (b & q & m' & Hb & Hq & Hsafe).
  - apply juicy_dry_specs.
  - apply dry_spec_mem.
  - apply CSHL_Sound.semax_prog_ext_sound, prog_correct.
  - apply (proj2_sig init_mem_exists).
  - exists q.
    rewrite (proj2_sig main_block_exists) in Hb; inv Hb.
    assert (m' = init_mem); [|subst; auto].
    destruct Hq; tauto.
Qed.
