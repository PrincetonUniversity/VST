Require Import VST.progs64.io_specs.
Require Import VST.progs64.io.
Require Import VST.floyd.proofauto.
Require Import VST.sepcomp.extspec.
Require Import VST.veric.semax_ext.
Require Import VST.veric.SequentialClight.
Require Import VST.progs64.dry_mem_lemmas.

Section IO_Dry.

Context {E : Type -> Type} {IO_E : @IO_event nat -< E}.

Notation IO_itree := (@IO_itree E).

Definition getchar_pre (m : mem) (witness : byte -> IO_itree) (z : IO_itree) :=
  let k := witness in (sutt eq (r <- read stdin;; k r) z).

Definition getchar_post (m0 m : mem) (r : int) (witness : byte -> IO_itree) (z : IO_itree) :=
  m0 = m /\ -1 <= Int.signed r <= Byte.max_unsigned /\
  let k := witness in if eq_dec (Int.signed r) (-1) then sutt eq (r <- read stdin;; k r) z else z = k (Byte.repr (Int.signed r)).

Definition putchar_pre (m : mem) (witness : byte * IO_itree) (z : IO_itree) :=
  let '(c, k) := witness in (sutt eq (write stdout c;; k) z).

Definition putchar_post (m0 m : mem) (r : int) (witness : byte * IO_itree) (z : IO_itree) :=
  m0 = m /\ let '(c, k) := witness in
  (Int.signed r = -1 \/ Int.signed r = Byte.unsigned c) /\
  if eq_dec (Int.signed r) (-1) then sutt eq (write stdout c;; k) z else z = k.

Existing Instance semax_lemmas.eq_dec_external_function.

Definition getchar_sig := {| sig_args := []; sig_res := Xint; sig_cc := cc_default |}.
Definition putchar_sig := {| sig_args := [Xint]; sig_res := Xint; sig_cc := cc_default |}.

Program Definition io_dry_spec : external_specification mem external_function IO_itree.
Proof.
  unshelve econstructor.
  - intro e.
    destruct (eq_dec e (EF_external "putchar" putchar_sig)).
    { exact (mem * (byte * IO_itree))%type. }
    destruct (eq_dec e (EF_external "getchar" getchar_sig)).
    { exact (mem * (byte -> IO_itree))%type. }
    exact False%type.
  - simpl; intros.
    if_tac in X; [|if_tac in X; last contradiction]; destruct X as (m & w).
    + exact (X1 = [Vubyte (fst w)] /\ m = X3 /\ putchar_pre X3 w X2).
    + exact (X1 = [] /\ m = X3 /\ getchar_pre X3 w X2).
  - simpl; intros ??? ot ???.
    if_tac in X; [|if_tac in X; last contradiction]; destruct X as (m0 & w).
    + exact (exists r, X1 = Some (Vint r) /\ ot <> Xvoid /\ putchar_post m0 X3 r w X2).
    + exact (exists r, X1 = Some (Vint r) /\ ot <> Xvoid /\ getchar_post m0 X3 r w X2).
  - intros; exact True%type.
Defined.

Context (ext_link : string -> ident)
  (ext_link_inj : forall s1 s2, In s1 ["getchar"; "putchar"] -> ext_link s1 = ext_link s2 -> s1 = s2).

Arguments eq_dec : simpl never.

Theorem io_spec_sound : forall `{!VSTGS IO_itree Σ}, ext_spec_entails (IO_ext_spec ext_link) io_dry_spec.
Proof.
  intros; apply juicy_dry_spec; last done; intros.
  destruct H as [H | [H | ?]]; last done; injection H as <-%ext_link_inj <-; simpl; auto.
  - if_tac; last done; intros.
    exists (m, w).
    destruct w as (c, k).
    iIntros "(Hz & _ & %Hargs & H)".
    rewrite /SEPx; monPred.unseal.
    iDestruct "H" as "(_ & (% & % & Hext) & _)".
    iDestruct (has_ext_state with "[$Hz $Hext]") as %<-.
    iSplit; first done.
    iIntros (???? (r & -> & ? & -> & Hr & Hz')).
    iMod (change_ext_state with "[$]") as "($ & ?)".
    iIntros "!>"; iExists r.
    iSplit; first done.
    rewrite /local /= /lift1; unfold_lift.
    iSplit.
    { iPureIntro; destruct ty; done. }
    iSplit; last done.
    iExists z'; iFrame; iPureIntro.
    split; last done.
    if_tac; subst; done.
  - if_tac; last done; intros.
    exists (m, w).
    iIntros "(Hz & _ & %Hargs & H)".
    rewrite /SEPx; monPred.unseal.
    iDestruct "H" as "(_ & (% & % & Hext) & _)".
    iDestruct (has_ext_state with "[$Hz $Hext]") as %<-.
    iSplit; first done.
    iIntros (???? (r & -> & ? & -> & Hr & Hz')).
    simpl in Hz'.
    iMod (change_ext_state with "[$]") as "($ & ?)".
    iIntros "!>"; iExists r.
    iSplit; first done.
    rewrite /local /= /lift1; unfold_lift.
    iSplit.
    { iPureIntro; destruct ty; done. }
    iSplit; last done.
    iExists z'; iFrame; iPureIntro.
    split; last done.
    if_tac; subst; done.
Qed.

End IO_Dry.
