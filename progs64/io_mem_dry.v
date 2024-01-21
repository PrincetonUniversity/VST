Require Import VST.progs64.io_mem_specs.
Require Import VST.floyd.proofauto.
Require Import VST.sepcomp.extspec.
Require Import VST.veric.semax_ext.
Require Import VST.veric.SequentialClight.
Require Import VST.progs64.dry_mem_lemmas.
Require Import VST.veric.mem_lessdef.

Section IO_Dry.

Definition bytes_to_memvals li := concat (map (fun i => encode_val Mint8unsigned (Vubyte i)) li).

Lemma bytes_to_memvals_length : forall li, Zlength (bytes_to_memvals li) = Zlength li.
Proof.
  intros.
  rewrite !Zlength_correct; f_equal.
  unfold bytes_to_memvals.
  rewrite <- map_map, encode_vals_length, map_length; auto.
Qed.

Context {E : Type -> Type} {IO_E : @IO_event nat -< E}.

Notation IO_itree := (@IO_itree E).

Definition getchars_pre (m : mem) (witness : share * val * Z * (list byte -> IO_itree)) (z : IO_itree) :=
  let '(sh, buf, len, k) := witness in (sutt eq (r <- read_list stdin (Z.to_nat len);; k r) z) /\
    match buf with Vptr b ofs =>
      Mem.range_perm m b (Ptrofs.unsigned ofs) (Ptrofs.unsigned ofs + Z.max 0 len) Memtype.Cur Memtype.Writable
      | _ => False end.

Definition getchars_post (m0 m : mem) r (witness : share * val * Z * (list byte -> IO_itree)) (z : IO_itree) :=
  let '(sh, buf, len, k) := witness in r = Int.repr len /\
    exists msg, Zlength msg = len /\ z = k msg /\
    match buf with Vptr b ofs => exists m', Mem.storebytes m0 b (Ptrofs.unsigned ofs) (bytes_to_memvals msg) = Some m' /\
        mem_equiv m m'
    | _ => False end.

Definition putchars_pre (m : mem) (witness : share * val * list byte * Z * list val * IO_itree) (z : IO_itree) :=
  let '(sh, buf, msg, _, _, k) := witness in (sutt eq (write_list stdout msg;; k) z) /\
  match buf with Vptr b ofs =>
    Mem.loadbytes m b (Ptrofs.unsigned ofs) (Zlength msg) =
      Some (bytes_to_memvals msg)
    | _ => False end.

Definition putchars_post (m0 m : mem) r (witness : share * val * list byte * Z * list val * IO_itree) (z : IO_itree) :=
  let '(sh, buf, msg, _, _, k) := witness in m0 = m /\ r = Int.repr (Zlength msg) /\ z = k.

Existing Instance semax_lemmas.eq_dec_external_function.

Definition getchars_sig := {| sig_args := [Tptr; AST.Tint]; sig_res := Tret AST.Tint; sig_cc := cc_default |}.
Definition putchars_sig := {| sig_args := [Tptr; AST.Tint]; sig_res := Tret AST.Tint; sig_cc := cc_default |}.

Program Definition io_dry_spec : external_specification mem external_function IO_itree.
Proof.
  unshelve econstructor.
  - intro e.
    destruct (eq_dec e (EF_external "putchars" putchars_sig)).
    { exact (mem * (share * val * list byte * Z * list val * IO_itree))%type. }
    destruct (eq_dec e (EF_external "getchars" getchars_sig)).
    { exact (mem * (share * val * Z * (list byte -> IO_itree)))%type. }
    exact False%type.
  - simpl; intros.
    if_tac in X; [|if_tac in X; last contradiction]; destruct X as (m & w).
    + exact ((let '(_, buf, msg, _, _, _) := w in X1 = [buf; Vint (Int.repr (Zlength msg))]) /\ m = X3 /\ putchars_pre X3 w X2).
    + exact ((let '(_, buf, len, _) := w in X1 = [buf; Vint (Int.repr len)]) /\ m = X3 /\ getchars_pre X3 w X2).
  - simpl; intros ??? ot ???.
    if_tac in X; [|if_tac in X; last contradiction]; destruct X as (m0 & w).
    + exact (exists r, X1 = Some (Vint r) /\ ot <> AST.Tvoid /\ putchars_post m0 X3 r w X2).
    + exact (exists r, X1 = Some (Vint r) /\ ot <> AST.Tvoid /\ getchars_post m0 X3 r w X2).
  - intros; exact True%type.
Defined.

Context {CS : compspecs} (ext_link : string -> ident) (ext_link_inj : forall s1 s2, ext_link s1 = ext_link s2 -> s1 = s2).

Arguments eq_dec : simpl never.

Theorem io_spec_sound : forall `{!VSTGS IO_itree Σ}, ext_spec_entails (IO_ext_spec ext_link) io_dry_spec.
Proof.
  intros; apply juicy_dry_spec; last done; intros.
  destruct H as [H | [H | ?]]; last done; injection H as <-%ext_link_inj <-; simpl.
  - if_tac; last done; intros.
    exists (m, w).
(*    destruct w as (c, k).
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
Qed.*)
Admitted.

End IO_Dry.
