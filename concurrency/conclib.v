Require Export VST.veric.slice.
Require Export VST.concurrency.semax_conc_pred.
Require Export VST.concurrency.semax_conc.
Require Export VST.floyd.proofauto.
Require Export VST.zlist.sublist.
Import LiftNotation.
Import -(notations) compcert.lib.Maps.

(* Require Export VST.concurrency.conclib_veric. *)

Notation vint z := (Vint (Int.repr z)).
Notation vptrofs z := (Vptrofs (Ptrofs.repr z)).

Section mpred.

Context `{!VSTGS OK_ty Σ}.

Lemma big_sep_map : forall {B : bi} {A} (P Q : A -> B) (l : list A),
  [∗] map (fun a => P a ∗ Q a) l ⊣⊢ [∗] map P l ∗ [∗] map Q l.
Proof.
  induction l; simpl.
  - symmetry; apply bi.sep_emp.
  - rewrite IHl; iSplit; iIntros "H"; iStopProof; cancel.
Qed.

(*Ltac forward_malloc t n := forward_call (sizeof t); [simpl; try computable |
  Intros n; rewrite malloc_compat by (auto; reflexivity); Intros;
  rewrite memory_block_data_at_ by auto].
*)

(*Lemma semax_fun_id'' id f gv Espec {cs} Delta P Q R Post c :
  (var_types Delta) ! id = None ->
  (glob_specs Delta) ! id = Some f ->
  (glob_types Delta) ! id = Some (type_of_funspec f) ->
  snd (local2ptree Q) = Some gv ->
  @semax cs Espec Delta
    (PROPx P
      (LOCALx Q
      (SEPx ((func_ptr' f (gv id)) :: R)))) c Post ->
  @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R))) c Post.
Proof.
intros V G GS HGV SA.
apply (semax_fun_id id f Delta); auto.
eapply semax_pre_post; try apply SA; clear SA;
 intros; try apply ENTAIL_refl.
destruct (local2ptree Q) as [[[T1 T2] Res] GV] eqn:?H.
simpl in HGV; subst GV.
erewrite (local2ptree_soundness P) by eauto.
erewrite (local2ptree_soundness P) by eauto.
go_lowerx.
entailer.
  unfold func_ptr'.
  rewrite <- andp_left_corable by (apply corable_func_ptr).
  rewrite andp_comm; apply andp_derives; auto.
  erewrite <- gvars_eval_var; [apply derives_refl | eauto ..].
  pose proof LocalD_sound_gvars gv T1 T2 _ eq_refl.
  clear - H2 H3.
  revert H3.
  generalize (gvars gv).
  rewrite <- Forall_forall.
  induction (LocalD T1 T2 (Some gv)); [constructor |].
  simpl in H2.
  destruct H2; constructor; auto.
Qed.

Ltac get_global_function'' _f :=
eapply (semax_fun_id'' _f); try reflexivity.

(* legacy *)
Ltac start_dep_function := start_function.

(* automation for dependent funspecs moved to call_lemmas and forward.v*)*)

Lemma PROP_into_SEP : forall P Q (R : list mpred), PROPx P (LOCALx Q (SEPx R)) ⊣⊢
  PROPx [] (LOCALx Q (SEPx ((⌜fold_right and True P⌝ ∧ emp) :: R))).
Proof.
  intros; unfold PROPx, LOCALx, SEPx; split => rho; monPred.unseal.
  iSplit.
  - iIntros "($ & $ & $)".
  - iIntros "(_ & $ & ($ & _) & $)".
Qed.

Lemma PROP_into_SEP_LAMBDA : forall P U Q (R : list mpred), PROPx P (LAMBDAx U Q (SEPx R)) ⊣⊢
  PROPx [] (LAMBDAx U Q (SEPx ((⌜fold_right and True P⌝ ∧ emp) :: R))).
Proof.
  intros; unfold PROPx, LAMBDAx, GLOBALSx, LOCALx, SEPx, argsassert2assert;
    split => rho; monPred.unseal.
  iSplit.
  - iIntros "($ & $ & $)".
  - iIntros "(_ & $ & $ & ($ & _) & $)".
Qed.


Definition exclusive_mpred (P : mpred) := P ∗ P ⊢ False.

Lemma exclusive_weak_exclusive : forall P, exclusive_mpred P -> ⊢ P ∗ P -∗ False.
Proof.
  unfold exclusive_mpred; intros ? ->; auto.
Qed.

Lemma exclusive_sepcon1 : forall P Q (HP : exclusive_mpred P), exclusive_mpred (P ∗ Q).
Proof.
  unfold exclusive_mpred; intros.
  iIntros "((? & ?) & (? & ?))"; iDestruct (HP with "[$]") as "[]".
Qed.

Lemma exclusive_sepcon2 : forall P Q (HP : exclusive_mpred Q), exclusive_mpred (P ∗ Q).
Proof.
  intros; rewrite /exclusive_mpred comm; apply exclusive_sepcon1; auto.
Qed.

Lemma exclusive_andp1 : forall P Q (HP : exclusive_mpred P), exclusive_mpred (P ∧ Q).
Proof.
  unfold exclusive_mpred; intros.
  iIntros "((? & _) & (? & _))"; iDestruct (HP with "[$]") as "[]".
Qed.

Lemma exclusive_andp2 : forall P Q (HQ : exclusive_mpred Q), exclusive_mpred (P ∧ Q).
Proof.
  intros; rewrite /exclusive_mpred comm; apply exclusive_andp1; auto.
Qed.

Lemma exclusive_False : exclusive_mpred False.
Proof.
  unfold exclusive_mpred.
  iIntros "([] & _)".
Qed.

Lemma derives_exclusive : forall P Q (Hderives : P ⊢ Q) (HQ : exclusive_mpred Q),
  exclusive_mpred P.
Proof.
  unfold exclusive_mpred; intros.
  rewrite Hderives //.
Qed.

Lemma mapsto_exclusive : forall {cs : compspecs} (sh : Share.t) (t : type) (v : val),
  sh ≠ Share.bot -> exclusive_mpred (∃ v2 : _, mapsto sh t v v2).
Proof.
  intros; unfold exclusive_mpred.
  Intros v1 v2; apply mapsto_conflict; auto.
Qed.

Lemma field_at__exclusive : forall (cs : compspecs) (sh : Share.t) (t : type) (fld : list gfield) (p : val),
  sepalg.nonidentity sh ->
  0 < sizeof (nested_field_type t fld) -> exclusive_mpred (field_at_ sh t fld p).
Proof.
  intros; apply field_at__conflict; auto.
Qed.

Lemma ex_field_at_exclusive : forall (cs : compspecs) (sh : Share.t) (t : type) (fld : list gfield) (p : val),
  sepalg.nonidentity sh ->
  0 < sizeof (nested_field_type t fld) -> exclusive_mpred (∃ v : _, field_at sh t fld v p).
Proof.
  intros; unfold exclusive_mpred.
  Intros v v'; apply field_at_conflict; auto.
Qed.

Corollary field_at_exclusive : forall (cs : compspecs) (sh : Share.t) (t : type) (fld : list gfield) v (p : val),
  sepalg.nonidentity sh -> 0 < sizeof (nested_field_type t fld) -> exclusive_mpred (field_at sh t fld v p).
Proof.
  intros; eapply derives_exclusive, ex_field_at_exclusive; eauto.
Qed.

Lemma ex_data_at_exclusive : forall (cs : compspecs) (sh : Share.t) (t : type) (p : val),
  sepalg.nonidentity sh -> 0 < sizeof t -> exclusive_mpred (∃ v : _, data_at sh t v p).
Proof.
  intros; unfold exclusive_mpred.
  Intros v v'; apply data_at_conflict; auto.
Qed.

Corollary data_at_exclusive : forall (cs : compspecs) (sh : Share.t) (t : type) v (p : val),
  sepalg.nonidentity sh -> 0 < sizeof t -> exclusive_mpred (data_at sh t v p).
Proof.
  intros; eapply derives_exclusive, ex_data_at_exclusive; eauto.
Qed.

Corollary data_at__exclusive : forall (cs : compspecs) (sh : Share.t) (t : type) (p : val),
  sepalg.nonidentity sh -> 0 < sizeof t -> exclusive_mpred (data_at_ sh t p).
Proof.
  intros; eapply derives_exclusive, data_at_exclusive; eauto.
Qed.

Lemma func_ptr_pre : forall sig cc A P1 P2 Q p, (forall a, P1 a ≡ P2 a) ->
  func_ptr (NDmk_funspec sig cc A P1 Q) p ⊢ func_ptr (NDmk_funspec sig cc A P2 Q) p.
Proof.
  intros; apply func_ptr_mono.
  split; first done; intros; simpl.
  rewrite -H -fupd_intro.
  Exists x2 (emp : mpred); entailer!.
Qed.

End mpred.

#[export] Hint Resolve unreadable_bot : core.
#[export] Hint Resolve excl_auth_valid : init. (* doesn't currently seem to work *)

Ltac ghost_alloc G :=
  lazymatch goal with |-semax _ _ (PROPx _ (LOCALx _ (SEPx (?R1 :: _)))) _ _ =>
    rewrite -{1}(bi.emp_sep R1); Intros; viewshift_SEP 0 (∃ g : _, G g);
  [go_lowerx; iIntros "_"; iApply own_alloc; auto; simpl; auto with init share|] end.

(*Ltac cancel_for_forward_spawn :=
  eapply symbolic_cancel_setup;
   [ construct_fold_right_sepcon
   | construct_fold_right_sepcon
   | fold_abnormal_mpred
   | cbv beta iota delta [before_symbol_cancel]; cancel_for_forward_call].*)

Ltac go_lower1 := rewrite ENTAIL_refl; apply remove_PROP_LOCAL_left';
  split => rho; rewrite !monPred_at_embed.

Ltac forward_spawn id arg wit :=
  lazymatch goal with gv : globals |- _ =>
  make_func_ptr id; let f := fresh "f_" in set (f := gv id);
  lazymatch goal with |- context[func_ptr (NDmk_funspec ?sig ?cc (val * ?A) ?Pre ?Post) f] =>
    let Q := fresh "Q" in let R := fresh "R" in
    evar (Q : A -> globals); evar (R : A -> val -> mpred);
    gather_SEP (func_ptr _ f); replace_SEP 0 (func_ptr (NDmk_funspec sig cc (val * A)
      (fun '(a, w) => PROPx [] (PARAMSx (a::nil) (GLOBALSx ((Q w) :: nil) (SEPx [R w a])))) Post) f);
    [ go_lower1; apply func_ptr_pre; let x := fresh "x" in intros (?, x);
        instantiate (1 := fun w a => _ w) in (value of R);
        repeat (destruct x as (x, ?);
        instantiate (1 := fun '(a, b) => _ a) in (value of Q);
        instantiate (1 := fun '(a, b) => _ a) in (value of R));
        rewrite PROP_into_SEP_LAMBDA; do 3 f_equiv;
        [ instantiate (1 := fun _ => _) in (value of Q); subst Q; f_equiv; simpl; reflexivity
        | unfold SEPx; f_equiv; simpl; rewrite !bi.sep_emp;
          unfold R; instantiate (1 := fun _ => _); simpl;
          reflexivity]
     |];
  forward_call (f, arg, existT(P := fun T => (T -> globals) * T * (T -> val -> mpred))%type A (Q, wit, R)); subst Q R;
           [ .. | subst f];
    [try (subst f; rewrite <- ?bi.sep_assoc; apply bi.sep_mono; [apply derives_refl|]).. |]
  end end.
