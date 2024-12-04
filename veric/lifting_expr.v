Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import VST.veric.juicy_base.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.juicy_mem_lemmas.
Require Import VST.veric.Clight_base.
Require Import VST.veric.Cop2.
Require Import VST.veric.Clight_seplog.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr.
Require Import VST.veric.binop_lemmas4.
Require Import VST.veric.expr_lemmas4.
Require Import VST.veric.valid_pointer.
Require Import VST.veric.env.
Import LiftNotation.

Section mpred.

Context `{!heapGS Σ} `{!envGS Σ} (ge : genv).

(* evaluate locals according to the current stack level *)
(* It would be neater to turn env_matches into an assert. *)
Definition wp_expr E e Φ : assert :=
  |={E}=> ∀ m rho, ⎡mem_auth m⎤ -∗ ⎡env_auth rho⎤ ={E}=∗
         ∃ v, <affine> assert_of (λ n, ⌜forall ve te,
            env_matches (env_to_environ rho n) ge ve te ->
            Clight.eval_expr ge ve te m e v (*/\ typeof e = t /\ tc_val t v*)⌝) ∗
         ⎡mem_auth m⎤ ∗ ⎡env_auth rho⎤ ∗ Φ v.

Definition wp_lvalue E e (Φ : address → assert) : assert :=
  |={E}=> ∀ m rho, ⎡mem_auth m⎤ -∗ ⎡env_auth rho⎤ ={E}=∗
         ∃ b o, <affine> assert_of (λ n, ⌜forall ve te,
            env_matches (env_to_environ rho n) ge ve te ->
            Clight.eval_lvalue ge ve te m e b o Full (*/\ typeof e = t /\ tc_val t v*)⌝) ∗
         ⎡mem_auth m⎤ ∗ ⎡env_auth rho⎤ ∗ Φ (b, Ptrofs.unsigned o).

Lemma fupd_wp_expr : forall E e P, (|={E}=> wp_expr E e P) ⊢ wp_expr E e P.
Proof. intros; apply fupd_trans. Qed.

Global Instance elim_modal_fupd_wp_expr p P E e Q :
  ElimModal Logic.True p false (|={E}=> P) P (wp_expr E e Q) (wp_expr E e Q).
Proof.
  by rewrite /ElimModal bi.intuitionistically_if_elim
    fupd_frame_r bi.wand_elim_r fupd_wp_expr.
Qed.

Lemma wp_expr_strong_mono : forall E e P1 P2, (∀ v, P1 v ={E}=∗ P2 v) ∗ wp_expr E e P1 ⊢ wp_expr E e P2.
Proof.
  intros; rewrite /wp_expr.
  iIntros "(HP & >H) !>" (??) "??".
  iMod ("H" with "[$] [$]") as (?) "(? & ? & ? & H)".
  iMod ("HP" with "H").
  iIntros "!>"; iExists _; iFrame.
Qed.

Lemma wp_expr_mono : forall E e P1 P2, (∀ v, P1 v ⊢ |={E}=> P2 v) → wp_expr E e P1 ⊢ wp_expr E e P2.
Proof.
  intros; iIntros; iApply wp_expr_strong_mono; iFrame.
  by iIntros (?) "?"; iApply H.
Qed.

Global Instance wp_expr_proper E e : Proper (pointwise_relation _ base.equiv ==> base.equiv) (wp_expr E e).
Proof. solve_proper. Qed.

Lemma wp_expr_mask_mono : forall E E' e P, E ⊆ E' → wp_expr E e P ⊢ wp_expr E' e P.
Proof.
  intros; rewrite /wp_expr.
  iIntros "H"; iMod (fupd_mask_subseteq E) as "Hclose"; first done.
  iMod "H"; iMod "Hclose" as "_".
  iIntros "!>" (??) "??".
  iMod (fupd_mask_subseteq E) as "Hclose"; first done.
  iMod ("H" with "[$] [$]") as "H"; iMod "Hclose".
  iApply "H".
Qed.

Lemma wp_expr_frame : forall E e P Q, P ∗ wp_expr E e Q ⊢ wp_expr E e (λ v, P ∗ Q v).
Proof.
  intros; rewrite /wp_expr.
  iIntros "($ & $)".
Qed.

Lemma fupd_wp_lvalue : forall E e P, (|={E}=> wp_lvalue E e P) ⊢ wp_lvalue E e P.
Proof. intros; apply fupd_trans. Qed.

Global Instance elim_modal_fupd_wp_lvalue p P E e Q :
  ElimModal Logic.True p false (|={E}=> P) P (wp_lvalue E e Q) (wp_lvalue E e Q).
Proof.
  by rewrite /ElimModal bi.intuitionistically_if_elim
    fupd_frame_r bi.wand_elim_r fupd_wp_lvalue.
Qed.

Lemma wp_lvalue_strong_mono : forall E e P1 P2, (∀ v, P1 v ={E}=∗ P2 v) ∗ wp_lvalue E e P1 ⊢ wp_lvalue E e P2.
Proof.
  intros; rewrite /wp_lvalue.
  iIntros "(HP & >H) !>" (??) "??".
  iMod ("H" with "[$] [$]") as (??) "(? & ? & ? & H)".
  iMod ("HP" with "H").
  iIntros "!>"; iExists _; iFrame.
Qed.

Lemma wp_lvalue_mono : forall E e P1 P2, (∀ v, P1 v ⊢ |={E}=> P2 v) → wp_lvalue E e P1 ⊢ wp_lvalue E e P2.
Proof.
  intros; iIntros; iApply wp_lvalue_strong_mono; iFrame.
  by iIntros (?) "?"; iApply H.
Qed.

Global Instance wp_lvalue_proper E e : Proper (pointwise_relation _ base.equiv ==> base.equiv) (wp_lvalue E e).
Proof. solve_proper. Qed.

Lemma wp_lvalue_mask_mono : forall E E' e P, E ⊆ E' → wp_lvalue E e P ⊢ wp_lvalue E' e P.
Proof.
  intros; rewrite /wp_lvalue.
  iIntros "H"; iMod (fupd_mask_subseteq E) as "Hclose"; first done.
  iMod "H"; iMod "Hclose" as "_".
  iIntros "!>" (??) "??".
  iMod (fupd_mask_subseteq E) as "Hclose"; first done.
  iMod ("H" with "[$] [$]") as "H"; iMod "Hclose".
  iApply "H".
Qed.

Lemma wp_lvalue_frame : forall E e P Q, P ∗ wp_lvalue E e Q ⊢ wp_lvalue E e (λ v, P ∗ Q v).
Proof.
  intros; rewrite /wp_lvalue.
  iIntros "($ & $)".
Qed.

(* rules *)
Lemma wp_const_int E i t P:
  P (Vint i) ⊢ wp_expr E (Econst_int i t) P.
Proof.
  rewrite /wp_expr.
  iIntros "? !> %% ?? !>".
  iFrame.
  iIntros "!>"; iStopProof; split => ?; monPred.unseal; apply bi.pure_intro.
  intros; constructor.
Qed.

Lemma wp_const_long E i t P:
  P (Vlong i)
  ⊢ wp_expr E (Econst_long i t) P.
Proof.
  rewrite /wp_expr.
  iIntros "? !> %% ?? !>".
  iFrame.
  iIntros "!>"; iStopProof; split => ?; monPred.unseal; apply bi.pure_intro.
  intros; constructor.
Qed.

Lemma wp_const_float E i t P:
  P (Vfloat i)
  ⊢ wp_expr E (Econst_float i t) P.
Proof.
  rewrite /wp_expr.
  iIntros "? !> %% ?? !>".
  iFrame.
  iIntros "!>"; iStopProof; split => ?; monPred.unseal; apply bi.pure_intro.
  intros; constructor.
Qed.

Lemma wp_const_single E i t P:
  P (Vsingle i)
  ⊢ wp_expr E (Econst_single i t) P.
Proof.
  rewrite /wp_expr.
  iIntros "? !> %% ?? !>".
  iFrame.
  iIntros "!>"; iStopProof; split => ?; monPred.unseal; apply bi.pure_intro.
  intros; constructor.
Qed.

(* Caesium uses a small-step semantics for exprs, so the wp/typing for an operation can be broken up into
   evaluating the arguments and then the op. Clight uses big-step and can't in general inject vals
   into expr, so for now, hacking in a different wp judgment for ops. *)
Definition wp_binop E op t1 v1 t2 v2 Φ : assert :=
  |={E}=> ∀ m, ⎡mem_auth m⎤ ={E}=∗
         ∃ v, ⌜sem_binary_operation (genv_cenv ge) op v1 t1 v2 t2 m = Some v (*/\ typeof e = t /\ tc_val t v*)⌝ ∧
         ⎡mem_auth m⎤ ∗ Φ v.

Lemma fupd_wp_binop : forall E op t1 v1 t2 v2 P, (|={E}=> wp_binop E op t1 v1 t2 v2 P) ⊢ wp_binop E op t1 v1 t2 v2 P.
Proof. intros; apply fupd_trans. Qed.

Global Instance elim_modal_fupd_wp_binop p P E op t1 v1 t2 v2 Q :
  ElimModal Logic.True p false (|={E}=> P) P (wp_binop E op t1 v1 t2 v2 Q) (wp_binop E op t1 v1 t2 v2 Q).
Proof.
  by rewrite /ElimModal bi.intuitionistically_if_elim
    fupd_frame_r bi.wand_elim_r fupd_wp_binop.
Qed.

Lemma wp_binop_rule : forall E e1 e2 Φ o t, wp_expr E e1 (λ v1, wp_expr E e2 (λ v2, wp_binop E o (typeof e1) v1 (typeof e2) v2 Φ))
  ⊢ wp_expr E (Ebinop o e1 e2 t) Φ.
Proof.
  intros.
  rewrite /wp_expr /wp_binop.
  iIntros ">H !>" (??) "Hm ?".
  iMod ("H" with "Hm [$]") as "(%v1 & H1 & Hm & ? & >H)".
  iMod ("H" with "Hm [$]") as "(%v2 & H2 & Hm & ? & >H)".
  iMod ("H" with "Hm") as "(%v & %H & Hm & ?)".
  iIntros "!>"; iExists _; iFrame.
  iStopProof; split => ?; monPred.unseal; rewrite !monPred_at_affinely.
  iIntros "(% & %)"; iPureIntro; intros; econstructor; eauto.
Qed.

Definition blocks_match op v1 v2 :=
match op with Cop.Olt | Cop.Ogt | Cop.Ole | Cop.Oge =>
  match v1, v2 with
    Vptr b _, Vptr b2 _ => b=b2
    | _, _ => False%type
  end
| _ => True%type
end.

Lemma mapsto_valid_pointer : forall {CS : compspecs} b o sh t m,
  sh <> Share.bot ->
  mem_auth m ∗ mapsto_ sh t (Vptr b o) ⊢
  ⌜Mem.valid_pointer m b (Ptrofs.unsigned o) = true⌝.
Proof.
intros; iIntros "[Hm H]".
iAssert ⌜exists ch, access_mode t = By_value ch⌝ with "[H]" as %(ch & Hch).
{ rewrite /mapsto_ /mapsto.
  destruct (access_mode t) eqn: ?; try done.
  destruct (type_is_volatile t) eqn: ?; try done.
  eauto. }
iMod (mapsto_valid_pointer1 with "H") as "H"; simpl; try done.
{ instantiate (1 := 0); pose proof (Ptrofs.unsigned_range o); lia. }
{ rewrite /sizeof (size_chunk_sizeof _ _ _ Hch).
  pose proof (size_chunk_pos ch); lia. }
iDestruct (valid_pointer_dry with "[$Hm $H]") as %Hvalid.
by rewrite Z.add_0_r Ptrofs.add_zero in Hvalid.
Qed.

Lemma cmplu_bool_true : forall f cmp v1 v2 v, Val.cmplu_bool f cmp v1 v2 = Some v ->
  Val.cmplu_bool true2 cmp v1 v2 = Some v.
Proof.
  rewrite /Val.cmplu_bool; intros.
  destruct v1; try done; destruct v2; try done; simple_if_tac; try done;
    repeat match goal with H : (if ?b then _ else _) = Some _ |- _ => destruct b eqn: ?Hb; try done end;
    apply andb_prop in Hb as [-> _]; auto.
Qed.

Lemma cmpu_bool_true : forall f cmp v1 v2 v, Val.cmpu_bool f cmp v1 v2 = Some v ->
  Val.cmpu_bool true2 cmp v1 v2 = Some v.
Proof.
  rewrite /Val.cmpu_bool; intros.
  destruct v1; try done; destruct v2; try done; simple_if_tac; try done;
    repeat match goal with H : (if ?b then _ else _) = Some _ |- _ => destruct b eqn: ?Hb; try done end;
    apply andb_prop in Hb as [-> _]; auto.
Qed.

Lemma option_map_Some : forall {A B} (f : A -> B) a b, option_map f a = Some b ->
  exists a', a = Some a' /\ f a' = b.
Proof.
  destruct a; inversion 1; eauto.
Qed.

Lemma wp_pointer_cmp: forall {CS : compspecs} E (cmp : Cop.binary_operation) ty1 ty2 v1 v2 sh1 sh2 P,
  expr.is_comparison cmp = true ->
  tc_val ty1 v1 -> tc_val ty2 v2 ->
  eqb_type ty1 int_or_ptr_type = false ->
  eqb_type ty2 int_or_ptr_type = false ->
  sh1 <> Share.bot -> sh2 <> Share.bot ->
  blocks_match cmp v1 v2 ->
  ▷ ⎡<absorb> mapsto_ sh1 ty1 v1 ∧ <absorb> mapsto_ sh2 ty2 v2⎤ ∧
  (∀ v, <affine> ⌜classify_cmp ty1 ty2 = cmp_case_pp ∧ sem_cmp_pp (op_to_cmp cmp) v1 v2 = Some v⌝ -∗ P v) ⊢
  wp_binop E cmp ty1 v1 ty2 v2 P.
Proof.
  intros; rewrite /wp_binop.
  iIntros "H !>" (?) "Hm".
  rewrite -embed_later bi.later_and !bi.later_absorbingly embed_and !embed_absorbingly.
  iCombine "H Hm" as "H".
  iDestruct (add_and _ (▷ ⌜∃ ch b o, access_mode ty1 = By_value ch ∧ v1 = Vptr b o ∧ Mem.valid_pointer m b (Ptrofs.unsigned o) = true⌝)
    with "H") as "(H & >%Hv1)".
  { iIntros "(((>H & _) & _) & Hm) !>".
    iDestruct (mapsto_pure_facts with "H") as %((? & ?) & ?).
    destruct v1; try contradiction.
    iDestruct (mapsto_valid_pointer with "[$]") as %?; eauto 7. }
  destruct Hv1 as (ch1 & b1 & o1 & ? & Hv1 & MT_1).
  iDestruct (add_and _ (▷ ⌜∃ ch b o, access_mode ty2 = By_value ch ∧ v2 = Vptr b o ∧ Mem.valid_pointer m b (Ptrofs.unsigned o) = true⌝)
    with "H") as "((H & Hm) & >%Hv2)".
  { iIntros "(((_ & >H) & _) & Hm) !>".
    iDestruct (mapsto_pure_facts with "H") as %((? & ?) & ?).
    destruct v2; try contradiction.
    iDestruct (mapsto_valid_pointer with "[$]") as %?; eauto 7. }
  destruct Hv2 as (ch2 & b2 & o2 & ? & Hv2 & MT_2).
  assert (classify_cmp ty1 ty2 = cmp_case_pp) as Hcase.
  { subst; destruct ty1; try solve [simpl in *; try destruct f; try tauto; congruence].
    destruct ty2; try solve [simpl in *; try destruct f; try tauto; congruence]. }
  assert (exists v, sem_binary_operation ge cmp v1 ty1 v2 ty2 m = Some v) as (v & Hv).
  { rewrite /sem_binary_operation /Cop.sem_cmp Hcase.
    rewrite /cmp_ptr /Val.cmpu_bool /Val.cmplu_bool Hv1 Hv2 MT_1 MT_2 /=.
    rewrite bool2val_eq.
    destruct cmp; try discriminate; subst; simpl; destruct Archi.ptr64 eqn:Hp;
      try rewrite -> if_true by auto;
      try solve [if_tac; subst; eauto]; rewrite ?peq_true; simpl; eauto. }
  iExists v; iFrame.
  iIntros "!>"; iSplit; first done.
  iApply "H"; iPureIntro.
  rewrite /sem_binary_operation /Cop.sem_cmp Hcase /cmp_ptr in Hv; rewrite /sem_cmp_pp -bool2val_eq.
  destruct cmp; try done; simple_if_tac; apply option_map_Some in Hv as (? & Hv & <-); simpl;
    first [by apply cmplu_bool_true in Hv as -> | by apply cmpu_bool_true in Hv as ->].
Qed.

Definition wp_unop E op t1 v1 Φ : assert :=
  |={E}=> ∀ m, ⎡mem_auth m⎤ ={E}=∗
         ∃ v, ⌜Cop.sem_unary_operation op v1 t1 m = Some v⌝ ∧
         ⎡mem_auth m⎤ ∗ Φ v.

Lemma fupd_wp_unop : forall E op t1 v1 P, (|={E}=> wp_unop E op t1 v1 P) ⊢ wp_unop E op t1 v1 P.
Proof. intros; apply fupd_trans. Qed.

Global Instance elim_modal_fupd_wp_unop p P E op t1 v1 Q :
  ElimModal Logic.True p false (|={E}=> P) P (wp_unop E op t1 v1 Q) (wp_unop E op t1 v1 Q).
Proof.
  by rewrite /ElimModal bi.intuitionistically_if_elim
    fupd_frame_r bi.wand_elim_r fupd_wp_unop.
Qed.

Lemma wp_unop_rule : forall E e Φ o t, wp_expr E e (λ v, wp_unop E o (typeof e) v Φ)
  ⊢ wp_expr E (Eunop o e t) Φ.
Proof.
  intros.
  rewrite /wp_expr /wp_binop.
  iIntros ">H !>" (??) "Hm ?".
  iMod ("H" with "Hm [$]") as "(%v1 & H1 & Hm & ? & >H)".
  iMod ("H" with "Hm") as "(%v & %H & Hm & ?)".
  iIntros "!>"; iExists _; iFrame.
  iStopProof; split => ?; rewrite !monPred_at_affinely; iIntros (?).
  iPureIntro; intros; econstructor; eauto.
Qed.

Lemma wp_cast : forall E e ty P, expr_lemmas4.cast_pointer_to_bool (typeof e) ty = false ->
  wp_expr E e (λ v, ⌜tc_val (typeof e) v⌝ ∧ ∃ v', ⌜sem_cast (typeof e) ty v = Some v'⌝ ∧ P v') ⊢ wp_expr E (Ecast e ty) P.
Proof.
  intros; rewrite /wp_expr.
  do 8 f_equiv. iIntros "(% & ? & Hm & ? & % & %v' & %Hcast & P)".
  iExists v'; iFrame.
  iStopProof; split => ?; rewrite !monPred_at_affinely; iIntros (?).
  iPureIntro; intros; econstructor; eauto.
  by apply expr_lemmas4.sem_cast_e1.
Qed.

Lemma wp_tempvar_local : forall E _x x c_ty P,
  temp _x x ∗ (temp _x x -∗ P x)
  ⊢ wp_expr E (Etempvar _x c_ty) P.
Proof.
  split => n; rewrite /wp_expr; monPred.unseal.
  iIntros "[H HP] !>" (??? <-). iIntros "Hm" (? <-) "Hr !>".
  iDestruct (temp_e with "[$H $Hr]") as %H.
  iSpecialize ("HP" with "[%] H"); first done.
  iExists _; iFrame. rewrite monPred_at_affinely; iPureIntro.
  intros ?? (? & ? & Hte); rewrite -Hte in H.
  by constructor.
Qed.

Lemma wp_var_local : forall E _x c_ty b (P:address->assert),
  lvar _x c_ty b ∗ (lvar _x c_ty b -∗ P (b, 0))
  ⊢ wp_lvalue E (Evar _x c_ty) P.
Proof.
  split => n; rewrite /wp_lvalue; monPred.unseal.
  iIntros "[H HP] !>" (??? <-). iIntros "Hm" (? <-) "Hr !>".
  iDestruct (lvar_e with "[$H $Hr]") as %H.
  iSpecialize ("HP" with "[%] H"); first done.
  change 0 with (Ptrofs.unsigned Ptrofs.zero).
  iExists _, _; iFrame. rewrite monPred_at_affinely; iPureIntro.
  intros ?? (? & Hve & ?); rewrite -Hve in H.
  by constructor.
Qed.

Lemma wp_var_global : forall E _x c_ty b (P:address->assert),
  ⎡gvar _x b⎤ ∗ (⎡gvar _x b⎤ -∗ P (b, 0))
  ⊢ wp_lvalue E (Evar _x c_ty) P.
Proof.
  split => n; rewrite /wp_lvalue; monPred.unseal.
  iIntros "[H HP] !>" (??? <-). iIntros "Hm" (? <-) "Hr !>".
  iDestruct (gvar_e with "[$H $Hr]") as %H.
  iSpecialize ("HP" with "[%] H"); first done.
  change 0 with (Ptrofs.unsigned Ptrofs.zero).
  iExists _, _; iFrame. rewrite monPred_at_affinely; iPureIntro.
  intros ?? (Hge & ? & ?); rewrite -Hge in H.
  by constructor.
Qed.

Lemma wp_deref : forall E e ty P,
  wp_expr E e (λ v, ∃ b o, ⌜v = Vptr b o⌝ ∧ P (b, Ptrofs.unsigned o)) ⊢ wp_lvalue E (Ederef e ty) P.
Proof.
  intros; rewrite /wp_lvalue /wp_expr.
  do 8 f_equiv.
  iIntros "(% & ? & ? & ? & %b & %o & % & ?)"; iExists b, o; iFrame.
  iStopProof; split => ?; rewrite !monPred_at_affinely; iIntros (?).
  iPureIntro; intros; subst; econstructor; eauto.
Qed.

Lemma wp_expr_byref : forall E e P, access_mode (typeof e) = By_reference →
  wp_lvalue E e (λ '(b, o), P (Vptr b (Ptrofs.repr o))) ⊢ wp_expr E e P.
Proof.
  intros; rewrite /wp_lvalue /wp_expr.
  do 8 f_equiv.
  iIntros "(% & % & ? & $)".
  iStopProof; split => ?; rewrite !monPred_at_affinely; iIntros (?).
  iPureIntro; intros; econstructor; eauto.
  rewrite Ptrofs.repr_unsigned; constructor; auto.
Qed.

Lemma wp_expr_mapsto : forall E e P,
  wp_lvalue E e (λ '(b, o), ∃ sh v, ⌜readable_share sh ∧ v ≠ Vundef⌝ ∧
    ⎡▷ <absorb> mapsto sh (typeof e) (Vptr b (Ptrofs.repr o)) v⎤ ∧ P v) ⊢
  wp_expr E e P.
Proof.
  intros; rewrite /wp_lvalue /wp_expr.
  f_equiv. iIntros "H" (m ?) "Hm ?".
  iDestruct ("H" with "Hm [$]") as ">(% & % & ? & Hm & ? & % & % & (% & %) & H)".
  rewrite Ptrofs.repr_unsigned bi.later_absorbingly embed_absorbingly.
  iCombine "H Hm" as "H".
  iDestruct (add_and _ (▷ ⌜∃ ch, access_mode (typeof e) = By_value ch⌝) with "H") as "(H & >(%ch & %Hch))".
  { iIntros "((>H & _) & Hm) !>".
    by iDestruct (mapsto_pure_facts with "H") as %(? & _). }
  iDestruct (add_and _ (▷ ⌜load ch m b (Ptrofs.unsigned o) = Some v⌝) with "H") as "((H & Hm) & >%Hload)".
  { iIntros "((>H & _) & Hm) !>"; iDestruct (core_load_load' with "[$Hm H]") as %?; last done.
    rewrite mapsto_core_load //. }
  rewrite bi.and_elim_r.
  iModIntro; iExists v; iFrame.
  iStopProof; split => ?; rewrite !monPred_at_affinely; iIntros (?).
  iPureIntro; intros; econstructor; eauto.
  econstructor; eauto.
Qed.

End mpred.
