Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import VST.veric.juicy_base.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.Clight_base.
Require Import VST.veric.Clight_seplog.
Require Import VST.veric.tycontext.
Import LiftNotation.

Global Instance local_absorbing `{!heapGS Σ} l : Absorbing (local l).
Proof.
  rewrite /local; apply monPred_absorbing, _.
Qed.

Global Instance local_persistent `{!heapGS Σ} l : Persistent (local l).
Proof.
  rewrite /local; apply monPred_persistent, _.
Qed.

Section mpred.

Context `{!heapGS Σ}.

Definition wp_expr E e Φ : assert :=
  |={E}=> ∀ m, ⎡mem_auth m⎤ ={E}=∗
         ∃ v, local (λ rho, forall ge ve te,
            rho = construct_rho (filter_genv ge) ve te ->
            Clight.eval_expr ge ve te m e v (*/\ typeof e = t /\ tc_val t v*)) ∧
         ⎡mem_auth m⎤ ∗ Φ v.

Definition wp_lvalue E e (Φ : address → assert) : assert :=
  |={E}=> ∀ m, ⎡mem_auth m⎤ ={E}=∗
         ∃ b o, local (λ rho, forall ge ve te,
            rho = construct_rho (filter_genv ge) ve te ->
            Clight.eval_lvalue ge ve te m e b o Full (*/\ typeof e = t /\ tc_val t v*)) ∧
         ⎡mem_auth m⎤ ∗ Φ (b, Ptrofs.unsigned o).

Lemma fupd_wp_expr : forall E e P, (|={E}=> wp_expr E e P) ⊢ wp_expr E e P.
Proof. intros; apply fupd_trans. Qed.

Global Instance elim_modal_fupd_wp_expr p P E e Q :
  ElimModal Logic.True p false (|={E}=> P) P (wp_expr E e Q) (wp_expr E e Q).
Proof.
  by rewrite /ElimModal bi.intuitionistically_if_elim
    fupd_frame_r bi.wand_elim_r fupd_wp_expr.
Qed.

Lemma wp_expr_mono : forall E e P1 P2, (∀ v, P1 v ⊢ |={E}=> P2 v) → wp_expr E e P1 ⊢ wp_expr E e P2.
Proof.
  intros; rewrite /wp_expr.
  iIntros ">H !>" (?) "Hm".
  iMod ("H" with "Hm") as (?) "(? & ? & H)".
  rewrite H; iMod "H".
  iIntros "!>"; iExists _; iFrame.
Qed.

Lemma fupd_wp_lvalue : forall E e P, (|={E}=> wp_lvalue E e P) ⊢ wp_lvalue E e P.
Proof. intros; apply fupd_trans. Qed.

Global Instance elim_modal_fupd_wp_lvalue p P E e Q :
  ElimModal Logic.True p false (|={E}=> P) P (wp_lvalue E e Q) (wp_lvalue E e Q).
Proof.
  by rewrite /ElimModal bi.intuitionistically_if_elim
    fupd_frame_r bi.wand_elim_r fupd_wp_lvalue.
Qed.

Lemma wp_lvalue_mono : forall E e P1 P2, (∀ v, P1 v ⊢ |={E}=> P2 v) → wp_lvalue E e P1 ⊢ wp_lvalue E e P2.
Proof.
  intros; rewrite /wp_lvalue.
  iIntros ">H !>" (?) "Hm".
  iMod ("H" with "Hm") as (??) "(? & ? & H)".
  rewrite H; iMod "H".
  iIntros "!>"; iExists _; iFrame.
Qed.

(* rules *)
Lemma wp_const_int E i t P:
  P (Vint i) ⊢ wp_expr E (Econst_int i t) P.
Proof.
  rewrite /wp_expr.
  iIntros "? !> % Hm !>".
  iFrame.
  iSplit; last done.
  iStopProof; split => rho; monPred.unseal.
  apply bi.pure_intro; constructor.
Qed.

Lemma wp_const_long E i t P:
  P (Vlong i)
  ⊢ wp_expr E (Econst_long i t) P.
Proof.
  rewrite /wp_expr.
  iIntros "? !> % Hm !>".
  iFrame.
  iSplit; last done.
  iStopProof; split => rho; monPred.unseal.
  apply bi.pure_intro; constructor.
Qed.

Lemma wp_const_float E i t P:
  P (Vfloat i)
  ⊢ wp_expr E (Econst_float i t) P.
Proof.
  rewrite /wp_expr.
  iIntros "? !> % Hm !>".
  iFrame.
  iSplit; last done.
  iStopProof; split => rho; monPred.unseal.
  apply bi.pure_intro; constructor.
Qed.

Lemma wp_const_single E i t P:
  P (Vsingle i)
  ⊢ wp_expr E (Econst_single i t) P.
Proof.
  rewrite /wp_expr.
  iIntros "? !> % Hm !>".
  iFrame.
  iSplit; last done.
  iStopProof; split => rho; monPred.unseal.
  apply bi.pure_intro; constructor.
Qed.

(* Caesium uses a small-step semantics for exprs, so the wp/typing for an operation can be broken up into
   evaluating the arguments and then the op. Clight uses big-step and can't in general inject vals
   into expr, so for now, hacking in a different wp judgment for ops. *)
Definition wp_binop E op t1 v1 t2 v2 Φ : assert :=
  |={E}=> ∀ m, ⎡mem_auth m⎤ ={E}=∗
         ∃ v, local (λ rho, forall ge ve te,
            rho = construct_rho (filter_genv ge) ve te ->
            sem_binary_operation (genv_cenv ge) op v1 t1 v2 t2 m = Some v (*/\ typeof e = t /\ tc_val t v*)) ∧
         ⎡mem_auth m⎤ ∗ Φ v.

Lemma wp_binop_rule : forall E e1 e2 Φ o t, wp_expr E e1 (λ v1, wp_expr E e2 (λ v2, wp_binop E o (typeof e1) v1 (typeof e2) v2 Φ))
  ⊢ wp_expr E (Ebinop o e1 e2 t) Φ.
Proof.
  intros.
  rewrite /wp_expr /wp_binop.
  iIntros ">H !>" (?) "Hm".
  iMod ("H" with "Hm") as "(%v1 & H1 & Hm & >H)".
  iMod ("H" with "Hm") as "(%v2 & H2 & Hm & >H)".
  iMod ("H" with "Hm") as "(%v & H & Hm & ?)".
  iIntros "!>"; iExists _; iFrame.
  iStopProof; split => rho; monPred.unseal.
  rewrite !monPred_at_affinely /local /lift1 /=.
  iIntros "(%H1 & %H2 & %H)"; iPureIntro.
  split; auto; intros; econstructor; eauto.
Qed.

Definition wp_unop E op t1 v1 Φ : assert :=
  |={E}=> ∀ m, ⎡mem_auth m⎤ ={E}=∗
         (* unops don't use the environment *)
         ∃ v, ⌜Cop.sem_unary_operation op v1 t1 m = Some v⌝ ∧
         ⎡mem_auth m⎤ ∗ Φ v.

Lemma wp_unop_rule : forall E e Φ o t, wp_expr E e (λ v, wp_unop E o (typeof e) v Φ)
  ⊢ wp_expr E (Eunop o e t) Φ.
Proof.
  intros.
  rewrite /wp_expr /wp_binop.
  iIntros ">H !>" (?) "Hm".
  iMod ("H" with "Hm") as "(%v1 & H1 & Hm & >H)".
  iMod ("H" with "Hm") as "(%v & H & Hm & ?)".
  iIntros "!>"; iExists _; iFrame.
  iStopProof; split => rho; monPred.unseal.
  rewrite !monPred_at_affinely /local /lift1 /=.
  iIntros "(%H1 & %H)"; iPureIntro.
  split; auto; intros; econstructor; eauto.
Qed.

Definition globals := ident -> val.

Inductive localdef : Type :=
 | temp: ident -> val -> localdef
 | lvar: ident -> type -> val -> localdef   (* local variable *)
 | gvars: globals -> localdef.              (* global variables *)

Arguments temp i%_positive v.

Definition lvar_denote (i: ident) (t: type) (v: val) rho :=
     match Map.get (ve_of rho) i with
         | Some (b, ty') => t=ty' /\ v = Vptr b Ptrofs.zero
         | None => False%type
         end.

Definition gvars_denote (gv: globals) rho :=
   gv = (fun i => match Map.get (ge_of rho) i with Some b => Vptr b Ptrofs.zero | None => Vundef end).

Definition locald_denote (d: localdef) : environ -> Prop :=
 match d with
 | temp i v => `and (`(eq v) (eval_id i)) `(v <> Vundef)
 | lvar i t v => lvar_denote i t v
 | gvars gv => gvars_denote gv
 end.

Lemma wp_tempvar_local : forall E _x x c_ty P,
  <affine> (local $ locald_denote $ temp _x x) ∗ P x 
  ⊢ wp_expr E (Etempvar _x c_ty) P.
Proof.
  intros. rewrite /wp_expr /=.
  iIntros "[H HP] !>" (?) "Hm !>".
  iExists _; iFrame. iSplit; [|done].
  rewrite bi.affinely_elim.
  iStopProof; split => rho.
  rewrite /local /lift1 /=.
  iIntros "[% %]" (????).
  iPureIntro. econstructor.
  unfold eval_id in H.
  super_unfold_lift; subst; simpl in *.
  unfold Map.get, make_tenv in *.
  destruct (_ !! _); done.
Qed.

Lemma wp_var_local : forall E _x c_ty (lv:val) (T:address->assert),
  <affine> (local $ locald_denote $ lvar _x c_ty lv) ∗
  (∃ l, <affine> ⌜Some l = val2address lv⌝ ∗
  T l)
  ⊢ wp_lvalue E (Evar _x c_ty) T.
Proof.
  intros. subst. rewrite /wp_lvalue  /=.
  iIntros "(Hl & [%l [% HT]]) !>" (m) "Hm !>".
  iStopProof. split => rho; monPred.unseal.
  rewrite !monPred_at_affinely /=.
  iIntros "(%Hvar & H & ?)".
  unfold lvar_denote in Hvar.
  destruct (Map.get (ve_of rho) _x) eqn: Hve; [|done].
  destruct p. destruct Hvar.
  rewrite H1 in H. inversion H.
  iExists _, _; iFrame.
  iPureIntro. split; last done; intros; subst.
  apply eval_Evar_local. apply Hve.
Qed.

End mpred.
