Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import VST.veric.juicy_base.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.juicy_mem_lemmas.
Require Import VST.veric.Clight_base.
Require Import VST.veric.Cop2.
Require Import VST.veric.mapsto_memory_block.
Require Import VST.veric.seplog.
Require Import VST.veric.tycontext.
Require Import VST.veric.valid_pointer.
Require Import VST.veric.expr.
Require Import VST.veric.env.

Section mpred.

Context `{!heapGS Σ} `{!envGS Σ} (ge : genv).
(* We could provide only a composite_env here, which would theoretically allow
   us to allocate new global variables during a proof, but Clight doesn't allow that.
   Might be worth it anyway for compositionality. *)

Lemma make_tycontext_v_lookup : forall tys id t,
  make_tycontext_v tys !! id = Some t -> In (id, t) tys.
Proof.
  intros ???; induction tys; simpl.
  - rewrite PTree.gempty //.
  - destruct a as (i, ?).
    destruct (eq_dec id i).
    + subst; rewrite PTree.gss.
      inversion 1; auto.
    + rewrite PTree.gso //; auto.
Qed.

Lemma make_tycontext_v_sound : forall tys id t, list_norepet (map fst tys) ->
  make_tycontext_v tys !! id = Some t <-> In (id, t) tys.
Proof.
  intros; split; first apply make_tycontext_v_lookup.
  induction tys; simpl; first done.
  intros [-> | ?].
  - apply PTree.gss.
  - destruct a; inv H.
    rewrite PTree.gso; auto.
    intros ->.
    contradiction H3; rewrite in_map_iff; eexists (_, _); eauto.
Qed.

Definition match_venv (ve: venviron) (vars: list (ident * type)) :=
 forall id, match lookup id ve with Some (b,t) => In (id,t) vars | _ => True end.

Lemma typecheck_var_match_venv : forall ve tys,
  typecheck_var_environ ve (make_tycontext_v tys) → match_venv ve tys.
Proof.
  unfold typecheck_var_environ, match_venv; intros.
  destruct (lookup id ve) as [(?, ty)|] eqn: Hid; last done.
  destruct (H id ty) as [_ Hty].
  apply make_tycontext_v_lookup, Hty; eauto.
Qed.

Definition make_env {A} (ve : PTree.t A) : gmap ident A :=
  PTree.fold (fun e i v => <[i := v]>e) ve ∅.

Lemma make_env_spec : forall {A} (ve : PTree.t A) i, lookup i (make_env ve) = PTree.get i ve.
Proof.
  intros; unfold make_env.
  eapply PTree_Properties.fold_ind.
  - intros; rewrite H //.
  - intros ?????? Hrem.
    destruct (eq_dec i k).
    + subst; rewrite lookup_insert //.
    + rewrite lookup_insert_ne //.
      rewrite PTree.gro // in Hrem.
Qed.

Definition stack_level (n : nat) : assert := <affine> monPred_in(I := stack_index) n.

Lemma stack_level_intro : ⊢ ∃ n, stack_level n.
Proof.
  by iDestruct (monPred_in_intro emp with "[]") as (?) "($ & _)".
Qed.

Lemma stack_level_elim : forall (P : assert) n, ⊢ stack_level n -∗ ⎡P n⎤ -∗ P.
Proof.
  intros; iIntros "#? H".
  iApply bi.impl_elim_r; iSplit; first iApply "H".
  by iApply monPred_in_elim.
Qed.

Lemma stack_level_embed : forall n (P : assert), ⊢ stack_level n -∗ P -∗ ⎡P n⎤.
Proof.
  split => ?; rewrite /stack_level; monPred.unseal.
  iIntros "_" (? [=]); rewrite monPred_at_affinely /=.
  iIntros ([=] ? [=]); subst; auto.
Qed.

Lemma stack_level_eq : forall a b, ⊢ stack_level a -∗ stack_level b -∗ ⌜a = b⌝.
Proof.
  split => n; rewrite /stack_level; monPred.unseal; setoid_rewrite monPred_at_affinely; simpl.
  iIntros; iPureIntro; congruence.
Qed.

Definition env_matches (rho : environ) (ge : genv) (ve : env) (te : temp_env) :=
  (forall i, Genv.find_symbol ge i = lookup i (ge_of rho)) /\
  (forall i, ve !! i = lookup i (ve_of rho)) /\
  (forall i, te !! i = lookup i (te_of rho)).

Definition env_match rho ge ve te := assert_of (λ n, ⌜env_matches (env_to_environ rho n) ge ve te⌝).

Global Instance env_match_persistent rho ge0 ve te : Persistent (env_match rho ge0 ve te).
Proof. apply monPred_persistent, _. Qed.

Lemma env_match_in : forall n rho ge ve te, ⊢ stack_level n -∗ env_match rho ge ve te -∗
  ⌜env_matches (env_to_environ rho n) ge ve te⌝.
Proof.
  intros; split => ?; rewrite /stack_level; monPred.unseal.
  iIntros "_" (? [=]).
  rewrite monPred_at_affinely; iIntros ([=] ? [=]); subst; auto.
Qed.

Lemma env_match_intro : forall n rho ge ve te, env_matches (env_to_environ rho n) ge ve te ->
  stack_level n ⊢ env_match rho ge ve te.
Proof.
  intros; split => ?; rewrite /stack_level; monPred.unseal; rewrite monPred_at_affinely.
  iIntros ([=]); subst; auto.
Qed.

(* evaluate locals according to the current stack level *)
(* f is used for only one purpose: to check whether function local variables
   shadow the names of global variables. *)
Definition wp_expr E f e Φ : assert :=
  |={E}=> ∀ m rho, ⎡mem_auth m⎤ -∗ ⎡env_auth rho⎤ ={E}=∗
         ∃ v, <affine> (∀ ve te, env_match rho ge ve te -∗
            ⌜match_venv (make_env ve) (fn_vars f) →
             Clight.eval_expr ge ve te m e v (*/\ typeof e = t /\ tc_val t v*)⌝) ∗
         ⎡mem_auth m⎤ ∗ ⎡env_auth rho⎤ ∗ Φ v.

Definition wp_lvalue E f e (Φ : address → assert) : assert :=
  |={E}=> ∀ m rho, ⎡mem_auth m⎤ -∗ ⎡env_auth rho⎤ ={E}=∗
         ∃ b o, <affine> (∀ ve te, env_match rho ge ve te -∗
            ⌜match_venv (make_env ve) (fn_vars f) →
            Clight.eval_lvalue ge ve te m e b o Full (*/\ typeof e = t /\ tc_val t v*)⌝) ∗
         ⎡mem_auth m⎤ ∗ ⎡env_auth rho⎤ ∗ Φ (b, Ptrofs.unsigned o).

Lemma fupd_wp_expr : forall E f e P, (|={E}=> wp_expr E f e P) ⊢ wp_expr E f e P.
Proof. intros; apply fupd_trans. Qed.

Global Instance elim_modal_fupd_wp_expr p P E f e Q :
  ElimModal Logic.True p false (|={E}=> P) P (wp_expr E f e Q) (wp_expr E f e Q).
Proof.
  by rewrite /ElimModal bi.intuitionistically_if_elim
    fupd_frame_r bi.wand_elim_r fupd_wp_expr.
Qed.

Lemma wp_expr_strong_mono : forall E f e P1 P2, (∀ v, P1 v ={E}=∗ P2 v) ∗ wp_expr E f e P1 ⊢ wp_expr E f e P2.
Proof.
  intros; rewrite /wp_expr.
  iIntros "(HP & >H) !>" (??) "??".
  iMod ("H" with "[$] [$]") as (?) "(? & ? & ? & H)".
  iMod ("HP" with "H").
  iIntros "!>"; iExists _; iFrame.
Qed.

Lemma wp_expr_mono : forall E e f P1 P2, (∀ v, P1 v ⊢ |={E}=> P2 v) → wp_expr E f e P1 ⊢ wp_expr E f e P2.
Proof.
  intros; iIntros; iApply wp_expr_strong_mono; iFrame.
  by iIntros (?) "?"; iApply H.
Qed.

Global Instance wp_expr_proper E f e : Proper (pointwise_relation _ base.equiv ==> base.equiv) (wp_expr E f e).
Proof. solve_proper. Qed.

Lemma wp_expr_mask_mono : forall E E' f e P, E ⊆ E' → wp_expr E f e P ⊢ wp_expr E' f e P.
Proof.
  intros; rewrite /wp_expr.
  iIntros "H"; iMod (fupd_mask_subseteq E) as "Hclose"; first done.
  iMod "H"; iMod "Hclose" as "_".
  iIntros "!>" (??) "??".
  iMod (fupd_mask_subseteq E) as "Hclose"; first done.
  iMod ("H" with "[$] [$]") as "H"; iMod "Hclose".
  iApply "H".
Qed.

Lemma wp_expr_frame : forall E f e P Q, P ∗ wp_expr E f e Q ⊢ wp_expr E f e (λ v, P ∗ Q v).
Proof.
  intros; rewrite /wp_expr.
  iIntros "($ & $)".
Qed.

Lemma fupd_wp_lvalue : forall E f e P, (|={E}=> wp_lvalue E f e P) ⊢ wp_lvalue E f e P.
Proof. intros; apply fupd_trans. Qed.

Global Instance elim_modal_fupd_wp_lvalue p P E f e Q :
  ElimModal Logic.True p false (|={E}=> P) P (wp_lvalue E f e Q) (wp_lvalue E f e Q).
Proof.
  by rewrite /ElimModal bi.intuitionistically_if_elim
    fupd_frame_r bi.wand_elim_r fupd_wp_lvalue.
Qed.

Lemma wp_lvalue_strong_mono : forall E f e P1 P2, (∀ v, P1 v ={E}=∗ P2 v) ∗ wp_lvalue E f e P1 ⊢ wp_lvalue E f e P2.
Proof.
  intros; rewrite /wp_lvalue.
  iIntros "(HP & >H) !>" (??) "??".
  iMod ("H" with "[$] [$]") as (??) "(? & ? & ? & H)".
  iMod ("HP" with "H").
  iIntros "!>"; iExists _; iFrame.
Qed.

Lemma wp_lvalue_mono : forall E f e P1 P2, (∀ v, P1 v ⊢ |={E}=> P2 v) → wp_lvalue E f e P1 ⊢ wp_lvalue E f e P2.
Proof.
  intros; iIntros; iApply wp_lvalue_strong_mono; iFrame.
  by iIntros (?) "?"; iApply H.
Qed.

Global Instance wp_lvalue_proper E f e : Proper (pointwise_relation _ base.equiv ==> base.equiv) (wp_lvalue E f e).
Proof. solve_proper. Qed.

Lemma wp_lvalue_mask_mono : forall E E' f e P, E ⊆ E' → wp_lvalue E f e P ⊢ wp_lvalue E' f e P.
Proof.
  intros; rewrite /wp_lvalue.
  iIntros "H"; iMod (fupd_mask_subseteq E) as "Hclose"; first done.
  iMod "H"; iMod "Hclose" as "_".
  iIntros "!>" (??) "??".
  iMod (fupd_mask_subseteq E) as "Hclose"; first done.
  iMod ("H" with "[$] [$]") as "H"; iMod "Hclose".
  iApply "H".
Qed.

Lemma wp_lvalue_frame : forall E e f P Q, P ∗ wp_lvalue E f e Q ⊢ wp_lvalue E f e (λ v, P ∗ Q v).
Proof.
  intros; rewrite /wp_lvalue.
  iIntros "($ & $)".
Qed.

(* rules *)
Lemma wp_const_int_fupd E f i t P:
  (|={E}=> P (Vint i)) ⊢ wp_expr E f (Econst_int i t) P.
Proof.
  rewrite /wp_expr; apply fupd_mono.
  iIntros "? %% ?? !>".
  iFrame.
  iIntros "!>" (??) "?"; iPureIntro; intros; constructor.
Qed.

Lemma wp_const_long_fupd E f i t P:
  (|={E}=> P (Vlong i)) ⊢ wp_expr E f (Econst_long i t) P.
Proof.
  rewrite /wp_expr; apply fupd_mono.
  iIntros "? %% ?? !>".
  iFrame.
  iIntros "!>" (??) "?"; iPureIntro; intros; constructor.
Qed.

Lemma wp_const_float_fupd E f i t P:
  (|={E}=> P (Vfloat i)) ⊢ wp_expr E f (Econst_float i t) P.
Proof.
  rewrite /wp_expr; apply fupd_mono.
  iIntros "? %% ?? !>".
  iFrame.
  iIntros "!>" (??) "?"; iPureIntro; intros; constructor.
Qed.

Lemma wp_const_single_fupd E f i t P:
  (|={E}=> P (Vsingle i)) ⊢ wp_expr E f (Econst_single i t) P.
Proof.
  rewrite /wp_expr; apply fupd_mono.
  iIntros "? %% ?? !>".
  iFrame.
  iIntros "!>" (??) "?"; iPureIntro; intros; constructor.
Qed.

Lemma wp_const_int E f i t P:
  P (Vint i) ⊢ wp_expr E f (Econst_int i t) P.
Proof.
  rewrite -wp_const_int_fupd; apply fupd_intro.
Qed.

Lemma wp_const_long E f i t P:
  P (Vlong i)
  ⊢ wp_expr E f (Econst_long i t) P.
Proof.
  rewrite -wp_const_long_fupd; apply fupd_intro.
Qed.

Lemma wp_const_float E f i t P:
  P (Vfloat i)
  ⊢ wp_expr E f (Econst_float i t) P.
Proof.
  rewrite -wp_const_float_fupd; apply fupd_intro.
Qed.

Lemma wp_const_single E f i t P:
  P (Vsingle i)
  ⊢ wp_expr E f (Econst_single i t) P.
Proof.
  rewrite -wp_const_single_fupd; apply fupd_intro.
Qed.

(* Caesium uses a small-step semantics for exprs, so the wp/typing for an operation can be broken up into
   evaluating the arguments and then the op. Clight uses big-step and can't in general inject vals
   into expr, so for now, hacking in a different wp judgment for ops. *)
Definition wp_binop E op t1 v1 t2 v2 Φ : assert :=
  |={E}=> ∀ m, ⎡mem_auth m⎤ ={E}=∗
         ∃ v, ⌜sem_binary_operation ge op v1 t1 v2 t2 m = Some v (*/\ typeof e = t /\ tc_val t v*)⌝ ∧
         ⎡mem_auth m⎤ ∗ Φ v.

Lemma fupd_wp_binop : forall E op t1 v1 t2 v2 P, (|={E}=> wp_binop E op t1 v1 t2 v2 P) ⊢ wp_binop E op t1 v1 t2 v2 P.
Proof. intros; apply fupd_trans. Qed.

Global Instance elim_modal_fupd_wp_binop p P E op t1 v1 t2 v2 Q :
  ElimModal Logic.True p false (|={E}=> P) P (wp_binop E op t1 v1 t2 v2 Q) (wp_binop E op t1 v1 t2 v2 Q).
Proof.
  by rewrite /ElimModal bi.intuitionistically_if_elim
    fupd_frame_r bi.wand_elim_r fupd_wp_binop.
Qed.

Lemma wp_binop_rule : forall E f e1 e2 Φ o t, wp_expr E f e1 (λ v1, wp_expr E f e2 (λ v2, wp_binop E o (typeof e1) v1 (typeof e2) v2 Φ))
  ⊢ wp_expr E f (Ebinop o e1 e2 t) Φ.
Proof.
  intros.
  rewrite /wp_expr /wp_binop.
  iIntros ">H !>" (??) "Hm ?".
  iMod ("H" with "Hm [$]") as "(%v1 & H1 & Hm & ? & >H)".
  iMod ("H" with "Hm [$]") as "(%v2 & H2 & Hm & ? & >H)".
  iMod ("H" with "Hm") as "(%v & %H & Hm & ?)".
  iIntros "!>"; iExists _; iFrame.
  iIntros "!>" (??) "#?"; rewrite !bi.affinely_elim.
  iDestruct ("H1" with "[$]") as %?; iDestruct ("H2" with "[$]") as %?; iPureIntro.
  intros; econstructor; eauto.
Qed.

(* variant of Clight_Cop2, closer to Cop *)
Definition sem_cast t1 t2 : val -> option val :=
  match Cop.classify_cast t1 t2 with
  | cast_case_pointer => fun v =>
      match v with
      | Vptr _ _ => Some v
      | Vint _ => if Archi.ptr64 then None else Some v
      | Vlong _ => if Archi.ptr64 then Some v else None
      | _ => None
      end
  | Cop.cast_case_i2i sz2 si2 => sem_cast_i2i sz2 si2
  | Cop.cast_case_f2f => sem_cast_f2f
  | Cop.cast_case_s2s => sem_cast_s2s
  | Cop.cast_case_s2f => sem_cast_s2f
  | Cop.cast_case_f2s => sem_cast_f2s
  | Cop.cast_case_i2f si1 => sem_cast_i2f si1
  | Cop.cast_case_i2s si1 => sem_cast_i2s si1
  | Cop.cast_case_f2i sz2 si2 => sem_cast_f2i sz2 si2
  | Cop.cast_case_s2i sz2 si2 => sem_cast_s2i sz2 si2
  | Cop.cast_case_i2bool => sem_cast_i2bool
  | Cop.cast_case_l2bool => sem_cast_l2bool
  | Cop.cast_case_f2bool => sem_cast_f2bool
  | Cop.cast_case_s2bool => sem_cast_s2bool
  | Cop.cast_case_l2l => sem_cast_l2l
  | Cop.cast_case_i2l si => sem_cast_i2l si
  | Cop.cast_case_l2i sz si => sem_cast_l2i sz si
  | Cop.cast_case_l2f si1 => sem_cast_l2f si1
  | Cop.cast_case_l2s si1 => sem_cast_l2s si1
  | Cop.cast_case_f2l si2 => sem_cast_f2l si2
  | Cop.cast_case_s2l si2 => sem_cast_s2l si2
  | Cop.cast_case_struct id1 id2 => sem_cast_struct id1 id2
  | Cop.cast_case_union id1 id2 => sem_cast_union id1 id2
  | Cop.cast_case_void =>
      fun v => Some v
  | Cop.cast_case_default =>
      fun v => None
 end.

Definition sem_binarith
    (sem_int: signedness -> int -> int -> option val)
    (sem_long: signedness -> int64 -> int64 -> option val)
    (sem_float: float -> float -> option val)
    (sem_single: float32 -> float32 -> option val)
    t1 t2 v1 v2 : option val :=
  let c := classify_binarith t1 t2 in
  let t := binarith_type c in
  match sem_cast t1 t v1 with
  | None => None
  | Some v1' =>
  match sem_cast t2 t v2 with
  | None => None
  | Some v2' =>
  match c with
  | bin_case_i sg =>
      match v1', v2' with
      | Vint n1, Vint n2 => sem_int sg n1 n2
      | _,  _ => None
      end
  | bin_case_f =>
      match v1', v2' with
      | Vfloat n1, Vfloat n2 => sem_float n1 n2
      | _,  _ => None
      end
  | bin_case_s =>
      match v1', v2' with
      | Vsingle n1, Vsingle n2 => sem_single n1 n2
      | _,  _ => None
      end
  | bin_case_l sg =>
      match v1', v2' with
      | Vlong n1, Vlong n2 => sem_long sg n1 n2
      | _,  _ => None
      end
  | bin_default => None
  end end end.

Definition sem_add t1 t2 v1 v2 : option val :=
  match classify_add t1 t2 with
  | add_case_pi ty si =>             (**r pointer plus integer *)
      Cop.sem_add_ptr_int ge ty si v1 v2
  | add_case_pl ty =>                (**r pointer plus long *)
      Cop.sem_add_ptr_long ge ty v1 v2
  | add_case_ip si ty =>             (**r integer plus pointer *)
      Cop.sem_add_ptr_int ge ty si v2 v1
  | add_case_lp ty =>                (**r long plus pointer *)
      Cop.sem_add_ptr_long ge ty v2 v1
  | add_default =>
      sem_binarith
        (fun sg n1 n2 => Some(Vint(Int.add n1 n2)))
        (fun sg n1 n2 => Some(Vlong(Int64.add n1 n2)))
        (fun n1 n2 => Some(Vfloat(Float.add n1 n2)))
        (fun n1 n2 => Some(Vsingle(Float32.add n1 n2)))
        t1 t2 v1 v2
  end.

Definition sem_sub t1 t2 v1 v2 : option val :=
  match classify_sub t1 t2 with
  | sub_case_pi ty si =>            (**r pointer minus integer *)
      match v1, v2 with
      | Vptr b1 ofs1, Vint n2 =>
          let n2 := ptrofs_of_int si n2 in
          Some (Vptr b1 (Ptrofs.sub ofs1 (Ptrofs.mul (Ptrofs.repr (@Ctypes.sizeof ge ty)) n2)))
      | Vint n1, Vint n2 =>
          if Archi.ptr64 then None else Some (Vint (Int.sub n1 (Int.mul (Int.repr (@Ctypes.sizeof ge ty)) n2)))
      | Vlong n1, Vint n2 =>
          let n2 := cast_int_long si n2 in
          if Archi.ptr64 then Some (Vlong (Int64.sub n1 (Int64.mul (Int64.repr (@Ctypes.sizeof ge ty)) n2))) else None
      | _,  _ => None
      end
  | sub_case_pl ty =>            (**r pointer minus long *)
      match v1, v2 with
      | Vptr b1 ofs1, Vlong n2 =>
          let n2 := Ptrofs.of_int64 n2 in
          Some (Vptr b1 (Ptrofs.sub ofs1 (Ptrofs.mul (Ptrofs.repr (@Ctypes.sizeof ge ty)) n2)))
      | Vint n1, Vlong n2 =>
          let n2 := Int.repr (Int64.unsigned n2) in
          if Archi.ptr64 then None else Some (Vint (Int.sub n1 (Int.mul (Int.repr (@Ctypes.sizeof ge ty)) n2)))
      | Vlong n1, Vlong n2 =>
          if Archi.ptr64 then Some (Vlong (Int64.sub n1 (Int64.mul (Int64.repr (@Ctypes.sizeof ge ty)) n2))) else None
      | _,  _ => None
      end
  | sub_case_pp ty =>          (**r pointer minus pointer *)
      match v1,v2 with
      | Vptr b1 ofs1, Vptr b2 ofs2 =>
          if eq_block b1 b2 then
            let sz := @Ctypes.sizeof ge ty in
            if zlt 0 sz && zle sz Ptrofs.max_signed
            then Some (Vptrofs (Ptrofs.divs (Ptrofs.sub ofs1 ofs2) (Ptrofs.repr sz)))
            else None
          else None
      | _, _ => None
      end
  | sub_default =>
      sem_binarith
        (fun sg n1 n2 => Some(Vint(Int.sub n1 n2)))
        (fun sg n1 n2 => Some(Vlong(Int64.sub n1 n2)))
        (fun n1 n2 => Some(Vfloat(Float.sub n1 n2)))
        (fun n1 n2 => Some(Vsingle(Float32.sub n1 n2)))
        t1 t2 v1 v2
  end.

Definition sem_mul (t1:type) (t2:type) (v1:val)  (v2: val)  : option val :=
  sem_binarith
    (fun sg n1 n2 => Some(Vint(Int.mul n1 n2)))
    (fun sg n1 n2 => Some(Vlong(Int64.mul n1 n2)))
    (fun n1 n2 => Some(Vfloat(Float.mul n1 n2)))
    (fun n1 n2 => Some(Vsingle(Float32.mul n1 n2)))
    t1 t2 v1 v2.

Definition sem_div (t1:type) (t2:type) (v1:val)  (v2: val) : option val :=
  sem_binarith
    (fun sg n1 n2 =>
      match sg with
      | Signed =>
          if Int.eq n2 Int.zero
          || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone
          then None else Some(Vint(Int.divs n1 n2))
      | Unsigned =>
          if Int.eq n2 Int.zero
          then None else Some(Vint(Int.divu n1 n2))
      end)
    (fun sg n1 n2 =>
      match sg with
      | Signed =>
          if Int64.eq n2 Int64.zero
          || Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone
          then None else Some(Vlong(Int64.divs n1 n2))
      | Unsigned =>
          if Int64.eq n2 Int64.zero
          then None else Some(Vlong(Int64.divu n1 n2))
      end)
    (fun n1 n2 => Some(Vfloat(Float.div n1 n2)))
    (fun n1 n2 => Some(Vsingle(Float32.div n1 n2)))
    t1 t2 v1 v2.

Definition sem_mod (t1:type) (t2:type) (v1:val)  (v2: val) : option val :=
  sem_binarith
    (fun sg n1 n2 =>
      match sg with
      | Signed =>
          if Int.eq n2 Int.zero
          || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone
          then None else Some(Vint(Int.mods n1 n2))
      | Unsigned =>
          if Int.eq n2 Int.zero
          then None else Some(Vint(Int.modu n1 n2))
      end)
    (fun sg n1 n2 =>
      match sg with
      | Signed =>
          if Int64.eq n2 Int64.zero
          || Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone
          then None else Some(Vlong(Int64.mods n1 n2))
      | Unsigned =>
          if Int64.eq n2 Int64.zero
          then None else Some(Vlong(Int64.modu n1 n2))
      end)
    (fun n1 n2 => None)
    (fun n1 n2 => None)
    t1 t2 v1 v2.

Definition sem_and (t1:type) (t2:type) (v1:val) (v2: val) : option val :=
  sem_binarith
    (fun sg n1 n2 => Some(Vint(Int.and n1 n2)))
    (fun sg n1 n2 => Some(Vlong(Int64.and n1 n2)))
    (fun n1 n2 => None)
    (fun n1 n2 => None)
    t1 t2 v1 v2.

Definition sem_or (t1:type) (t2:type) (v1:val)  (v2: val) : option val :=
  sem_binarith
    (fun sg n1 n2 => Some(Vint(Int.or n1 n2)))
    (fun sg n1 n2 => Some(Vlong(Int64.or n1 n2)))
    (fun n1 n2 => None)
    (fun n1 n2 => None)
    t1 t2 v1 v2.

Definition sem_xor (t1:type) (t2:type) (v1:val)  (v2: val) : option val :=
  sem_binarith
    (fun sg n1 n2 => Some(Vint(Int.xor n1 n2)))
    (fun sg n1 n2 => Some(Vlong(Int64.xor n1 n2)))
    (fun n1 n2 => None)
    (fun n1 n2 => None)
    t1 t2 v1 v2.

Definition sem_cmp_default c t1 t2 :=
  sem_binarith
        (fun sg n1 n2 =>
            Some(bool2val(match sg with Signed => Int.cmp c n1 n2 | Unsigned => Int.cmpu c n1 n2 end)))
        (fun sg n1 n2 =>
            Some(bool2val(match sg with Signed => Int64.cmp c n1 n2 | Unsigned => Int64.cmpu c n1 n2 end)))
        (fun n1 n2 =>
            Some(bool2val(Float.cmp c n1 n2)))
        (fun n1 n2 =>
            Some(bool2val(Float32.cmp c n1 n2)))
        t1 t2.


Definition sem_cmp c t1 t2 : val -> val -> option val :=
  match Cop.classify_cmp t1 t2 with
  | Cop.cmp_case_pp => sem_cmp_pp c
  | Cop.cmp_case_pi si => sem_cmp_pi si c
  | Cop.cmp_case_ip si => sem_cmp_ip si c
  | Cop.cmp_case_pl => sem_cmp_pl c
  | Cop.cmp_case_lp => sem_cmp_lp c
  | Cop.cmp_default => sem_cmp_default c t1 t2
  end.

Definition sem_binary_operation' (op: Cop.binary_operation)
    (t1:type) (t2: type) : val -> val -> option val :=
  match op with
  | Cop.Oadd => sem_add t1 t2
  | Cop.Osub => sem_sub t1 t2
  | Cop.Omul => sem_mul t1 t2
  | Cop.Omod => sem_mod t1 t2
  | Cop.Odiv => sem_div t1 t2
  | Cop.Oand => sem_and t1 t2
  | Cop.Oor  => sem_or t1 t2
  | Cop.Oxor  => sem_xor t1 t2
  | Cop.Oshl => fun v1 v2 => Cop.sem_shl v1 t1 v2 t2
  | Cop.Oshr  => fun v1 v2 => Cop.sem_shr v1 t1 v2 t2
  | Cop.Oeq => sem_cmp Ceq t1 t2
  | Cop.One => sem_cmp Cne t1 t2
  | Cop.Olt => sem_cmp Clt t1 t2
  | Cop.Ogt => sem_cmp Cgt t1 t2
  | Cop.Ole => sem_cmp Cle t1 t2
  | Cop.Oge => sem_cmp Cge t1 t2
  end.

Definition sc_cast v t1 t2 :=
  match Cop.classify_cast t1 t2 with
  | cast_case_i2bool =>
      match v with
      | Vptr b ofs =>
          if Archi.ptr64 then True else weak_valid_pointer v
      | _ => True
      end
  | cast_case_l2bool =>
      match v with
      | Vptr b ofs =>
          if negb Archi.ptr64 then True else weak_valid_pointer v
      | _ => True
      end
  | _ => True
  end.

Definition sc_binarith v1 t1 v2 t2 :=
  let c := classify_binarith t1 t2 in
  let t := binarith_type c in
  sc_cast v1 t1 t ∧ sc_cast v2 t2 t.

Definition sc_add v1 t1 v2 t2 :=
  match classify_add t1 t2 with
  | add_default => sc_binarith v1 t1 v2 t2
  | _ => True
  end.

Definition sc_sub v1 t1 v2 t2 :=
  match classify_sub t1 t2 with
  | sub_default => sc_binarith v1 t1 v2 t2
  | _ => True
  end.

Definition sc_cmplu_bool v1 v2 :=
  match v1, v2 with
  | Vlong n1, Vptr b2 ofs2 =>
      if negb Archi.ptr64 then True else weak_valid_pointer v2
  | Vptr b1 ofs1, Vptr b2 ofs2 =>
      if negb Archi.ptr64 then True else if eq_block b1 b2 then
        weak_valid_pointer v1 ∧ weak_valid_pointer v2
      else valid_pointer v1 ∧ valid_pointer v2
  | Vptr b1 ofs1, Vlong n2 =>
      if negb Archi.ptr64 then True else weak_valid_pointer v1
  | _, _ => True
  end.

Definition sc_cmpu_bool v1 v2 :=
  match v1, v2 with
  | Vint n1, Vptr b2 ofs2 =>
      if Archi.ptr64 then True else weak_valid_pointer v2
  | Vptr b1 ofs1, Vptr b2 ofs2 =>
      if Archi.ptr64 then True else if eq_block b1 b2 then
        weak_valid_pointer v1 ∧ weak_valid_pointer v2
      else valid_pointer v1 ∧ valid_pointer v2
  | Vptr b1 ofs1, Vint n2 =>
      if negb Archi.ptr64 then True else weak_valid_pointer v1
  | _, _ => True
  end.

Definition sc_cmp_ptr v1 v2 :=
  if Archi.ptr64 then sc_cmplu_bool v1 v2 else sc_cmpu_bool v1 v2.

Definition sc_cmp v1 t1 v2 t2 :=
  match classify_cmp t1 t2 with
  | cmp_case_pp => sc_cmp_ptr v1 v2
  | cmp_case_pi si =>
      match v2 with
      | Vint n2 =>
          let v2' := Vptrofs (ptrofs_of_int si n2) in
          sc_cmp_ptr v1 v2'
      | Vptr b ofs =>
          if Archi.ptr64 then True else sc_cmp_ptr v1 v2
      | _ => True
      end
  | cmp_case_ip si =>
      match v1 with
      | Vint n1 =>
          let v1' := Vptrofs (ptrofs_of_int si n1) in
          sc_cmp_ptr v1' v2
      | Vptr b ofs =>
          if Archi.ptr64 then True else sc_cmp_ptr v1 v2
      | _ => True
      end
  | cmp_case_pl =>
      match v2 with
      | Vlong n2 =>
          let v2' := Vptrofs (Ptrofs.of_int64 n2) in
          sc_cmp_ptr v1 v2'
      | Vptr b ofs =>
          if Archi.ptr64 then sc_cmp_ptr v1 v2 else True
      | _ => True
      end
  | cmp_case_lp =>
      match v1 with
      | Vlong n1 =>
          let v1' := Vptrofs (Ptrofs.of_int64 n1) in
          sc_cmp_ptr v1' v2
      | Vptr b ofs =>
          if Archi.ptr64 then sc_cmp_ptr v1 v2 else True
      | _ => True
      end
  | cmp_default =>
      sc_binarith v1 t1 v2 t2
  end.

Definition sc_binop op t1 t2 v1 v2 :=
  match op with
  | Oadd => sc_add v1 t1 v2 t2
  | Osub => sc_sub v1 t1 v2 t2
  | Omul | Omod | Odiv| Oand | Oor | Oxor => sc_binarith v1 t1 v2 t2
  | Oshl => True
  | Oshr  => True
  | _ => sc_cmp v1 t1 v2 t2
  end.

Lemma sc_cast_sound : forall v t1 t2 m,
  ⊢ sc_cast v t1 t2 -∗ mem_auth m -∗
  ⌜Cop.sem_cast v t1 t2 m = sem_cast t1 t2 v⌝.
Proof.
  intros; iIntros "H Hm".
  rewrite /sc_cast /Cop.sem_cast /sem_cast.
  destruct (Cop.classify_cast t1 t2); try done.
  destruct v; try done; simpl.
  simple_if_tac; try done.
  by rewrite /Mem.weak_valid_pointer; iDestruct (weak_valid_pointer_dry with "[$]") as %->.
Qed.

Lemma sc_binarith_sound : forall a b c d t1 t2 v1 v2 m,
  ⊢ sc_binarith v1 t1 v2 t2 -∗ mem_auth m -∗
  ⌜Cop.sem_binarith a b c d v1 t1 v2 t2 m = sem_binarith a b c d t1 t2 v1 v2⌝.
Proof.
  intros; iIntros "H Hm".
  rewrite /sc_binarith /Cop.sem_binarith /sem_binarith.
  iDestruct (sc_cast_sound with "[H] Hm") as %->; first by rewrite bi.and_elim_l.
  iDestruct (sc_cast_sound with "[H] Hm") as %->; first by rewrite bi.and_elim_r.
  done.
Qed.

Arguments valid_pointer : simpl never.

Lemma sc_cmp_ptr_sound : forall c v1 v2 m,
  ⊢ sc_cmp_ptr v1 v2 -∗ mem_auth m -∗
  ⌜Cop.cmp_ptr m c v1 v2 = sem_cmp_pp c v1 v2⌝.
Proof.
  intros; iIntros "H Hm".
  rewrite /sc_cmp_ptr /Cop.cmp_ptr /sem_cmp_pp.
  simple_if_tac.
  - rewrite /Val.cmplu_bool bool2val_eq.
    destruct v1; try done; destruct v2; try done; simpl.
    + simple_if_tac; try done.
      by iDestruct (weak_valid_pointer_dry with "[$]") as %->.
    + simple_if_tac; try done.
      by iDestruct (weak_valid_pointer_dry with "[$]") as %->.
    + simple_if_tac; try done.
      if_tac.
      * iDestruct (weak_valid_pointer_dry with "[H $Hm]") as %->; first by rewrite bi.and_elim_l.
        iDestruct (weak_valid_pointer_dry with "[H $Hm]") as %->; first by rewrite bi.and_elim_r.
        done.
      * iDestruct (valid_pointer_dry0 with "[H $Hm]") as %->; first by rewrite bi.and_elim_l.
        iDestruct (valid_pointer_dry0 with "[H $Hm]") as %->; first by rewrite bi.and_elim_r.
        done.
  - rewrite /Val.cmpu_bool bool2val_eq.
    destruct v1; try done; destruct v2; try done; simpl.
Qed.

Lemma sc_cmp_sound : forall c t1 t2 v1 v2 m,
  ⊢ sc_cmp v1 t1 v2 t2 -∗ mem_auth m -∗
  ⌜Cop.sem_cmp c v1 t1 v2 t2 m = sem_cmp c t1 t2 v1 v2⌝.
Proof.
  intros; iIntros "H Hm".
  rewrite /sc_cmp /Cop.sem_cmp /sem_cmp.
  destruct (classify_cmp t1 t2).
  - iApply (sc_cmp_ptr_sound with "H Hm").
  - rewrite /sem_cmp_pi.
    destruct v2; try simple_if_tac; try done; iApply (sc_cmp_ptr_sound with "H Hm").
  - rewrite /sem_cmp_ip.
    destruct v1; try simple_if_tac; try done; iApply (sc_cmp_ptr_sound with "H Hm").
  - rewrite /sem_cmp_pl.
    destruct v2; try simple_if_tac; try done; iApply (sc_cmp_ptr_sound with "H Hm").
  - rewrite /sem_cmp_lp.
    destruct v1; try simple_if_tac; try done; iApply (sc_cmp_ptr_sound with "H Hm").
  - rewrite /sem_cmp_default bool2val_eq.
    iApply (sc_binarith_sound with "H Hm").
Qed.

Lemma sc_binop_sound : forall op t1 t2 v1 v2 m,
  ⊢ sc_binop op t1 t2 v1 v2 -∗ mem_auth m -∗
  ⌜sem_binary_operation ge op v1 t1 v2 t2 m = sem_binary_operation' op t1 t2 v1 v2⌝.
Proof.
  intros; iIntros "H Hm".
  rewrite /sc_binop /sem_binary_operation /sem_binary_operation'.
  destruct op.
  - rewrite /sc_add /Cop.sem_add /sem_add.
    destruct (classify_add t1 t2); try done.
    iApply (sc_binarith_sound with "H Hm").
  - rewrite /sc_sub /Cop.sem_sub /sem_sub.
    destruct (classify_sub t1 t2); try done.
    iApply (sc_binarith_sound with "H Hm").
  - iApply (sc_binarith_sound with "H Hm").
  - iApply (sc_binarith_sound with "H Hm").
  - iApply (sc_binarith_sound with "H Hm").
  - iApply (sc_binarith_sound with "H Hm").
  - iApply (sc_binarith_sound with "H Hm").
  - iApply (sc_binarith_sound with "H Hm").
  - done.
  - done.
  - iApply (sc_cmp_sound with "H Hm").
  - iApply (sc_cmp_sound with "H Hm").
  - iApply (sc_cmp_sound with "H Hm").
  - iApply (sc_cmp_sound with "H Hm").
  - iApply (sc_cmp_sound with "H Hm").
  - iApply (sc_cmp_sound with "H Hm").
Qed.

Lemma wp_binop_sc : forall E op t1 v1 t2 v2 v P,
  sem_binary_operation' op t1 t2 v1 v2 = Some v →
  ⎡sc_binop op t1 t2 v1 v2⎤ ∧ P v ⊢ wp_binop E op t1 v1 t2 v2 P.
Proof.
  intros; rewrite /wp_binop.
  iIntros "H !>" (?) "Hm !>".
  iDestruct (sc_binop_sound with "[H] Hm") as %->; first by rewrite bi.and_elim_l.
  rewrite bi.and_elim_r; eauto with iFrame.
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

Lemma wp_pointer_cmp: forall {CS: compspecs} E (cmp : Cop.binary_operation) ty1 ty2 v1 v2 sh1 sh2 P,
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

Lemma wp_unop_rule : forall E f e Φ o t, wp_expr E f e (λ v, wp_unop E o (typeof e) v Φ)
  ⊢ wp_expr E f (Eunop o e t) Φ.
Proof.
  intros.
  rewrite /wp_expr /wp_binop.
  iIntros ">H !>" (??) "Hm ?".
  iMod ("H" with "Hm [$]") as "(%v1 & H1 & Hm & ? & >H)".
  iMod ("H" with "Hm") as "(%v & %H & Hm & ?)".
  iIntros "!>"; iExists _; iFrame.
  iStopProof; do 7 f_equiv.
  intros ??; econstructor; eauto.
Qed.

Definition cast_pointer_to_bool t1 t2 :=
 match t1 with (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _) => 
           match t2 with Tint IBool _ _ => true | _ => false end
 | _ => false
end.

Lemma sem_cast_e1:
 forall t t1 v1 v m,
   Clight_Cop2.sem_cast t t1 v = Some v1 ->
   cast_pointer_to_bool t t1 = false ->
   tc_val t v ->
   Cop.sem_cast v t t1 m = Some v1.
Proof.
intros.
destruct (eqb_type t int_or_ptr_type) eqn:J;
 [apply eqb_type_true in J; subst t
 | apply eqb_type_false in J];
(destruct (eqb_type t1 int_or_ptr_type) eqn:J0;
 [apply eqb_type_true in J0; subst t1
 | apply eqb_type_false in J0]).
* unfold sem_cast, sem_cast_pointer in H; simpl in *.
  rewrite -> N.eqb_refl in *.
  simpl in H.
  inv H.
  destruct v1; auto; inv H1.
*
unfold Clight_Cop2.sem_cast, classify_cast in H.
destruct t1; [auto | | | auto ..].
+
destruct i,s; auto; try solve [destruct v; inv H]; try solve [inv H0];
simpl in H;
simpl;
destruct Archi.ptr64; auto;
destruct v; inv H1; inv H; auto.
+ rewrite <- H; clear H.
  unfold tc_val in H1.
  rewrite eqb_type_refl in H1.
  simpl in H1.
  simpl in *.
  solve [auto | destruct Archi.ptr64 eqn:?Hp; auto; destruct v; inv H1; auto].
+
destruct f; inv H.
+
clear H0.
unfold int_or_ptr_type at 1 in H.
inv H.
simpl.
destruct v1; inv H1; auto.
*
unfold Clight_Cop2.sem_cast in H.
destruct t; try solve [inv H].
{
  simpl in H.
  rewrite N.eqb_refl in H.
  simpl in H1.
  destruct v; try inv H1.
  simpl.
  destruct Archi.ptr64 eqn:Hp; auto; inv Hp.
}
{
unfold classify_cast in H.
unfold int_or_ptr_type at 1 in H.
inv H.
simpl.
unfold tc_val in H1.
rewrite <- eqb_type_spec in J.
destruct (eqb_type (Tpointer t a) int_or_ptr_type); [congruence |].
hnf in H1.
destruct v1; tauto.
}
{
unfold classify_cast in H.
unfold int_or_ptr_type at 1 in H.
inv H.
simpl.
unfold tc_val in H1.
hnf in H1.
destruct v1; tauto.
}
{
unfold classify_cast in H.
unfold int_or_ptr_type at 1 in H.
inv H.
simpl.
unfold tc_val in H1.
hnf in H1.
destruct v1; tauto.
}
*
revert H.
clear - J J0 H0 H1.
unfold Cop.sem_cast, Clight_Cop2.sem_cast.
unfold Cop.classify_cast, classify_cast, sem_cast_pointer, 
 sem_cast_l2bool, sem_cast_i2bool.
rewrite ?(proj2 (eqb_type_false _ _) J);
rewrite ?(proj2 (eqb_type_false _ _) J0).
destruct t1   as [ | [ | | | ] [ | ] | | [ | ] | | | | | ]; auto;
destruct t   as [ | [ | | | ] [ | ] | | [ | ] | | | | | ]; auto; try discriminate H0;
 auto;
 destruct Archi.ptr64 eqn:Hp; auto;
 destruct v; auto; try contradiction;
 try solve [simpl in H1; rewrite Hp in H1; inv H1];
 try solve [simpl in H1; revert H1; simple_if_tac; intros []].
 
 simpl in H1; revert H1; simple_if_tac; simpl; rewrite Hp; intros [].
Qed.

Lemma wp_cast : forall E f e ty P, cast_pointer_to_bool (typeof e) ty = false ->
  wp_expr E f e (λ v, ⌜tc_val (typeof e) v⌝ ∧ ∃ v', ⌜Clight_Cop2.sem_cast (typeof e) ty v = Some v'⌝ ∧ P v') ⊢ wp_expr E f (Ecast e ty) P.
Proof.
  intros; rewrite /wp_expr.
  do 8 f_equiv. iIntros "(% & ? & Hm & ? & % & %v' & %Hcast & P)".
  iExists v'; iFrame.
  iStopProof; do 7 f_equiv.
  intros ??; econstructor; eauto.
  by apply sem_cast_e1.
Qed.

Lemma wp_cast_sc : forall E f e ty P,
  wp_expr E f e (λ v, ⎡sc_cast v (typeof e) ty⎤ ∧ ∃ v', ⌜sem_cast (typeof e) ty v = Some v'⌝ ∧ P v') ⊢ wp_expr E f (Ecast e ty) P.
Proof.
  intros; rewrite /wp_expr.
  do 8 f_equiv. iIntros "(% & ? & Hm & ? & H)".
  iDestruct (sc_cast_sound with "[H] Hm") as %?; first by rewrite bi.and_elim_l.
  iDestruct "H" as "(_ & % & %Hcast & P)".
  iExists v'; iFrame.
  iStopProof; do 7 f_equiv.
  intros ??; econstructor; eauto.
  by rewrite H.
Qed.

Lemma wp_tempvar_local : forall E f _x x c_ty P,
  temp _x x ∗ (temp _x x -∗ P x)
  ⊢ wp_expr E f (Etempvar _x c_ty) P.
Proof.
  split => n; rewrite /wp_expr; monPred.unseal.
  iIntros "[H HP] !>" (??? <-). iIntros "Hm" (? <-) "Hr !>".
  iDestruct (temp_e with "[$H $Hr]") as %H.
  iSpecialize ("HP" with "[%] H"); first done.
  iExists _; iFrame. rewrite monPred_at_affinely; iPureIntro; simpl.
  intros ??? <- (? & ? & Hte); rewrite -Hte in H.
  by constructor.
Qed.

Lemma wp_var_local : forall E f _x c_ty b (P:address->assert),
  lvar _x c_ty b ∗ (lvar _x c_ty b -∗ P (b, 0))
  ⊢ wp_lvalue f E (Evar _x c_ty) P.
Proof.
  split => n; rewrite /wp_lvalue; monPred.unseal.
  iIntros "[H HP] !>" (??? <-). iIntros "Hm" (? <-) "Hr !>".
  iDestruct (lvar_e with "[$H $Hr]") as %H.
  iSpecialize ("HP" with "[%] H"); first done.
  change 0 with (Ptrofs.unsigned Ptrofs.zero).
  iExists _, _; iFrame. rewrite monPred_at_affinely; iPureIntro; simpl.
  intros ??? <- (? & Hve & ?); rewrite -Hve in H.
  by constructor.
Qed.

Lemma ge_of_env : forall ρ n, ge_of (env_to_environ ρ n) = ρ.1.
Proof.
  intros; rewrite /env_to_environ.
  destruct (ρ.2 !! n)%stdpp as [(?, ?)|]; done.
Qed.

Lemma wp_var_global : forall E f _x c_ty b (P:address->assert),
  ~In _x (map fst (fn_vars f)) →
  ⎡gvar _x b⎤ ∗ (⎡gvar _x b⎤ -∗ P (b, 0))
  ⊢ wp_lvalue E f (Evar _x c_ty) P.
Proof.
  split => n; rewrite /wp_lvalue; monPred.unseal.
  iIntros "[H HP] !>" (??? <-). iIntros "Hm" (? <-) "Hr !>".
  iDestruct (gvar_e with "[$H $Hr]") as %Hx.
  iSpecialize ("HP" with "[%] H"); first done.
  change 0 with (Ptrofs.unsigned Ptrofs.zero).
  iExists _, _; iFrame. rewrite monPred_at_affinely; iPureIntro; simpl.
  intros ??? <- (Hge & ? & ?) Hmatch.
  rewrite ge_of_env in Hge; rewrite -Hge in Hx.
  apply eval_Evar_global; auto.
  rewrite /match_venv in Hmatch.
  specialize (Hmatch _x); rewrite make_env_spec in Hmatch.
  destruct (_ !! _) as [(?, ?)|]; auto.
  contradiction H; rewrite in_map_iff; eexists; split; eauto; done.
Qed.

Lemma wp_deref : forall E f e ty P,
  wp_expr E f e (λ v, ∃ b o, <affine> ⌜v = Vptr b o⌝ ∗ P (b, Ptrofs.unsigned o)) ⊢ wp_lvalue E f (Ederef e ty) P.
Proof.
  intros; rewrite /wp_lvalue /wp_expr.
  do 8 f_equiv.
  iIntros "(% & ? & ? & ? & %b & %o & % & ?)"; iExists b, o; iFrame.
  iStopProof; do 7 f_equiv.
  intros ??; subst; econstructor; eauto.
Qed.

Lemma wp_expr_byref : forall E f e P, access_mode (typeof e) = By_reference →
  wp_lvalue E f e (λ '(b, o), P (Vptr b (Ptrofs.repr o))) ⊢ wp_expr E f e P.
Proof.
  intros; rewrite /wp_lvalue /wp_expr.
  do 8 f_equiv.
  iIntros "(% & % & ? & $)".
  iStopProof; do 7 f_equiv.
  intros ??; econstructor; eauto.
  rewrite Ptrofs.repr_unsigned; constructor; auto.
Qed.

Lemma wp_lvalue_field : forall E f e i t P,
  wp_expr E f e (λ v, ∃ b o, <affine> ⌜v = Vptr b o⌝ ∗ ∃ co delta, <affine> ⌜match typeof e with
  | Tstruct id _ => (genv_cenv ge !! id)%maps = Some co ∧ field_offset ge i (co_members co) = Errors.OK (delta, Full)
  | Tunion id _ => (genv_cenv ge !! id)%maps = Some co ∧ union_field_offset ge i (co_members co) = Errors.OK (delta, Full)
  | _ => False end⌝ ∗ P (b, Ptrofs.unsigned (Ptrofs.add o (Ptrofs.repr delta)))) ⊢ wp_lvalue E f (Efield e i t) P.
Proof.
  intros; rewrite /wp_lvalue /wp_expr.
  do 8 f_equiv.
  iIntros "(% & ? & $ & $ & % & % & -> & % & % & % & $)".
  iStopProof; do 7 f_equiv.
  intros ??; destruct (typeof e) eqn: Hty; try done; destruct H.
  - eapply eval_Efield_struct; eauto.
  - eapply eval_Efield_union; eauto.
Qed.

Lemma wp_expr_mapsto : forall E f e P,
  wp_lvalue E f e (λ '(b, o), ∃ sh v, <affine> ⌜readable_share sh ∧ v ≠ Vundef⌝ ∗
    ⎡▷ <absorb> mapsto sh (typeof e) (Vptr b (Ptrofs.repr o)) v⎤ ∧ P v) ⊢
  wp_expr E f e P.
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
  iStopProof; do 7 f_equiv.
  intros ??; econstructor; eauto.
  econstructor; eauto.
Qed.

End mpred.

(* Lemma wp_expr_cenv_sub : forall `{!heapGS Σ} `{!envGS Σ} CE CE' E f e P, cenv_sub CE CE' ->
  wp_expr CE E f e P ⊢ wp_expr CE' E f e P.
Proof.
  intros; rewrite /wp_expr.
  repeat f_equiv.
  intros ? Hsub.
  eapply (cenv_sub_trans H) in Hsub; auto.
Qed.

Lemma wp_lvalue_cenv_sub : forall `{!heapGS Σ} `{!envGS Σ} CE CE' E f e P, cenv_sub CE CE' ->
  wp_lvalue CE E f e P ⊢ wp_lvalue CE' E f e P.
Proof.
  intros; rewrite /wp_lvalue.
  repeat f_equiv.
  intros ? Hsub.
  eapply (cenv_sub_trans H) in Hsub; auto.
Qed. *)
