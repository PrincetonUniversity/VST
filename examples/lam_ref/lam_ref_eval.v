(*
 * Copyright (c) 2009 Robert Dockins and Aquinas Hobor.
 *
 *)

Require Import lam_ref_tcb.
Require Import lam_ref_mach_defs.
Require Import lam_ref_mach_lemmas.

Require Import msl.msl_standard.

Section eval.
  Variable eval : mem -> expr -> (mem * expr).

  Definition eval' (m:mem) (e0:expr) : mem * expr :=
  match e0 with
  | App e1 e2 =>
      match eval m e1 with
      | (m', Lam e1') =>
          let (m'',e2') := eval m' e2 in
            match value_dec e2' with
            | left H => eval m'' (subst 0 (exp_to_val e2' H) e1')
            | _ => (m'',App (Lam e1') e2')
            end
      | (m',e1') => (m',App e1' e2)
      end
  | Prim f e1 =>
      match eval m e1 with
      | (m', Nat x) =>
        match value_dec (f x) with
        | left H => (m',f x)
        | _ => (m',Prim f (Nat x))
        end
      | (m',e1') => (m',Prim f e1')
      end
  | New e1 =>
      let (m',e') := eval m e1 in
      match value_dec e' with
      | left H =>
           let (m'',l) := new m' (exp_to_val e' H) in (m'',Loc l)
      | _ => (m',New e')
      end
  | Deref e1 =>
      match eval m e1 with
      | (m',Loc l) => eval m' (val_to_exp (deref m' l))
      | (m',e1') => (m',Deref e1')
      end
  | Update e1 e2 e3 =>
      match eval m e1 with
      | (m',Loc l) =>
          let (m'',e2') := eval m' e2 in
          match value_dec e2' with
          | left H =>
              eval (update m'' l (exp_to_val e2' H)) e3
          | _ => (m'',Update (Loc l) e2' e3)
          end
      | (m',x) => (m',Update x e2 e3)
      end
  | x => (m,x)
  end.

  Hypothesis Heval :
    forall m e m' e',
      eval m e = (m',e') ->
      stepstar (m,e) (m',e').

  Lemma eval'_correct :
    forall m e m' e',
      eval' m e = (m',e') ->
      stepstar (m,e) (m',e').
  Proof.
    intros.
    destruct e; simpl in H.
    inv H; try (apply step_refl; auto).
    case_eq (eval m e); intros.
    rewrite H0 in H.
    generalize H0; intros.
    apply Heval in H1.
    apply step_trans with (m0,Prim f e0).
    apply stepstar_search; auto.
    intros; apply st_Prim1; auto.
    destruct e0; inv H; try apply step_refl.
    destruct (value_dec (f n)).
    apply step1.
    apply st_Prim2; auto.
    apply step_refl.
    inv H; apply step_refl.
    inv H; apply step_refl.
    inv H; apply step_refl.
    case_eq (eval m e1); intros.
    rewrite H0 in H.
    generalize H0; intros.
    apply Heval in H1.
    apply step_trans with (m0,App e e2).
    apply (stepstar_search (fun x => App x e2)); auto.
    intros; apply st_App1; auto.
    destruct e; inv H; try (apply step_refl).
    case_eq (eval m0 e2); intros.
    rewrite H in H3.
    destruct (value_dec e0).
    apply Heval in H.
    apply step_trans with (m1,App (Lam e) e0).
    apply stepstar_search; intros; auto.
    apply st_App2; auto.
    rewrite H3.
    apply Heval in H3.
    apply step_trans with (m1,subst 0 (exp_to_val e0 i) e).
    apply step1.
    apply st_App3.
    auto.
    inv H3.
    apply Heval in H.
    apply stepstar_search; auto.
    intros; apply st_App2; auto.
    case_eq (eval m e); intros.
    rewrite H0 in H.
    apply Heval in H0.
    apply step_trans with (m0,New e0).
    apply stepstar_search; auto.
    intros; apply st_New1; auto.
    destruct (value_dec e0).
    case_eq (new m0 (exp_to_val e0 i)); intros.
    rewrite H1 in H.
    inv H.
    apply step1.
    apply st_New2 with i; auto.
    inv H.
    apply step_refl.
    case_eq (eval m e); intros.
    rewrite H0 in H.
    apply Heval in H0.
    apply step_trans with (m0,Deref e0).
    apply stepstar_search; auto.
    intros; apply st_Deref1; auto.
    destruct e0; inv H; try apply step_refl.
    rewrite H2.
    apply step_trans with (m0,val_to_exp (deref m0 l)).
    apply step1.
    apply st_Deref2; auto.
    apply Heval; auto.
    case_eq (eval m e1); intros.
    rewrite H0 in H.
    apply Heval in H0.
    apply step_trans with (m0,Update e e2 e3).
    apply (stepstar_search (fun x => Update x e2 e3)); auto.
    intros; apply st_Upd1; auto.
    destruct e; inv H; try apply step_refl.
    case_eq (eval m0 e2); intros.
    rewrite H in H2.
    apply Heval in H.
    apply step_trans with (m1,Update (Loc l) e e3).
    apply (stepstar_search (fun x => Update (Loc l) x e3)); auto.
    intros; apply st_Upd2; auto.
    destruct (value_dec e); try apply step_refl.
    rewrite H2.
    apply step_trans with (update m1 l (exp_to_val e i),e3).
    apply step1.
    apply st_Upd3 with i; auto.
    apply Heval; auto.
  Qed.
End eval.

Definition eval (x:Z) := Zmisc.iter x _ eval' (fun m e => (m,e)).

Lemma eval_correct : forall x m e m' e',
  eval x m e = (m',e') ->
  stepstar (m,e) (m',e').
Proof.
  intros; unfold eval in H.
  destruct x.
  inv H; apply step_refl.
  2: inv H; apply step_refl.
  rewrite iter_nat_of_Z in H by apply Zle_0_pos.
  rewrite Zabs2Nat.inj_pos in H.
  revert H.
  generalize (nat_of_P p); clear p.
  intro n; revert m e m' e'.
  induction n; simpl; intros.
  inv H; apply step_refl.
  eapply eval'_correct; eauto.
Qed.
