Require Import Arith.
Require Import Relations.
Require Import Lexicographic_Product.

(** Library for reasoning about wellfounded relations *)

Section LT_WF_REL.
 (* This Section is copied from the Coq library, which unfortunately uses
 Set instead of Type for Variable A, so just modified the one word. *)
  Variable A : Type.
  Variable R : A -> A -> Prop.

  (* Relational form of inversion *)
  Variable F : A -> nat -> Prop.
  Definition inv_lt_rel x y := exists2 n, F x n & (forall m, F y m -> n < m).

  Hypothesis F_compat : forall x y:A, R x y -> inv_lt_rel x y.
  Remark acc_lt_rel : forall x:A, (exists n, F x n) -> Acc R x.
  Proof.
    intros x [n fxn]; generalize dependent x.
Require Import Image.
    pattern n in |- *; apply lt_wf_ind; intros.
    constructor; intros.
    destruct (F_compat y x) as (x0,H1,H2); trivial.
    apply (H x0); auto.
  Qed.

  Theorem well_founded_inv_lt_rel_compat : well_founded R.
  Proof.
    constructor; intros.
    case (F_compat y a); trivial; intros.
    apply acc_lt_rel; trivial.
    exists x; trivial.
  Qed.

End LT_WF_REL.

Definition lex_pair {A B} (Ra: A -> A -> Prop) (Rb: B -> B -> Prop)
            (x: A*B) (y: A*B) : Prop :=
 Ra (fst x) (fst y) \/ (fst x = fst y /\ Rb (snd x) (snd y)).


(*
Lemma lex_pair_eqv:
  forall A B Ra Rb,
   lex_pair Ra Rb =
   (fun x y =>
   lexprod A (fun _ => B) Ra (fun _ => Rb)
     (existT (fun _:A => B) (fst x) (snd x))
     (existT (fun _:A => B) (fst y) (snd y))).
Proof.
 intros.
 apply Axioms.extensionality; intros [a b].
 apply Axioms.extensionality; intros [a' b'].
 simpl.
 apply Axioms.prop_ext; intuition.
 destruct H; simpl in *.
 left; auto.
 destruct H; subst a'. right; auto.
 inversion H; clear H; subst.
 left; simpl; auto.
 right; split; auto.
Qed.
*)

Lemma well_founded_incl:
  forall A (Rs Rt: A -> A -> Prop),
   inclusion _ Rt Rs -> well_founded Rs -> well_founded Rt.
Proof.
  unfold well_founded; intros.
  specialize (H0 a).
  induction H0; constructor; intros; auto.
Qed.

Lemma well_founded_image:
  forall A B (f: A -> B) (Rb: B -> B -> Prop),
    well_founded Rb ->
    well_founded (fun x y => Rb (f x) (f y)).
Proof.
  intros.
 intro a.
 specialize (H (f a)).
 remember (f a) as fa.
 revert a Heqfa; induction H; intros; constructor;  intros; auto.
 subst.
 eapply H0; eauto.
Qed.

Lemma well_founded_lex_pair:
  forall A B (Ra: A -> A -> Prop) (Rb: B -> B -> Prop),
  well_founded Ra -> well_founded Rb -> well_founded (lex_pair Ra Rb).
Proof.
 intros.
 apply well_founded_incl with (Rs :=  (fun x y =>
   lexprod A (fun _ => B) Ra (fun _ => Rb)
     (existT (fun _:A => B) (fst x) (snd x))
     (existT (fun _:A => B) (fst y) (snd y)))).
 intros [a b] [a' b'] ?.
 inversion H1; clear H1; subst; simpl in *.
 left; auto. destruct H2; subst; right; auto.
 apply well_founded_image.
 apply wf_lexprod; auto.
Qed.


Lemma well_founded_trans:
  forall A (Ra: A -> A -> Prop),
    well_founded Ra <-> well_founded (clos_trans _ Ra).
Proof.
intros; split; intros.
unfold well_founded in *.
intros.
specialize (H a).
induction H.
constructor; intros.
apply clos_trans_t1n in H1.
induction H1; auto.
assert (Acc (clos_trans A Ra) y).
2: destruct H3; apply H3; apply clos_t1n_trans; econstructor; eauto.
clear - H0 H2.
revert H0; induction H2; intros.
auto.
apply IHclos_trans_1n; auto.
constructor 1; auto.
unfold well_founded in *.
intros.
specialize (H a).
induction H.
constructor; intros; auto.
apply H0.
constructor 1 ;auto.
Qed.


Definition lexprodx {B A : Type} (f: A -> B) (R1: B -> B -> Prop)
  (R2: B -> A -> A -> Prop)
  (x y : A) : Prop :=
     R1 (f x) (f y) \/ f x = f y /\ R2 (f x) x y.

Lemma lexprodx_eq: forall B A f R1 R2 x y,
    lexprodx f R1 R2 x y <->
    lexprod B (fun _ => A) R1 R2 (existT (fun _:B => A) (f x) x)
               (existT (fun _:B => A) (f y) y).
Proof.
 intros.
 unfold lexprodx.
 intuition.
 left; auto.
 rewrite <- H. right. auto.
 inversion H; clear H; subst.
 left; auto.
 right; split; auto.
Qed.

Lemma well_founded_lexprodx: forall B A (f: A -> B) R1 R2,
  well_founded R1 -> (forall n, well_founded (R2 n)) ->
  well_founded (lexprodx f R1 R2).
Proof.
intros.
 apply well_founded_incl with (fun x y => lexprod B (fun _ => A) R1 R2 (existT (fun _:B => A) (f x) x)
               (existT (fun _:B => A) (f y) y)).
 intros ? ? ?. rewrite <- lexprodx_eq.  auto.
 apply well_founded_image with (f:= fun x => (existT (fun _ : B => A) (f x) x)).
 apply wf_lexprod; auto.
Qed.


(* WARNING: Not sure simple_lexprod is useful! *)
Definition simple_lexprod {A: Type} (R1: A -> A -> Prop) (R2: A -> A -> Prop)
            (x y: A) : Prop :=
  R1 x y \/ x=y /\ R2 x y.

Lemma simple_lexprod_eq:
  forall A R1 R2 x y,
     @simple_lexprod A R1 R2 x y <->
    lexprod A (fun _ => A) R1 (fun _ => R2)
       (existT (fun _:A => A) x x) (existT (fun _:A => A) y y).
Proof.
intros.
unfold simple_lexprod.
intuition.
left; auto.
subst; right; auto.
inversion H; clear H; subst; auto.
Qed.

Lemma wellfounded_simple_lexprod:
  forall A (R1: A -> A -> Prop) (R2: A -> A -> Prop),
    well_founded R1 ->
    well_founded R2 ->
    well_founded (simple_lexprod R1 R2).
Proof.
 intros.
 apply well_founded_incl with
   (fun x y => lexprod A (fun _ => A) R1 (fun _ => R2) (existT (fun _:A => A) x x)  (existT (fun _:A => A) y y)).
 intros ? ? ?. rewrite <- simple_lexprod_eq. auto.
 apply well_founded_image with (f:= fun x => existT (fun _:A => A) x x).
 apply wf_lexprod; auto.
Qed.

