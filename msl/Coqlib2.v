Require Import msl.Extensionality.
Require Import msl.base.

(* Can't use "Hint Resolve" because a bug in "apply proof_irr" matches
   things that are not Props, which leads the Qed to fail (later) *)
Hint Extern 1 (@eq _ _ _) => exact (proof_irr _ _).

(* Can't use "Hint Resolve" because it doesn't seem to do anything... *)
Hint Extern 2 (eq _ _)  => apply exist_ext.

(* Can't use "Hint Resolve" because it doesn't seem to do anything... *)
Hint Extern 2 (@eq _ (@existT _ _ _ _) (@existT _ _ _ _))  => apply existT_ext.

Tactic Notation "forget" constr(X) "as" ident(y) := 
   set (y:=X) in *; clearbody y.

Ltac proof_irr := match goal with H: ?A, H' : ?A |- _ => generalize (proof_irr H H'); intro; subst H' end.

Ltac inversion2 H1 H2 :=
 rewrite H1 in H2; symmetry in H2; inv H2.

Ltac invT H :=
match type of H  with 
  | existT _ ?a ?b = existT _ ?a ?c =>
     generalize (inj_pair2 _ _ a b c H); clear H; intro H; invT H
  | existT _ _ _ = existT _ _ _ => 
       let HH := fresh in (injection H; intros _ HH; invT HH; invT H)
  | _ => inv H
 end.

Ltac invSome :=
 match goal with 
 | H: match ?A with Some _ =>  _ | None => None end = Some _ |- _ => 
        let Hx := fresh in
               (revert H; case_eq A; [intros ? H Hx | intros H Hx]; inv Hx)
 | H: match ?A with Some _ => _  | None => False end |- _ =>
             (revert H; case_eq A; [intros ? H ? | intros; contradiction])
 | H: match ?A as x return (x=?A -> _) with Some _ => _ | None => _ end (refl_equal ?A)
                      = Some _ |- _ =>
        let Hx := fresh in 
           (revert H; generalize (refl_equal A); pattern A at 1 3; destruct A; 
            [ intros Hx H | intros ? H; discriminate H])
 end.

Ltac split3 := split; [|split].

Lemma if_true: forall (A: Prop) (E: {A}+{~A}) (T: Type) (B C: T), A -> (if E then B else C) = B.
Proof.
intros.
destruct E; auto.
contradiction.
Qed.

Lemma if_false: forall (A: Prop) (E: {A}+{~A}) (T: Type) (B C: T), ~A -> (if E then B else C) = C.
Proof.
intros.
destruct E; auto.
contradiction.
Qed.

(* END Tactics copied from ecm/Coqlib2.v *)

