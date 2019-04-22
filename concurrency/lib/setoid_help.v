
Require Import Coq.Classes.Morphisms.
Require Import Relation_Definitions.


Import Logic.
Import Basics.

(*Proper IFF tac*)
Ltac respectful_intros:=
  match goal with
  |  |- (_ ==> _)%signature _ _ => intros ???; respectful_intros
  | |- impl _ _ => unfold impl
  | _ => idtac
  end.
Ltac proper_intros:=
  intros;
  match goal with
    |- Proper (_ ==> _) _ => unfold Proper; respectful_intros
  end; intros.

Class two_way_relation {T} Rimpl Riff:=
  {TwoWay: forall (x y:T), Rimpl x y -> Rimpl y x -> Riff x y}.

Instance TwoWayIff:
  two_way_relation impl iff.
Proof. constructor; intros ????. split; auto. Qed.

Lemma Proper_two_way
   {A B} {R1 R2: relation B} {a: relation A} {f: A -> B}
    `{Syma: Symmetric _ a}
    `{TwoWay:two_way_relation _ R1 R2}:
    Proper (a ==> R1) f ->
    Proper (a ==> R2) f.
Proof. proper_intros; eapply TwoWay; eapply H ; auto. Qed.

(* BUGish: [Check Proper_two_way] binds to iff impl *)

Ltac proper_iff:=
  intros;
  match goal with
    |- Proper _ _ =>
    eapply Proper_two_way; auto
  end.

Instance two_way2
   {A B} {a: relation A} {b1 b2: relation B}
    `{Syma:Symmetric _ a}
    `{TwoWay:two_way_relation _ b1 b2}:
    two_way_relation (a ==> b1)%signature (a ==> b2)%signature.
Proof. intros. constructor; intros ???? ???. eapply TwoWay; eauto. Qed.


(* Example :
Lemma Proper_iff3:
  forall {A} (a b c: relation A) f,
    `(Symmetric a) ->
    `(Symmetric b) ->
    `(Symmetric c) ->
    Proper (a ==> b ==> c ==> impl) f ->
    Proper (a ==> b ==> c ==>  iff) f.
Proof. proper_iff. Qed.
*)
