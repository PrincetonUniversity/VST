Require Import VST.floyd.proofauto.

(********* EExists *********************************************************************
 * This tactic is like eexists. It instantiates EX qualtifier with
 * unification variables.
 *)
Goal forall {cs:compspecs} (p q : val),
  data_at Tsh (tptr tint) q p
    |-- EX q0:val, data_at Tsh (tptr tint) q0 p.
Proof.
  intros.
  EExists.
  entailer!.
Qed.

(* In EX _:T, _, if T is a tuple type, EExists automatically destruct it.
 * This design is because forward_loop tactics integrate multiple EXs
 * into single one. Please use EExists_alt to instantiate tuple with a
 * single unification variable.
 *)
Goal forall {cs:compspecs} (p q : val),
  data_at Tsh (tptr tint) q p
    |-- EX a:val*val, data_at Tsh (tptr tint) (fst a) (snd a).
Proof.
  intros.
  EExists.
  simpl fst. simpl snd.
  entailer!.
Qed.

(********* ecancel *********************************************************************
 * ecancel is a augmented version of cancel. First, it unifies unification variables.
 * Second, it unifies different kinds of discription of memory automatically, e.g.
 * data_at, field_at, data_at_ and field_at_. ecancel should be almost as fast as cancel.
 * Please report if you find ecancel is slower than expected.
 *)

Goal forall (listrep : list val -> val -> mpred) p al, listrep al p |-- EX p0:val, listrep al p0.
Proof.
  intros.
  EExists.
  cancel. (* cancel does nothing. *)
  ecancel.
Qed.

(********* sep_apply *********************************************************************
 * Now, sep_apply can infer arguments by itself. If there are more than one possibilities,
 * sep_apply may match any one.
 *)

Goal forall P Q R (x y : val),
  (forall x y, P x * Q y |-- R) ->
  P x * Q y |-- R.
Proof.
  intros.
  sep_apply H.
  cancel.
Qed.

(********* sep_eapply *********************************************************************
 * sep_eapply is like sep_apply, but allowes leaving unification variables.
 *)

Goal forall P Q R (x y : val),
  (forall x y (z : val), P x * Q y |-- R) ->
  P x * Q y |-- R.
Proof.
  intros.
  Fail sep_apply H.
  (* It fails because z is not found. *)
  sep_eapply H.
  cancel.
  Unshelve.
  auto.
Qed.

(* Please use sep_eapply (allp_instantiate' (B := _)) to instantiate ALL quantifier. *)
Goal forall P (x : val),
  ALL y:val, P y |-- P x.
Proof.
  intros.
  sep_eapply allp_instantiate'.
  ecancel.
Qed.

(* Please use wand_frame_elim'' instead of wand_frame_elim to help sep_apply to find (P -* Q) first. *)
Goal forall A B,
  (A -* B) * A |-- B.
Proof.
  intros.
  Fail sep_apply wand_frame_elim.
  (* It fails because sep_apply matches (P := (A -* B)). *)
  sep_apply wand_frame_elim''.
  cancel.
Qed.