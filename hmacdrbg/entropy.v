Require Import compcert.lib.Coqlib.
Require Import List. Import ListNotations.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import VST.floyd.functional_base.

Require Import sha.ByteBitRelations. (* TODO this is only here because of bitsToBytes *)

Module Type ABSTRACT_ENTROPY.

Parameter stream: Type.

Inductive error_code: Type :=
| catastrophic_error
| generic_error
.

Inductive result X: Type: Type :=
| success: X -> stream -> @result X
| error : error_code -> stream -> @result X
.

Arguments success {X} _ _.
Arguments error {X} _ _.

Parameter get_bytes: nat -> stream -> result (list byte).
Parameter get_bits: nat -> stream -> result (list bool).

End ABSTRACT_ENTROPY.

Module OPTIONAL_ENTROPY <: ABSTRACT_ENTROPY.

Definition stream: Type := nat -> option bool.

Inductive error_code: Type :=
| catastrophic_error
| generic_error
.

Inductive result X: Type: Type :=
| success: X -> stream -> @result X
| error : error_code -> stream -> @result X
.

Arguments success {X} _ _.
Arguments error {X} _ _.

Fixpoint get_bits (k: nat) (s: stream): result (list bool) :=
  match k with
    | O => success [] s
    | S k' => match get_bits k' s with
                | error e s' => error  e s'
                | success b s' =>
                  match s' O with
                    | None => error catastrophic_error (fun i => match Nat.compare i k' with
                                                                   | Lt => s i
                                                                   | Eq | Gt => s (1 + i)%nat
                                                                 end
                                                       )
                    | Some e => success (b ++ [e]) (fun i => s (k + i)%nat)
                  end
              end
  end.

Example get_bits_test1:
  forall bits s output s',
    bits = [Some false; Some true; Some false; Some false] ->
    s = (fun i => nth i bits None) ->
    success output s' = get_bits (length bits) s ->
    s' = (fun i => s (length bits + i)%nat) /\ output = [false; true; false; false].
Proof.
  intros.
  subst.
  inv H1.
  split.
  extensionality i. destruct i; reflexivity.
  reflexivity.
Qed.

Example get_bits_test2:
  forall bits s output s' s'',
    bits = [Some false; None; Some true; Some false; Some false] ->
    s = (fun i => nth i bits None) ->
    error catastrophic_error s' = get_bits 4%nat s ->
    success output s'' = get_bits 4%nat s' ->
    s'' = (fun i => s (length bits + i)%nat) /\ output = [false; true; false; false].
Proof.
  intros.
  subst.
  inv H1.
  inv H2.
  split.
  extensionality i. reflexivity.
  reflexivity.
Qed.

Example get_bits_test3:
  forall bits s output s' s'',
    bits = [None; Some false; Some true; Some false; Some false] ->
    s = (fun i => nth i bits None) ->
    error catastrophic_error s' = get_bits 4%nat s ->
    success output s'' = get_bits 4%nat s' ->
    s'' = (fun i => s (length bits + i)%nat) /\ output = [false; true; false; false].
Proof.
  intros.
  subst.
  inv H1.
  inv H2.
  split.
  extensionality i. reflexivity.
  reflexivity.
Qed.

Example get_bits_test4:
  forall bits s output s' s'',
    bits = [Some false; Some true; Some false; None; Some false] ->
    s = (fun i => nth i bits None) ->
    error catastrophic_error s' = get_bits 4%nat s ->
    success output s'' = get_bits 4%nat s' ->
    s'' = (fun i => s (length bits + i)%nat) /\ output = [false; true; false; false].
Proof.
  intros.
  subst.
  inv H1.
  inv H2.
  split.
  extensionality i. reflexivity.
  reflexivity.
Qed.
(*
Fixpoint get_bits_concrete (k: nat) (s: stream) (max: nat): @result (list bool) :=
  match k with
    | O => success [] s
    | S k' =>
      match s (max - k)%nat with
        | None => error catastrophic_error (fun i => s (1 + i)%nat)
        | Some bit =>
          match get_bits_concrete k' s max with
            | error e s' => error e (fun i => match Nat.compare i (max - k)%nat with
                                                  | Gt => s' i
                                                  | Eq | Lt => s i
                                     end)
            | success b s' => success (bit::b) (fun i => s (k + i)%nat)
          end
      end
  end
.
Lemma get_bits_concrete_correct:
  forall k s, get_bits k s = get_bits_concrete k s k.
Proof.
  intros k.
  induction k as [|k']; [reflexivity|].
  intros s.
  simpl.
  rewrite IHk'. clear IHk'.
  replace (k' - k')%nat with O by omega.
  remember (s O) as sO.
  destruct sO.
  {
    (* s 0 <> None *)
    (*
    remember (get_bits_concrete k' s k') as result.
    destruct result as [string s' | e s'].
    {
      remember (get_bits_concrete k' s (S k')) as result2.
      destruct result2 as [string2 s'2 | e2 s'2].
      {
        (* case where both result return success *)
        generalize dependent s.
        induction k' as [|k'']; intros.
        simpl in *. inv Heqresult. inv Heqresult2. rewrite <- HeqsO. auto.
        simpl in *. replace (k'' - k'')%nat with O in * by omega. rewrite <- HeqsO in *.
        rewrite IHk''.
      }
      unfold get_bits_concrete.
    }
*)
    induction k' as [|k''].
    {
      simpl. rewrite <- HeqsO.
      reflexivity.
    }
    simpl.
    replace (k'' - k'')%nat with O by omega.
    rewrite <- HeqsO in *.
    replace (match k'' with
             | 0%nat => S k''
             | S l => (k'' - l)%nat
             end) with 1%nat by (destruct k''; omega).

  }
  {
    destruct k' as [|k''].
    {
      simpl. rewrite <- HeqsO.
      replace (fun i : nat =>
      match Nat.compare i 0 with
      | Eq => s (S i)
      | Lt => s i
      | Gt => s (S i)
      end) with (fun i => s (S i)); [reflexivity|].
      extensionality i.
      destruct i as [|i']; reflexivity.
    }
    simpl.
    replace (k'' - k'')%nat with O by omega; rewrite <- HeqsO.
    reflexivity.
  }
  simpl.
  *)

Definition get_bytes (k: nat) (s: stream): result (list byte) :=
  match get_bits (8 * k)%nat s with
    | success bits s' => success (bitsToBytes bits) s'
    | error e s' => error e s'
  end
.

End OPTIONAL_ENTROPY.

Module ENTROPY := OPTIONAL_ENTROPY.

Definition get_entropy (security_strength min_length max_length: Z) (prediction_resistance: bool) s :=
           ENTROPY.get_bytes (Z.to_nat min_length) s.