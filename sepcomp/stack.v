Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.

Module Stack.
Definition t (T : Type) := seq T.
End Stack.

Module StackDefs. Section stackDefs.
Variable T : Type.

Import Stack.

Definition updStack (newStack : seq T) := newStack.
Definition push (stack: Stack.t T) (t: T) := updStack [:: t & stack].
Definition peek (stack: Stack.t T) : option T :=
  if stack is [:: topT & rest] then Some topT else None.
Definition pop  (stack: Stack.t T) : Stack.t T := behead stack.
Definition empty : Stack.t T := [::].

Definition nonempty : pred (Stack.t T) := 
  [pred s | if s is [::] then false else true].

Lemma peek_nonempty (stack : Stack.t T) : 
  nonempty stack -> exists t, peek stack = Some t.
Proof. by case: stack=>// a l _; exists a. Qed.

Lemma all_pop (stack : Stack.t T) p : all p stack -> all p (pop stack).
Proof. by case: stack=>//= a l; move/andP=> [H1 H2]. Qed.

End stackDefs. End StackDefs.

(** Export push, pop, empty, nonempty, push_pop, pop_nonempty *)

Definition push      := StackDefs.push.
Definition pop       := StackDefs.pop.
Definition peek      := StackDefs.peek.
Definition empty     := StackDefs.empty.
Definition nonempty  := StackDefs.nonempty.
Definition peek_nonempty := StackDefs.peek_nonempty.
Definition all_pop   := StackDefs.all_pop.

Implicit Arguments empty [T].
