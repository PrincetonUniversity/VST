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

Lemma peek_nonempty (stack : Stack.t T) t : peek stack = Some t -> nonempty stack.
Proof. by rewrite/peek; case: stack. Qed.

Lemma nonempty_nempty (stack: Stack.t T) : nonempty stack -> [::] = stack -> T.
Proof. by case: stack. Qed.

Definition head (stack: Stack.t T) (pf: nonempty stack) : T :=
  (match stack as s return (s = stack -> T) with 
    | nil => fun pf' => nonempty_nempty pf pf'
    | s :: stack' => fun pf' => s
  end) erefl.

Lemma nonempty_peek (stack : Stack.t T) (pf : nonempty stack) : 
  peek stack = Some (head stack pf).
Proof. by move: pf; case: stack=>// a l _. Qed.

Lemma peeksome_head stack t : 
  peek stack = Some t -> 
  forall pf : nonempty stack, head stack pf = t.
Proof. by rewrite/head; case: stack=> //=; move=> ? ?; case. Qed.

Lemma all_pop (stack : Stack.t T) p : all p stack -> all p (pop stack).
Proof. by case: stack=>//= a l; move/andP=> [H1 H2]. Qed.

End stackDefs. End StackDefs.

(** Export push, pop, empty, nonempty, push_pop, pop_nonempty *)

Definition push      := StackDefs.push.
Definition pop       := StackDefs.pop.
Definition peek      := StackDefs.peek.
Definition head      := StackDefs.head.
Definition empty     := StackDefs.empty.
Definition nonempty  := StackDefs.nonempty.
Definition peek_nonempty := StackDefs.peek_nonempty.
Definition all_pop   := StackDefs.all_pop.

Implicit Arguments empty [T].
