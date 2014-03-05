Require Import ssreflect ssrbool ssrnat ssrfun seq.
Set Implicit Arguments.

(* This file defines the type of stacks used to model callstacks in       *)
(* linking.v.                                                             *)

Module SeqStack. Section seqStack.
Variable T : Type.

Definition updStack (newStack : seq T) := newStack.
Definition push (stack: seq T) (t: T) := updStack [:: t & stack].
Definition peek (stack: seq T) : option T :=
  if stack is [:: topT & rest] then Some topT else None.
Definition pop  (stack: seq T) : seq T := behead stack.
Definition empty : seq T := [::].

Definition nonempty : pred (seq T) := 
  [pred s | if s is [::] then false else true].

Lemma peek_nonempty (stack : seq T) t : 
  peek stack = Some t -> nonempty stack.
Proof. by rewrite/peek; case: stack. Qed.

Lemma nonempty_nempty (stack: seq T) : nonempty stack -> [::] = stack -> T.
Proof. by case: stack. Qed.

Definition head (stack: seq T) (pf: nonempty stack) : T :=
  (match stack as s return (s = stack -> T) with 
    | nil => fun pf' => nonempty_nempty pf pf'
    | s :: stack' => fun pf' => s
  end) erefl.

Lemma nonempty_peek (stack : seq T) (pf : nonempty stack) : 
  peek stack = Some (head stack pf).
Proof. by move: pf; case: stack=>// a l _. Qed.

Lemma peeksome_head stack t : 
  peek stack = Some t -> 
  forall pf : nonempty stack, head stack pf = t.
Proof. by rewrite/head; case: stack=> //=; move=> ? ?; case. Qed.

Lemma all_pop (stack : seq T) p : all p stack -> all p (pop stack).
Proof. by case: stack=>//= a l; move/andP=> [H1 H2]. Qed.

End seqStack. 

Arguments empty / {T}.
Arguments push {T} _ _ /.
Arguments pop {T} !_ /.
Arguments peek {T} !_ /.
Arguments nonempty {T} !_ /.
Arguments head {T} !_ _ /.

End SeqStack.

Module STACK. 

Record type (T : Type) : Type := 
  { t : Type
  ; empty: t 
  ; push : t -> T -> t
  ; pop  : t -> t
  ; peek : t -> option T
  ; nonempty : pred t
  ; head : forall t, nonempty t -> T
  ; all  : pred T -> t -> bool 
  ; all_pop : forall t p, all p t -> all p (pop t) }.

End STACK.

Arguments STACK.empty {T t} /.
Arguments STACK.push {T t} _ _ /.
Arguments STACK.pop {T t} _ /.
Arguments STACK.peek {T t} _ /.
Arguments STACK.nonempty {T t} _ /.
Arguments STACK.head {T t} _ _ /.

Coercion STACK.t : STACK.type >-> Sortclass.

Module Stack.

Import SeqStack.

Section Stack.

Variable T : Type.

Definition t : STACK.type T := 
  @STACK.Build_type T (seq T) empty push pop peek nonempty head 
  all (@all_pop T).

End Stack.

End Stack.

Canonical Structure seq_stackTy T : STACK.type T := Stack.t T.

Lemma pop_size U T (stack1 : seq U) (stack2 : seq T)
  (pf1 : 1 <= size stack1) (pf2 : 1 <= size stack2) :
  size (STACK.pop stack1) = size (STACK.pop stack2) -> 
  size stack1 = size stack2.
Proof.
by case: stack1 pf1=> // a s1 ? /=; case: stack2 pf2=> // b s2 ? /= => ->.
Qed.


