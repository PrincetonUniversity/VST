Load loadpath. Load ssrloadpath.
Require Import veristar.basic veristar.variables.
Require Import ssreflect ssrbool ssrnat ssrfun seq eqtype.
Require Import NArith NOrderedType.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Definition var := N.

Definition val := N.

Definition addr := N.

Definition label := N.

(** integer and address expressions *)

Inductive abinop : Type :=
| Aplus
| Aminus
| Amult.

Inductive aexpr : Type :=
| AEvar : var -> aexpr
| AEval : val -> aexpr
| AEbinop : abinop -> aexpr -> aexpr -> aexpr.

(** boolean expressions *)

Inductive expr : Type :=
| Etrue
| Efalse
| Eneg : expr -> expr
| Eleq : aexpr -> aexpr -> expr
| Eand : expr -> expr -> expr
| Eor : expr -> expr -> expr
| Eaddr_eq : aexpr -> aexpr -> expr.

(** commands *)

Inductive stmt : Type :=
| Sskip : stmt
| Sassume : expr -> stmt
| Sassert : expr -> stmt
| Sassign : var -> aexpr -> stmt
| Sload : var -> aexpr -> stmt
| Sstore : aexpr -> aexpr -> stmt.

(** continuations *)

Inductive cont : Type :=
| Ksafe
| Kseq : stmt -> cont -> cont
| Kifte : expr -> cont -> cont -> cont
| Kgoto : label -> cont.

(** programs *)

Definition prog := label -> option cont.

(** states *)

Definition store := var -> option val.

Definition heap := addr -> option val.

Inductive state : Type := State : store -> heap -> state.

(** executable semantics *)

Definition eval_abinop (op : abinop) :=
  match op with
    | Aplus => Nplus
    | Aminus => Nminus
    | Amult => Nmult
  end.

Section eval_aexpr.
Variable (s : store).

Fixpoint eval_aexpr (ae : aexpr) : option val :=
  match ae with
    | AEvar x => s x
    | AEval n => Some n
    | AEbinop op e1 e2 =>
        obnd (fun n1 => obnd (fun n2 => Some (eval_abinop op n1 n2))
          (eval_aexpr e2)) (eval_aexpr e1)
  end.

End eval_aexpr.

Section eval_expr.
Variables (s : store) (h : heap).

Fixpoint eval_expr (e : expr) : option bool :=
  match e with
    | Etrue => Some true
    | Efalse => Some false
    | Eneg e' => obnd (fun b => Some (negb b)) (eval_expr e')
    | Eleq ie1 ie2 =>
        obnd (fun n1 => obnd (fun n2 => Some (Nleb n1 n2))
          (eval_aexpr s ie1)) (eval_aexpr s ie2)
    | Eand e1 e2 =>
        obnd (fun b1 => obnd (fun b2 => Some (andb b1 b2))
          (eval_expr e1)) (eval_expr e2)
    | Eor e1 e2 =>
        obnd (fun b1 => obnd (fun b2 => Some (orb b1 b2))
          (eval_expr e1)) (eval_expr e2)
    | Eaddr_eq ae1 ae2 =>
        obnd (fun a1 => obnd (fun a2 => Some (Neqb a1 a2))
          (eval_aexpr s ae1)) (eval_aexpr s ae2)
  end.

End eval_expr.

Definition store_upd (x : var) (v : val) (s : store) :=
  fun y => if Neqb x y then Some v else s y.

Definition heap_upd (a : addr) (v : val) (h : heap) :=
  fun b => if Neqb a b then Some v else h b.

Definition prog_upd (l : label) (k : cont) (P : prog) :=
  fun l' => if Neqb l l' then Some k else P l'.

Definition empty (_ : var) : option val := None.

Definition empty_prog (_ : var) : option cont := None.

Definition result := option state.

Notation inl := (inl _).
Notation inr := (inr _).

(** we need the bound [n] since programs may in general not terminate *)

Fixpoint eval n (k : cont) (P : prog) (s : store) (h : heap) : result :=
  match n with O => None | S n' =>
  match k with
    | Ksafe => Some (State s h)
    | Kseq Sskip k' => eval n' k' P s h
    | Kseq (Sassume e) k' =>
        obnd (fun b : bool => if b then eval n' k' P s h
                              else Some (State s h)) (eval_expr s e)
    | Kseq (Sassert e) k' =>
        obnd (fun b : bool => if b then eval n' k' P s h
                              else None) (eval_expr s e)
    | Kseq (Sassign x e) k' =>
        obnd (fun v => eval n' k' P (store_upd x v s) h) (eval_aexpr s e)
    | Kseq (Sload x e) k' =>
        obnd (fun l => obnd (fun v => eval n' k' P (store_upd x v s) h) (h l))
          (eval_aexpr s e)
    | Kseq (Sstore e1 e2) k' =>
        obnd (fun l => obnd (fun v => eval n' k' P s (heap_upd l v h))
          (eval_aexpr s e2)) (eval_aexpr s e1)
    | Kifte e k1 k2 =>
        obnd (fun b : bool => if b then eval n' k1 P s h
                              else eval n' k2 P s h) (eval_expr s e)
    | Kgoto l => obnd (fun k' => eval n' k' P s h) (P l)
  end end.

Definition eval_prog n (P : prog) s h := obnd (fun k => eval n k P s h) (P 0%N).

(** interpret a simple program *)

Module T1.

Local Open Scope N_scope.

Definition x : var := 1.
Definition y : var := 2.
Definition z : var := 3.

Definition h1 : heap :=
  heap_upd 4 1 (heap_upd 8 32
    (heap_upd 32 2 (heap_upd 36 12
      (heap_upd 12 3 (heap_upd 16 0 empty))))).

Definition P1 : prog :=
   prog_upd 0
    (Kseq (Sassign x (AEval 4)) (Kgoto 1)) (
  prog_upd 1
    (Kseq (Sload y (AEvar x))
          (Kifte (Eaddr_eq (AEvar y) (AEval 0))
                 (Kseq (Sassert (Eaddr_eq (AEvar y) (AEval 0))) Ksafe)
                 (Kseq (Sassign x (AEbinop Aplus (AEvar x) (AEval 4)))
                       (Kgoto 1))))
  empty_prog).

Compute obnd (fun st => match st with
                          | State s h => s y
                        end) (eval_prog 100 P1 empty h1).

End T1.

(** operational semantics *)

Inductive step {P : prog} : state -> cont -> state -> cont -> Prop :=
| step_Sskip : forall s k, step s (Kseq Sskip k) s k
| step_Sassume1 : forall e s h k,
    eval_expr s e = Some false ->
    step (State s h) (Kseq (Sassume e) k) (State s h) Ksafe
| step_Sassume2 : forall e s h k,
    eval_expr s e = Some true ->
    step (State s h) (Kseq (Sassume e) k) (State s h) k
| step_Sassert : forall e s h k,
    eval_expr s e = Some true ->
    step (State s h) (Kseq (Sassert e) k) (State s h) k
| step_Sassign : forall x e v s h k,
    eval_aexpr s e = Some v ->
    step (State s h) (Kseq (Sassign x e) k) (State (store_upd x v s) h) k
| step_Sload : forall x e v l s h k,
    eval_aexpr s e = Some l -> h l = Some v ->
    step (State s h) (Kseq (Sload x e) k) (State (store_upd x v s) h) k
| step_Sstore : forall e1 e2 v l s h k,
    eval_aexpr s e2 = Some v -> eval_aexpr s e1 = Some l ->
    step (State s h) (Kseq (Sstore e1 e2) k) (State s (heap_upd l v h)) k
| step_Ksafe : forall s, step s Ksafe s Ksafe
| step_Kifte1 : forall e s h k1 k2,
    eval_expr s e = Some true ->
    step (State s h) (Kifte e k1 k2) (State s h) k1
| step_Kifte2 : forall e s h k1 k2,
    eval_expr s e = Some false ->
    step (State s h) (Kifte e k1 k2) (State s h) k2
| step_Kgoto : forall l s k, P l = Some k -> step s (Kgoto l) s k.

Implicit Arguments step [].

(** general properties of step relations *)

Section step.
Variable (state cont : Type).
Variable (step : state -> cont -> state -> cont -> Prop).

Inductive star : state -> cont -> state -> cont -> Prop :=
| star_refl s k : star s k s k
| star_step s k s2 k2 s' k' :
    step s k s2 k2 -> star s2 k2 s' k' -> star s k s' k'.

Inductive stepN : nat -> state -> cont -> state -> cont -> Prop :=
| stepO s k : stepN O s k s k
| stepS s k s2 k2 s' k' n :
    step s k s2 k2 -> stepN n s2 k2 s' k' ->
    stepN (S n) s k s' k'.

Lemma star_stepN s k s' k' :
  star s k s' k' <-> exists n, stepN n s k s' k'.
Proof.
split=>[|[n H1]].
- elim=>{s k s' k'}=>[s k|s k s2 k2 s' k' H1 H2 [n H3]];
[by exists O; apply: stepO|by exists (n.+1); apply: (stepS H1 H3)].
- elim: H1=>{s k s' k'}=>[s k|s k s2 k2 s' k' n' H1 H2 H3];
[by apply: star_refl|by apply: (star_step H1 H3)].
Qed.

Inductive plus : state -> cont -> state -> cont -> Prop :=
| plus_left : forall s k s2 k2 s' k',
    step s k s2 k2 -> star s2 k2 s' k' -> plus s k s' k'.

Lemma plus_step1 s k s' k' :
  plus s k s' k' <-> exists n, stepN (S n) s k s' k'.
Proof.
split=>[|[n H1]].
- case=>{s k s' k'}=>s k s2 k2 s' k' H1.
by move/star_stepN=>[n H2]; exists n; apply: (stepS H1 H2).
- inversion H1; subst; apply: (plus_left H0).
by rewrite star_stepN; exists n.
Qed.

End step.

Implicit Arguments stepS [state step cont s k s' k' n].

Inductive prog_star : state -> prog -> state -> cont -> Prop :=
| star_prog : forall P s k s' k',
    P 0%N = Some k -> star (step P) s k s' k' ->
    prog_star s P s' k'.

(** interpreter is sound *)

Lemma stepN_Ksafe n P (s : state) : stepN (step P) n s Ksafe s Ksafe.
Proof.
move: s; induction n=>[[s h]|[s h]]; first by apply: stepO.
apply: (stepS (State s h) Ksafe); last by apply: (IHn (State s h)).
by apply: step_Ksafe.
Qed.

Lemma eval_soundN n k P s h s' h' :
  eval n k P s h = Some (State s' h') ->
  exists k', stepN (step P) n (State s h) k (State s' h') k'.
Proof.
move: s h s' h' k; induction n=>//s h s' h' k H1; case: k IHn H1.
-(*Ksafe*) by move/(_ s h)=>H1 /=; case=><-<-; exists Ksafe; apply: stepN_Ksafe.
-(*Kseq*) move=>c k; case H: c=>/=[|e|e|x e|x e|e1 e2]H1 H2.
  +(*Sskip*) move: H1; move/(_ _ _ _ _ _ H2)=>[k' H3]; exists k'.
  by apply: (stepS (State s h) k); first by apply: step_Sskip.
  +(*Sassume*) move: H2; case He: (eval_expr s e)=>[/=[]|]//.
  move=>H2; move: H1; move/(_ _ _ _ _ _ H2)=>[k' H3]; exists k'.
  by apply: (stepS (State s h) k); first by apply: step_Sassume2.
  case=><-<-; exists Ksafe; apply: (stepS (State s h) Ksafe)=>//.
  by apply: step_Sassume1. by apply stepN_Ksafe.
  +(*Sassert*) move: H2; case He: (eval_expr s e)=>[/=[]|]//.
  move=>H2; move: H1; move/(_ _ _ _ _ _ H2)=>[k' H3]; exists k'.
  by apply: (stepS (State s h) k); first by apply: step_Sassert.
  +(*Sassign*) move: H2; case He: (eval_aexpr s e)=>[/=a|]//.
  move=>H2; move: H1; move/(_ _ _ _ _ _ H2)=>[k' H3]; exists k'.
  by apply: (stepS (State (store_upd x a s) h) k); first by apply: step_Sassign.
  +(*Sload*) move: H2; case He:(eval_aexpr s e)=>//[/=l]; case Ha:(h l)=>[a|]//=.
  move=>H2; move: H1; move/(_ _ _ _ _ _ H2)=>[k' H3]; exists k'.
  apply: (stepS (State (store_upd x a s) h) k)=>//.
  by apply:(step_Sload _ _ He Ha).
  +(*Sstore*) move: H2.
  case He1: (eval_aexpr s e1)=>//[/=a1]; case He2: (eval_aexpr s e2)=>//[/=a2].
  move=>H2; move: H1; move/(_ _ _ _ _ _ H2)=>[k' H3]; exists k'.
  apply: (stepS (State s (heap_upd a1 a2 h)) k)=>//.
  by apply:(step_Sstore _ _ He2 He1).
-(*Kifte*) move=>e k1 k2 /= H1; case He: (eval_expr s e)=>//[/=[]];
move=>H2; move: H1; move/(_ _ _ _ _ _ H2)=>[k' H3]; exists k'.
by apply: (stepS (State s h) k1); first by apply: step_Kifte1.
by apply: (stepS (State s h) k2); first by apply: step_Kifte2.
-(*Kgoto*) move=>l /= H1; case Hp: (P l)=>//[/=k2]=>H2; move: H1.
move/(_ _ _ _ _ _ H2)=>[k' H3]; exists k'.
by apply: (stepS (State s h) k2)=>//; first by apply: step_Kgoto.
Qed.

Lemma eval_sound n k P s h s' h' :
  eval n k P s h = Some (State s' h') ->
  exists k', star (step P) (State s h) k (State s' h') k'.
Proof.
move=>H1; move: (eval_soundN H1)=>[k' H2]; exists k'.
by rewrite star_stepN; exists n.
Qed.

Lemma eval_prog_sound n P s h s' h' :
  eval_prog n P s h = Some (State s' h') ->
  exists k', prog_star (State s h) P (State s' h') k'.
Proof.
rewrite/eval_prog; case Hp: (P 0%N)=>//[/=k]; move/eval_sound=>[k' H1].
by exists k'; apply: (star_prog Hp).
Qed.

(** safety *)

Section safety.
Variable (state cont : Type).
Variable (step : state -> cont -> state -> cont -> Prop).

Notation star := (star step).
Notation stepN := (stepN step).

Definition safe s k := forall s2 k2,
  star s k s2 k2 -> exists s', exists k', step s2 k2 s' k'.

Definition safeN s k := forall s2 k2 n,
  stepN n s k s2 k2 -> exists s', exists k', step s2 k2 s' k'.

Lemma safe_safeN s k : safe s k <-> safeN s k.
Proof.
rewrite/safe/safeN; split=>H1 s2 k2.
- move=>n H2; case: (H1 s2 k2); first by apply/star_stepN; exists n.
by move=>s' [k' H3]; exists s'; exists k'.
- move/star_stepN=>[n' H2]; case: (H1 _ _ _ H2)=>s' [k' H3].
by exists s'; exists k'.
Qed.

Lemma safety_induction R s k :
  (forall s k, R s k -> exists s', exists k', step s k s' k') ->
  (forall s k s' k', R s k -> step s k s' k' -> R s' k') ->
  R s k -> safe s k.
Proof.
move=>H1 H2 H3; rewrite/safe=>s2 k2/star_stepN=>[[n H4]].
move: s k s2 k2 H3 H4; induction n=>s k s2 k2 H3 H4.
- by inversion H4; subst; apply: H1=>//.
- by inversion H4; subst=>{H4}; apply: (IHn s1 k1 s2 k2 (H2 _ _ _ _ H3 H0)).
Qed.

End safety.

(** simulations *)

Section simulation.
Variables (state cont : Type)
          (R : state -> cont -> state -> cont -> Prop)
          (S T : state -> cont -> state -> cont -> Prop)
          (rank : state -> cont -> nat).

(** T simulates S *)

Definition simulates :=
  forall s1 k1 s1' k1' s2 k2,
    R s1 k1 s2 k2 -> S s1 k1 s1' k1' ->
    exists s2', exists k2', plus T s2 k2 s2' k2' /\ R s1' k1' s2' k2'.

(** T wf-simulates S, with ranking function [rank] *)

Definition wf_simulates :=
  forall s1 k1 s1' k1' s2 k2,
    R s1 k1 s2 k2 -> S s1 k1 s1' k1' ->
    (exists s2', exists k2', plus T s2 k2 s2' k2' /\ R s1' k1' s2' k2') \/
    (rank s1' k1' < rank s1 k1 /\ R s1' k1' s2 k2).

End simulation.
