Require Import sepcomp.extspec.
Require Import sepcomp.Address.
Require Import sepcomp.core_semantics.
Require Import sepcomp.step_lemmas.
Require Import sepcomp.forward_simulations.

Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.

(*NOTE: because of redefinition of [val], these imports must appear 
  after Ssreflect eqtype.*)
Require Import compcert.common.AST.    (*for typ*)
Require Import compcert.common.Values. (*for val*)
Require Import compcert.lib.Integers.

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
Definition pop  (stack: Stack.t T) : seq T := 
  if stack is [:: topT & rest] then rest else [::].
Definition empty : Stack.t T := [::].

Definition nonempty : pred (Stack.t T) := 
  [pred s | if s is [::] then false else true].

Lemma peek_push (t : T) (stack : Stack.t T) : peek (push stack t) = Some t.
Proof. by []. Qed.

Lemma pop_push (t : T) (stack : Stack.t T) : pop (push stack t) = stack.
Proof. by []. Qed.

Lemma peek_nonempty (stack : Stack.t T) : 
  nonempty stack -> exists t, peek stack = Some t.
Proof. by case: stack=>// a l _; exists a. Qed.

End stackDefs. End StackDefs.

(* Export push, pop, empty, nonempty, push_pop, pop_nonempty *)
Definition push      := StackDefs.push.
Definition pop       := StackDefs.pop.
Definition peek      := StackDefs.peek.
Definition empty     := StackDefs.empty.
Definition nonempty  := StackDefs.nonempty.
Definition peek_push := StackDefs.peek_push.
Definition pop_push  := StackDefs.pop_push.
Definition peek_nonempty := StackDefs.peek_nonempty.

Implicit Arguments empty [T].

(* Cores are runtime execution units *)
Module Core.
Record t (G M: Type) := mk
  { C   : Type
  ; sem : @CoreSemantics G C M
  ; ge  :  G
  ; c   :> C
  }.

Definition upd {G M: Type} (core : t G M) (newC : core.(C)) :=
  {| C     := core.(C)
   ; sem   := core.(sem)
   ; ge    := core.(ge)
   ; c     := newC 
   |}.

Program Definition nullCoreSem {G C M: Type} : @CoreSemantics G C M :=
  Build_CoreSemantics G C M
    (fun _ _ _ => None)
    (fun _ => None)
    (fun _ _ => None)
    (fun _ => None)
    (fun _ _ _ _ _ => False)
    _ _ _ _.

Definition null {G M: Type} (ge: G) : t G M := mk nullCoreSem ge tt.
End Core.

Record linker (G M: Type) (N: nat) := mkLinker
  (* The first two fields of this record are static configuration data:  
     -[cores] is a function from module id's ('I_n, or integers in the range [0..n-1]) 
      to genvs and core semantics, with existentially quantified core type [C]. 
     -[fn_tbl] maps external function id's to module id's
     [stack] is used to maintain a stack of cores, at runtime. *)
  { cores : 'I_N  -> (G * {C: Type & @CoreSemantics G C M})%type
  ; fn_tbl: ident -> option 'I_N
  ; stack : Stack.t (Core.t G M)
  }.

Implicit Arguments mkLinker [G M N].

Section linkerDefs.
Context {G M: Type} {N: nat} (l: linker G M N).

Definition updStack (newStack: Stack.t (Core.t G M)) :=
  {| cores  := l.(cores)
   ; fn_tbl := l.(fn_tbl)
   ; stack  := newStack
  |}.

Definition pushCore (newCore: Core.t G M) := 
  updStack (push l.(stack) newCore).

Definition popCore := 
  updStack (pop l.(stack)).

Definition peekCore := peek l.(stack).

Definition emptyStack := if l.(stack) is [::] then true else false.

Lemma peekCore_nempty c : peekCore = Some c -> emptyStack = false.
Proof. by rewrite/peekCore/peek/emptyStack/StackDefs.peek; case: (stack l). Qed.

Definition initCore (ix: 'I_N) (v: val) (args: list val): option (Core.t G M) :=
  let: (ge, (existT C coreSem)) := l.(cores) ix in
  if initial_core coreSem ge v args is Some c then Some (Core.mk coreSem ge c)
  else None.

End linkerDefs.

Lemma peek_pushCore {G M: Type} {N: nat} c (l: linker G M N) : 
  peekCore (pushCore l c) = Some c.
Proof. by []. Qed.

(* The linking semantics *)

Module LinkerSem. Section linkerSem.
Variables G M: Type.
Variable  N  : nat.  (* Number of modules *)
Variable my_cores : 'I_N  -> (G * {C: Type & @CoreSemantics G C M})%type.
Variable my_fn_tbl: ident -> option 'I_N.

Definition initial_core (ge: G) (v: val) (args: list val): option (linker G M N) :=
  Some (mkLinker my_cores my_fn_tbl empty). 

Definition at_external0 (l: linker G M N) :=
  let: mc := peekCore l in
  if mc is Some c then at_external (Core.sem c) (Core.c c) else None.

Definition halted0 (l: linker G M N) :=
  let: mc := peekCore l in
  if mc is Some c then halted (Core.sem c) (Core.c c) else None.

Definition corestep0 (ge: G) (l: linker G M N) (m: M) (l': linker G M N) (m': M) := 
  let: mc := peekCore l in
  if mc is Some c then 
    exists c', corestep (Core.sem c) ge (Core.c c) m c' m'
            /\ l' = pushCore l (Core.upd c c')
  else False.

Definition handle (id: ident) (l: linker G M N) (args: list val) :=
  if l.(fn_tbl) id is Some ix then
    if initCore l ix (Vptr id Int.zero) args is Some c then Some (pushCore l c) else None
  else None.

Definition fun_id (ef: external_function) : option ident :=
  if ef is (EF_external id sig) then Some id else None.

Definition at_external (l: linker G M N) :=
  if at_external0 l is Some (ef, dep_sig, args) 
    then if fun_id ef is Some id then
         if handle id l args is None then Some (ef, dep_sig, args) else None
         else None
  else at_external0 l.

Definition after_external (mv: option val) (l: linker G M N) :=
  let: mc := peekCore l in
  if mc is Some c then 
    if after_external (Core.sem c) mv (Core.c c) is Some c' then 
      Some (pushCore (popCore l) (Core.upd c c'))
    else None
  else None.

Definition halted (l: linker G M N) := 
  if emptyStack l then Some (Vint Int.zero) else None.

Definition corestep (ge: G) (l: linker G M N) (m: M) (l': linker G M N) (m': M) := 
  if halted0 l is Some rv 
    then if after_external (Some rv) (popCore l) is Some l'' then l'=l'' else False
  else 
  if at_external0 l is Some (ef, dep_sig, args) 
    then if fun_id ef is Some id then 
         if handle id l args is Some l'' then l'=l'' else False
         else False
  else corestep0 ge l m l' m'.

Lemma corestep_not_at_external0 ge m c m' c' :
  corestep0 ge c m c' m' -> at_external0 c = None.
Proof.
rewrite/corestep0/at_external0; case: (peekCore c)=>// a [newCore][H1 H2].
by apply corestep_not_at_external in H1.
Qed.

Lemma at_external_halted_excl0 c :
  at_external0 c = None \/ halted0 c = None.
Proof.
rewrite/at_external0/halted0; case: (peekCore c); last by right.
by move=> a; apply: at_external_halted_excl.
Qed.

Lemma corestep_not_halted0 ge m c m' c' :
  corestep0 ge c m c' m' -> halted c = None.
Proof.
rewrite/corestep0/halted; case Heq: (peekCore c)=>//[a].
by move=> [newCore [H1 H2]]; rewrite (@peekCore_nempty _ _ _ c a).
Qed.

Lemma corestep_not_at_external ge m c m' c' :
  corestep ge c m c' m' -> at_external c = None.
Proof.
rewrite/corestep/at_external. 
case Heq: (at_external0 c)=>//[[[ef sig] args]].
case Hht: (halted0 c)=>//. 
case Hat: (after_external _ _)=>// _.
by case: (at_external_halted_excl0 c)=> [H|H]; congruence.
by move: Heq; case: (fun_id ef)=>// id H; case: (handle _ _ _).
Qed.

Lemma halted0_not_halted c rv :
  halted0 c = Some rv -> halted c = None.
Proof.
rewrite/halted0/halted.
by case Heq: (peekCore c)=>//[a] H; rewrite (@peekCore_nempty _ _ _ c a).
Qed.

Lemma at_external0_not_halted c x :
  at_external0 c = Some x -> halted c = None.
Proof.
rewrite/at_external0/halted.
by case Heq: (peekCore c)=>//[a] H; rewrite (@peekCore_nempty _ _ _ c a).
Qed.

Lemma corestep_not_halted ge m c m' c' :
  corestep ge c m c' m' -> halted c = None.
Proof.
rewrite/corestep/halted. 
case Hht: (halted0 c)=>//. 
by move=> _; apply: (halted0_not_halted _ Hht).
case Hat: (at_external0 c)=>// H. 
by apply: (at_external0_not_halted _ Hat).
by apply: (corestep_not_halted0 _ _ _ _ _ H).
Qed.

Lemma at_external_halted_excl c :
  at_external c = None \/ halted c = None.
Proof.
rewrite/at_external/halted; case: (peekCore c).
move=> a; case Hat: (at_external0 c)=>//; 
first by right; apply: (at_external0_not_halted _ Hat). 
by left.
case Hat: (at_external0 c)=>//; 
first by right; apply: (at_external0_not_halted _ Hat).
by left.
Qed.

Lemma after_at_external_excl rv c c' :
  after_external rv c = Some c' -> at_external c' = None.
Proof.
rewrite/after_external/at_external; case: (peekCore c)=>// a. 
case Heq: (core_semantics.after_external _ _ _)=>//.
inversion 1; subst.
case Hat: (at_external0 _)=>//[[[ef sig] args]].
move: Hat; rewrite/at_external0.
rewrite peek_pushCore=> H2.
by apply after_at_external_excl in Heq; rewrite Heq in H2; congruence.
Qed.

Definition coreSem := 
  Build_CoreSemantics G (linker G M N) M 
    initial_core
    at_external
    after_external
    halted 
    corestep
    corestep_not_at_external    
    corestep_not_halted 
    at_external_halted_excl
    after_at_external_excl.

End linkerSem. End LinkerSem.
