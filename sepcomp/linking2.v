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
Require Import compcert.common.Globalenvs. 
Require Import compcert.lib.Integers.

Require Import ZArith.

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

(* Export push, pop, empty, nonempty, push_pop, pop_nonempty *)

Definition push      := StackDefs.push.
Definition pop       := StackDefs.pop.
Definition peek      := StackDefs.peek.
Definition empty     := StackDefs.empty.
Definition nonempty  := StackDefs.nonempty.
Definition peek_nonempty := StackDefs.peek_nonempty.
Definition all_pop   := StackDefs.all_pop.

Implicit Arguments empty [T].

(* Dummy signatures, external functions, and core semantics *)

Definition dummy_sig := mksignature [::] None.

Definition dummy_ef  := EF_external xH dummy_sig.

Program Definition dummy_coreSem {G C M: Type} : @CoreSemantics G C M :=
  Build_CoreSemantics G C M
    (fun _ _ _ => None)
    (fun _ => Some (dummy_ef, dummy_sig, [::]))
    (fun _ _ => None)
    (fun _ => None)
    (fun _ _ _ _ _ => False)
    _ _ _ _.
Next Obligation. by []. Qed.

Axiom dummy_genv: forall F V, Genv.t F V. (*FIXME*)

(* Cores are runtime execution units *)

Module Core.
Record t (M: Type) := mk
  { F   : Type
  ; V   : Type
  ; C   : Type
  ; sem : @CoreSemantics (Genv.t F V) C M
  ; ge  :  Genv.t F V
  ; c   :> C
  }.

Definition upd {M: Type} (core : t M) (newC : core.(C)) :=
  {| F     := core.(F)
   ; V     := core.(V)
   ; C     := core.(C)
   ; sem   := core.(sem)
   ; ge    := core.(ge)
   ; c     := newC 
   |}.

Definition dummy {M: Type} : t M := mk dummy_coreSem (dummy_genv unit unit) tt.

End Core.

Definition atExternal {M: Type} (c: Core.t M) :=
  let: (Core.mk F V C coreSem ge c) := c in
  if at_external coreSem c is Some (ef, dep_sig, args) then true
  else false.

(* Linker invariants: 
   -1: all cores except the topmost one are at_external 
   -2: the call stack always contains at least one core *)

Definition wf_callStack {M: Type} (stk: Stack.t (Core.t M)) :=
  [&& all [pred c | atExternal c] (pop stk) & size stk > 0].

(* Call stacks are [stack]s satisfying the [wf_callStack] invariant. *)

Module CallStack.
Record t (M: Type) : Type := mk
  { callStack :> Stack.t (Core.t M)
  ; _         :  wf_callStack callStack 
  }.

End CallStack.

Section callStackDefs.
Context {M: Type} (stack: CallStack.t M).

Import CallStack.

Definition callStackSize := size stack.(callStack).

Program Definition singl_callStack (core: Core.t M) := 
  CallStack.mk [:: core] _.

Definition dummy_callStack := singl_callStack Core.dummy.

Lemma callStack_wf : wf_callStack stack.
Proof. by case: stack. Qed.

Lemma callStack_ext : all [pred c | atExternal c] (pop stack).
Proof. by move: callStack_wf; move/andP=> [H1 H2]. Qed.

Lemma callStack_size : callStackSize > 0.
Proof. by move: callStack_wf; move/andP=> [H1 H2]. Qed.

End callStackDefs.

Module Payload.
Record t (M: Type) := mk
  { F   : Type
  ; V   : Type
  ; ge  : Genv.t F V
  ; C   : Type
  ; coreSem : @CoreSemantics (Genv.t F V) C M
  ; c   : C
  }.

Definition dummy (M: Type) := 
  @mk M unit unit (dummy_genv _ _) unit dummy_coreSem tt.

End Payload.

(* The first two fields of this record are static configuration data:  
   -[cores] is a function from module id's ('I_n, or integers in the range [0..n-1]) 
    to genvs and core semantics, with existentially quantified core type [C]. 
   -[fn_tbl] maps external function id's to module id's
   [stack] is used to maintain a stack of cores, at runtime. 
   Parameter [N] is the number of static modules in the program. *)

Record linker (M: Type) (N: nat) := mkLinker
  { cores : 'I_N  -> Payload.t M
  ; fn_tbl: ident -> option 'I_N
  ; stack : CallStack.t M
  }.

Implicit Arguments mkLinker [M N].

Section linkerDefs.
Context {M: Type} {N: nat} (l: linker M N).

Import CallStack. (*for coercion [callStack]*)

Definition dummy_linker := 
  mkLinker (fun _ : 'I_N => Payload.dummy M) (fun id => None) dummy_callStack.

Section emptyLinker.
Variables (my_cores: 'I_N -> Payload.t M) (my_fun_tbl : ident -> option 'I_N).

Definition empty_linker := mkLinker my_cores my_fun_tbl dummy_callStack.

Lemma empty_linker_ext :
  all [pred c | atExternal c] empty_linker.(stack).(CallStack.callStack).
Proof. by []. Qed.  

End emptyLinker.

Definition updStack (newStack: CallStack.t M) :=
  {| cores  := l.(cores)
   ; fn_tbl := l.(fn_tbl)
   ; stack  := newStack
  |}.

(* [inContext]: The top core on the call stack has a return context *)

Definition inContext (l0 : linker M N) := callStackSize l0.(stack) > 1.

(* [updCore]: Replace the top core on the call stack with [newCore] *)

Program Definition updCore (newCore: Core.t M) := 
  updStack (CallStack.mk (push (pop l.(stack)) newCore) _).  
Next Obligation. apply/andP; split=>/=; last by []; by apply: callStack_ext. Qed.

(* [pushCore]: Push a new core onto the call stack.  
   Succeeds only if all cores are currently at_external. *)

Program Definition pushCore 
  (newCore: Core.t M) (_ : all [pred c | atExternal c] l.(stack).(callStack)) := 
  updStack (CallStack.mk (push l.(stack) newCore) _).
Next Obligation. by rewrite/wf_callStack; apply/andP; split. Qed.

(* [popCore]: Pop the top core on the call stack.  
   Succeeds only if the top core is running in a return context. *)

Lemma inContext_wf (stk : Stack.t (Core.t M)) : 
  size stk > 1 -> wf_callStack stk -> wf_callStack (pop stk).
Proof.
rewrite/wf_callStack=> H1; move/andP=> [H2 H3]; apply/andP; split.
by apply: all_pop.
by move: H1 H2 H3; case: stk.
Qed.

Program Definition popCore : option (linker M N) := 
  (match inContext l as pf return (pf = inContext l -> option (linker M N)) with
    | true => fun pf => 
        Some (updStack (CallStack.mk (pop l.(stack)) (inContext_wf _ _ _)))
    | false => fun pf => None
  end) Logic.eq_refl.
Next Obligation. by apply: callStack_wf. Qed.

Definition peekCore := peek l.(stack).

Definition emptyStack := if l.(stack).(callStack) is [::] then true else false.

Lemma peekCore_nempty c : peekCore = Some c -> emptyStack = false.
Proof. by rewrite/peekCore/peek/emptyStack/StackDefs.peek; case: (callStack _). Qed.

Definition initCore (ix: 'I_N) (v: val) (args: list val): option (Core.t M) :=
  let: Payload.mk F V ge C coreSem c := l.(cores) ix in
  if initial_core coreSem ge v args is Some c then Some (Core.mk coreSem ge c)
  else None.

End linkerDefs.

(* The linking semantics *)

Module LinkerSem. Section linkerSem.
Variables M : Type.
Variable  N : nat.  (* Number of (compile-time) modules *)
Variable my_cores : 'I_N  -> Payload.t M.
Variable my_fn_tbl: ident -> option 'I_N.

(* [handle id l args] looks up function id [id] in function table [l.fn_tbl], 
   producing an optional module index [ix : 'I_N].  The index is used to 
   construct a new core to handle the call to function [id]. The new core 
   is pushed onto the call stack. *)

Section handle.
Variables (id: ident) (l: linker M N) (args: list val).

Import CallStack.

Definition handle :=
  (match all [pred c | atExternal c] l.(stack).(callStack) as pf 
        return (pf = all [pred c | atExternal c] l.(stack).(callStack) 
               -> option (linker M N)) with
    | true => fun pf => 
        if l.(fn_tbl) id is Some ix then
        if initCore l ix (Vptr id Int.zero) args is Some c 
          then Some (pushCore l c (Logic.eq_sym pf))
        else None else None
    | false => fun _ => None
  end) Logic.eq_refl.

End handle.

Definition initial_core (tt: unit) (v: val) (args: list val)
  : option (linker M N) :=
  if v is Vptr id ofs then handle id (empty_linker my_cores my_fn_tbl) args 
  else None.

(* Is the running core at_external? *)

Definition at_external0 (l: linker M N) :=
  let: mc := peekCore l in
  if mc is Some c then at_external (Core.sem c) (Core.c c) else None.

(* Is the running core halted? *)

Definition halted0 (l: linker M N) :=
  let: mc := peekCore l in
  if mc is Some c then halted (Core.sem c) (Core.c c) else None.

(* Lift a running core step to linker step *)

Definition corestep0 (l: linker M N) (m: M) (l': linker M N) (m': M) := 
  let: mc := peekCore l in
  if mc is Some c then 
    exists c', corestep (Core.sem c) (Core.ge c) (Core.c c) m c' m'
            /\ l' = updCore l (Core.upd c c')
  else False.

Definition fun_id (ef: external_function) : option ident :=
  if ef is (EF_external id sig) then Some id else None.

(* The linker is [at_external] whenever the top core is [at_external] and 
   the [id] of the called external function isn't handleable by any 
   compilation unit. *)

Definition at_external (l: linker M N) :=
  if at_external0 l is Some (ef, dep_sig, args) 
    then if fun_id ef is Some id then
         if handle id l args is None then Some (ef, dep_sig, args) else None
         else None
  else at_external0 l.

Definition after_external (mv: option val) (l: linker M N) :=
  let: mc := peekCore l in
  if mc is Some c then 
    if after_external (Core.sem c) mv (Core.c c) is Some c' then 
      Some (updCore l (Core.upd c c'))
    else None
  else None.

(* The linker is [halted] when the last core on the call stack is halted. *)

Definition halted (l: linker M N) := 
  if ~~inContext l then 
  if halted0 l is Some rv then Some rv
  else None else None.


Definition corestep (ge: unit) (l: linker M N) (m: M) (l': linker M N) (m': M) := 
  (* 1- The running core takes a step, or *)
  corestep0 l m l' m' \/

  (* 2- We're in a function call context. In this case, the running core is either *)
  (if inContext l then 

      (* 3- at_external, in which case we push a core onto the stack to handle 
         the external function call (or this is not possible because no module 
         handles the external function id, in which case the entire linker is 
         at_external) *)

      if at_external0 l is Some (ef, dep_sig, args) then
      if fun_id ef is Some id then
      if handle id l args is Some l'' then l'=l'' else False else False
      else 

      (* 4- or halted, in which case we pop the halted core from the call stack
         and inject its return value into the caller's corestate. *)

      if halted0 l is Some rv then
      if popCore l is Some l0 then 
      if after_external (Some rv) l0 is Some l'' then l'=l'' 
      else False else False else False

   else False).


Lemma corestep_not_at_external0 m c m' c' :
  corestep0 c m c' m' -> at_external0 c = None.
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

Lemma corestep_not_halted0 m c m' c' :
  corestep0 c m c' m' -> halted c = None.
Proof.
rewrite/corestep0/halted; case Heq: (peekCore c)=>//[a].
move=> [newCore [H1 H2]]. 
case Hcx: (~~ inContext _)=>//; case Hht: (halted0 _)=>//.
by move: Hht; apply corestep_not_halted in H1; rewrite/halted0 Heq H1.
Qed.

Lemma corestep_not_at_external ge m c m' c' :
  corestep ge c m c' m' -> at_external c = None.
Proof.
rewrite/corestep/at_external. 
move=> [H|H]; first by move: H; move/corestep_not_at_external0=> ->.
move: H; case Hcx: (inContext _)=>//.
case Heq: (at_external0 c)=>//[[[ef sig] args]].
move: Heq; case: (at_external_halted_excl0 c)=> [H|H]; first by rewrite H.
by move=> H2; case: (fun_id ef)=>// id; case: (handle _ _ _).
Qed.

Lemma at_external0_not_halted c x :
  at_external0 c = Some x -> halted c = None.
Proof.
case: (at_external_halted_excl0 c); rewrite/at_external0/halted.
by case Heq: (peekCore c)=>//[a] ->.
move=> H; case Heq: (peekCore c)=>//[a]. 
by case Hcx: (~~ inContext _)=>//; rewrite H.
Qed.

Lemma corestep_not_halted ge m c m' c' :
  corestep ge c m c' m' -> halted c = None.
Proof. 
rewrite/corestep/halted.
move=> [H|H]; first by move: H; move/corestep_not_halted0.
by move: H; case Hcx: (inContext _).
Qed.

Lemma at_external_halted_excl c :
  at_external c = None \/ halted c = None.
Proof.
rewrite/at_external/halted; case Hat: (at_external0 c)=>//; 
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
move: Hat; rewrite/at_external0=>/= H2.
by apply after_at_external_excl in Heq; rewrite Heq in H2; congruence.
Qed.

Definition coreSem := 
  Build_CoreSemantics unit (linker M N) M 
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
