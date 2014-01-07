Require Import sepcomp.extspec.
Require Import sepcomp.Address.
Require Import sepcomp.core_semantics.
Require Import sepcomp.effect_semantics.
Require Import sepcomp.step_lemmas.
Require Import sepcomp.mem_lemmas.
Require Import sepcomp.effect_simulations.

Require Import sepcomp.pos.
Require Import sepcomp.stack.
Require Import sepcomp.core_semantics_lemmas.

Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.

(*NOTE: because of redefinition of [val], these imports must appear 
  after Ssreflect eqtype.*)
Require Import compcert.common.AST.    (*for typ*)
Require Import compcert.common.Values. (*for val*)
Require Import compcert.common.Globalenvs. 
Require Import compcert.lib.Integers.

Require Import ZArith.

(** file: linking.v
    ~~~~~~~~~~~~~~~

This file gives the operational semantics of multi-language linking
via a functor [CoreLinker (Csem : CORESEM)].  [CoreLinker] defines the
following types/modules:

  -[Static.t]: the type of compile-time semantics corresponding to a
  particular translation unit, written in a particular programming
  language and w/ a particular statically allocated initial global
  environment

  -[Core.t]: Runtime states corresponding to dynamic invocations of
  [Static.t]s, initialized from a [Static] module to handle a
  particular external function call made by another [Core]

  -[CallStack.t]: just lists of [Core.t]s satisfying a few
  well-formedness properties

  -[Linker.t]: The type of linker corestates.  Linker states contain:

     =[cores], a function from module id's ('I_N, or integers in the
      range [0..N-1]) to genvs and core semantics

     =[fn_tbl], a table mapping external function id's to module id's,
     and

     =[stack], a callstack used to maintain a stack of cores at
    runtime.  Above, parameter [N] is the number of static modules in
    the program.

  -[LinkerSem]: defines the actual linking semantics. In later parts
  of the file, the [LinkerSem] semantics is shown to be both a
  [CoopCoreSem] and an [EffectSem] (cf. core_semantics.v,
  effect_semantics.v).  *)

(** * Linking semantics *)

(** The [CoreLinker] module gives the operational semantics of linking. 
    It is parameterized by a core semantics [Csem]. *)

Module CoreLinker (Csem : CORESEM).

(** Static semantics of translation units *)

Module Static. 

Record t := mk
  { F   : Type
  ; V   : Type
  ; ge  : Genv.t F V
  ; C   : Type
  ; coreSem : Csem.t (Genv.t F V) C
  ; init : C
  }.

Definition dummy := @mk unit unit Dummy.genv unit Csem.dummy tt.

End Static.

(** [Cores] are runtime execution units. *)

Module Core. Section core.

Variable N : pos.
Variable cores : 'I_N -> Static.t.

Import Static.

Record t := mk
  { i  : 'I_N
  ; c  :> (cores i).(C)
  }.

Definition upd (core : t) (newC : (cores core.(i)).(C)) :=
  {| i := core.(i)
   ; c := newC 
   |}.

Definition dummy : t := mk (i0 N) (cores (i0 N)).(init).

End core. End Core.

Arguments Core.t {N} cores.

Arguments Core.dummy {N} cores. 

Arguments Core.i {N cores} !t /.

Arguments Core.c {N cores} !t /.

Arguments Core.upd {N cores} !core _ /.

(** Linking semantics invariants: 
    -All cores except the topmost one are at_external. 
    -The call stack always contains at least one core. *)

Import Coresem.

Section coreDefs.

Import Static.

Variable N : pos.
Variable cores : 'I_N -> Static.t.

Definition atExternal (c: Core.t cores) :=
  let: (Core.mk i c) := c in
  let: F := (cores i).(F) in
  let: V := (cores i).(V) in
  let: C := (cores i).(C) in
  let: coreSem := (cores i).(coreSem) in
  if @at_external (Genv.t F V) C Csem.M (Csem.instance (T:=coreSem)) c is 
    Some (ef, dep_sig, args) then true
  else false.

Definition wf_callStack (stk: Stack.t (Core.t cores)) :=
  [&& all atExternal (pop stk) & size stk > 0].

End coreDefs.

Arguments atExternal {N} cores c.

(** Call stacks are [stack]s satisfying the [wf_callStack] invariant. *)

Module CallStack. Section callStack.

Context {N : pos} (cores : 'I_N -> Static.t).

Record t : Type := mk
  { callStack :> Stack.t (Core.t cores)
  ; _         :  wf_callStack callStack 
  }.

Program Definition singl (core: Core.t cores) := mk [:: core] _.

Definition dummy := singl (Core.dummy cores).

Section callStackDefs.

Context (stack : t).

Definition callStackSize := size stack.(callStack).

Lemma callStack_wf : wf_callStack stack.
Proof. by case: stack. Qed.

Lemma callStack_ext : all (atExternal cores) (pop stack).
Proof. by move: callStack_wf; move/andP=> [H1 H2]. Qed.

Lemma callStack_size : callStackSize > 0.
Proof. by move: callStack_wf; move/andP=> [H1 H2]. Qed.

Lemma callStack_nonempty : nonempty stack.
Proof. by case: stack=> //; case. Qed.

End callStackDefs. 

End callStack. End CallStack.

(** * [Linker.t]

   The first two fields of this record are static configuration data:  
   -[cores] is a function from module id's ('I_n, or integers in the range [0..n-1]) 
    to genvs and core semantics, with existentially quantified core type [C]. 
   -[fn_tbl] maps external function id's to module id's

   [stack] is used to maintain a stack of cores, at runtime. 
   Parameter [N] is the number of static modules in the program. *)

Module Linker. Section linker.

Variable N : pos.
Variable cores : 'I_N  -> Static.t.

Record t := mkLinker 
  { fn_tbl : ident -> option 'I_N
  ; stack  :> CallStack.t cores
  }.

End linker. End Linker.

Import Linker.

Notation linker := Linker.t.

Section linkerDefs.

Context {N : pos} (my_cores : 'I_N -> Static.t) (l : linker N my_cores).

Import CallStack. (*for coercion [callStack]*)

Definition dummy_linker := 
  let: my_cores := fun _ : 'I_N => Static.dummy in
  @mkLinker _ my_cores (fun id => None) (dummy my_cores).

Section emptyLinker.

Variable my_fun_tbl : ident -> option 'I_N.

Definition empty_linker := @mkLinker _ my_cores my_fun_tbl (dummy my_cores).

End emptyLinker.

Definition updStack (newStack : CallStack.t my_cores) :=
  {| fn_tbl := l.(fn_tbl)
   ; stack  := newStack
   |}.

(** [inContext]: The top core on the call stack has a return context *)

Definition inContext (l0 : linker N my_cores) := callStackSize l0.(stack) > 1.

(** [updCore]: Replace the top core on the call stack with [newCore] *)

Program Definition updCore (newCore: Core.t my_cores) := 
  updStack (CallStack.mk (push (pop l.(stack)) newCore) _).  

Next Obligation. apply/andP; split=>/=; last by []; by apply: callStack_ext. Qed.

Lemma updCore_inj newCore newCore' : 
  updCore newCore = updCore newCore' -> newCore=newCore'.
Proof. by case. Qed.

Lemma updCore_inj_upd c c1 c2 : 
  updCore (Core.upd c c1) = updCore (Core.upd c c2) -> c1=c2.
Proof. 
case=> H1; move: (EqdepFacts.eq_sigT_snd H1); move=> <-. 
by rewrite -Eqdep.Eq_rect_eq.eq_rect_eq.
Qed.

(** [pushCore]: Push a new core onto the call stack.  
    Succeeds only if all cores are currently at_external. *)

Program Definition pushCore 
  (newCore: Core.t my_cores) 
  (_ : all (atExternal my_cores) l.(stack).(callStack)) := 
  updStack (CallStack.mk (push l.(stack) newCore) _).

Next Obligation. by rewrite/wf_callStack; apply/andP; split. Qed.

(** [popCore]: Pop the top core on the call stack.  
    Succeeds only if the top core is running in a return context. *)

Lemma inContext_wf (stk : Stack.t (Core.t my_cores)) : 
  size stk > 1 -> wf_callStack stk -> wf_callStack (pop stk).
Proof.
rewrite/wf_callStack=> H1; move/andP=> [H2 H3]; apply/andP; split.
- by apply: all_pop.
- by move: H1 H2 H3; case: stk.
Qed.

Program Definition popCore : option (linker N my_cores) := 
  (match inContext l as pf return (pf = inContext l -> option (linker N my_cores)) with
    | true => fun pf => 
        Some (updStack (CallStack.mk (pop l.(stack)) (inContext_wf _ _ _)))
    | false => fun pf => None
  end) Logic.eq_refl.

Next Obligation. by apply: callStack_wf. Qed.

(*Definition peekCore := peek l.(stack).*)

Definition peekCore := stack.head l.(stack) (callStack_nonempty l.(stack)).

Definition emptyStack := if l.(stack).(callStack) is [::] then true else false.

(*Lemma peekCore_nempty c : peekCore = Some c -> emptyStack = false.
Proof. by rewrite/peekCore/peek/emptyStack/StackDefs.peek; case: (callStack _). Qed.*)

Import Static.

Definition initCore (ix: 'I_N) (v: val) (args: list val) 
  : option (Core.t my_cores):=
  if @initial_core _ _ _ 
       (Csem.instance (T:=(my_cores ix).(coreSem))) 
       (my_cores ix).(Static.ge) 
       v args 
  is Some c then Some (Core.mk _ my_cores ix c)
  else None.

End linkerDefs.

Notation ge_ty := (Genv.t unit unit).

Arguments updStack {N} {my_cores} !_ _ /.

Arguments updCore {N} {my_cores} !_ _ /.

Arguments pushCore {N} {my_cores} !l _ _ /.

Arguments peekCore {N} {my_cores} !l /.

Arguments emptyStack {N} {my_cores} !l /.

(** The linking semantics *)

Module LinkerSem. Section linkerSem.

Variable N : pos.  (* Number of (compile-time) modules *)
Variable my_cores : 'I_N  -> Static.t.
Variable my_fn_tbl: ident -> option 'I_N.

(** [handle id l args] looks up function id [id] in function table [l.fn_tbl], 
    producing an optional module index [ix : 'I_N].  The index is used to 
    construct a new core to handle the call to function [id]. The new core 
    is pushed onto the call stack. *)

Section handle.

Variables (id: ident) (l: linker N my_cores) (args: list val).

Import CallStack.

Definition handle :=
  (match all (atExternal my_cores) l.(stack).(callStack) as pf 
        return (pf = all (atExternal my_cores) l.(stack).(callStack) 
               -> option (linker N my_cores)) with
    | true => fun pf => 
        if l.(fn_tbl) id is Some ix then
        if initCore my_cores ix (Vptr id Int.zero) args is Some c 
          then Some (pushCore l c (Logic.eq_sym pf))
        else None else None
    | false => fun _ => None
  end) Logic.eq_refl.

End handle.

(** Initial core *)

Definition initial_core (tt: ge_ty) (v: val) (args: list val)
  : option (linker N my_cores) :=
  if v is Vptr id ofs then handle id (empty_linker my_cores my_fn_tbl) args 
  else None.

(** Is the running core at_external? *)

Definition at_external0 (l: linker N my_cores) :=
  let: c   := peekCore l in
  let: ix  := c.(Core.i) in
  let: sem := (my_cores ix).(Static.coreSem) in
  let: F   := (my_cores ix).(Static.F) in
  let: V   := (my_cores ix).(Static.V) in
    @at_external (Genv.t F V) _ _ (Csem.instance (T:=sem)) (Core.c c).

Arguments at_external0 !l.

(** Is the running core halted? *)

Definition halted0 (l: linker N my_cores) :=
  let: c   := peekCore l in
  let: ix  := c.(Core.i) in
  let: sem := (my_cores ix).(Static.coreSem) in
  let: F   := (my_cores ix).(Static.F) in
  let: V   := (my_cores ix).(Static.V) in
    @halted (Genv.t F V) _ _ (Csem.instance (T:=sem)) (Core.c c).

Arguments halted0 !l.

(** Lift a running core step to linker step *)

Definition corestep0 
  (l: linker N my_cores) (m: Csem.M) (l': linker N my_cores) (m': Csem.M) := 
  let: c   := peekCore l in
  let: ix  := c.(Core.i) in
  let: sem := (my_cores ix).(Static.coreSem) in
  let: F   := (my_cores ix).(Static.F) in
  let: V   := (my_cores ix).(Static.V) in
  let: ge  := (my_cores ix).(Static.ge) in
    exists c', 
      @corestep (Genv.t F V) _ _ (Csem.instance (T:=sem)) ge (Core.c c) m c' m'
   /\ l' = updCore l (Core.upd c c').

Arguments corestep0 !l m l' m'.

Definition fun_id (ef: external_function) : option ident :=
  if ef is (EF_external id sig) then Some id else None.

(** The linker is [at_external] whenever the top core is [at_external] and 
    the [id] of the called external function isn't handleable by any 
    compilation unit. *)

Definition at_external (l: linker N my_cores) :=
  if at_external0 l is Some (ef, dep_sig, args) 
    then if fun_id ef is Some id then
         if handle id l args is None then Some (ef, dep_sig, args) else None
         else None
  else at_external0 l.

Definition after_external (mv: option val) (l: linker N my_cores) :=
  let: c   := peekCore l in
  let: ix  := c.(Core.i) in
  let: sem := (my_cores ix).(Static.coreSem) in
  let: F   := (my_cores ix).(Static.F) in
  let: V   := (my_cores ix).(Static.V) in
  let: ge  := (my_cores ix).(Static.ge) in
    if @after_external (Genv.t F V) _ _ (Csem.instance (T:=sem)) mv (Core.c c) 
      is Some c' then Some (updCore l (Core.upd c c'))
    else None.

(** The linker is [halted] when the last core on the call stack is halted. *)

Definition halted (l: linker N my_cores) := 
  if ~~inContext l then 
  if halted0 l is Some rv then Some rv
  else None else None.

(** Corestep relation of linking semantics *)

Definition corestep 
  (ge: ge_ty) 
  (l: linker N my_cores) (m: Csem.M) 
  (l': linker N my_cores) (m': Csem.M) := 

  (** 1- The running core takes a step, or *)
  corestep0 l m l' m' \/

  (** 2- We're in a function call context. In this case, the running core is either *)
  (m=m' 
   /\ ~corestep0 l m l' m' 
   /\ if inContext l then 

      (** 3- at_external, in which case we push a core onto the stack to handle 
         the external function call (or this is not possible because no module 
         handles the external function id, in which case the entire linker is 
         at_external) *)

      if at_external0 l is Some (ef, dep_sig, args) then
      if fun_id ef is Some id then
      if handle id l args is Some l'' then l'=l'' else False else False
      else 

      (** 4- or halted, in which case we pop the halted core from the call stack
         and inject its return value into the caller's corestate. *)

      if halted0 l is Some rv then
      if popCore l is Some l0 then 
      if after_external (Some rv) l0 is Some l'' then l'=l'' 
      else False else False else False

     else False).

Lemma corestep_not_at_external0 m c m' c' :
  corestep0 c m c' m' -> at_external0 c = None.
Proof. by move=>[]newCore []H1 H2; apply corestep_not_at_external in H1. Qed.

Lemma at_external_halted_excl0 c : at_external0 c = None \/ halted0 c = None.
Proof. by apply: at_external_halted_excl. Qed.

Lemma corestep_not_halted0 m c m' c' : corestep0 c m c' m' -> halted c = None.
Proof.
move=> []newCore []H1 H2; rewrite/halted.
case Hcx: (~~ inContext _)=>//; case Hht: (halted0 _)=>//.
by move: Hht; rewrite/halted0; apply corestep_not_halted in H1; rewrite /= H1.
Qed.

Lemma corestep_not_at_external ge m c m' c' : 
  corestep ge c m c' m' -> at_external c = None.
Proof.
rewrite/corestep/at_external.
move=> [H|[_ [_ H]]]; first by move: H; move/corestep_not_at_external0=> /= ->.
move: H; case Hcx: (inContext _)=>//.
case Heq: (at_external0 c)=>[[[ef sig] args]|//].
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
move=> [H|[_ [_ H]]]; first by move: H; move/corestep_not_halted0.
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
rewrite/after_external/at_external.
case Heq: (Coresem.after_external _ _)=>//.
inversion 1; subst.
case Hat: (at_external0 _)=>//[[[ef sig] args]].
move: Hat; rewrite/at_external0=>/= H2.
by apply after_at_external_excl in Heq; rewrite Heq in H2. 
Qed.

Definition coresem : CoreSemantics ge_ty (linker N my_cores) Csem.M :=
  Build_CoreSemantics ge_ty (linker N my_cores) Csem.M 
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

End CoreLinker.

Module Linker := CoreLinker Effectsem. Import Linker.
Module Sem    := Linker.LinkerSem.

(** Specialize to effect semantics *)

Section effingLinker.

Variable N : pos. 
Variable my_cores : 'I_N -> Static.t. 
Variable my_fun_tbl : ident -> option 'I_N.

Import Linker.

Definition effstep0 U (l: linker N my_cores) m (l': linker N my_cores) m' := 
  let: c   := peekCore l in
  let: ix  := c.(Core.i) in
  let: sem := (my_cores ix).(Static.coreSem) in
  let: F   := (my_cores ix).(Static.F) in
  let: V   := (my_cores ix).(Static.V) in
  let: ge  := (my_cores ix).(Static.ge) in
    exists c', 
      @effstep (Genv.t F V) _ sem ge U (Core.c c) m c' m'
   /\ l' = updCore l (Core.upd c c').

Lemma effstep0_unchanged U l m l' m' : 
  effstep0 U l m l' m' ->
  Memory.Mem.unchanged_on (fun b ofs => U b ofs = false) m m'.
Proof. 
rewrite/effstep0; case=> ? [STEP].
by move: {STEP}(effax1 _ _ _ _ _ _ _ STEP)=> [STEP]UNCH H2.
Qed.

Lemma effstep0_corestep0 U l m l' m' : 
  effstep0 U l m l' m' -> Sem.corestep0 l m l' m'.
Proof. 
rewrite/effstep0/Sem.corestep0; case=> c' [STEP].
move: {STEP}(effax1 _ _ _ _ _ _ _ STEP)=> [STEP]UNCH H2.
by exists c'; split.
Qed.

Lemma effstep0_forward U l m l' m' : 
  effstep0 U l m l' m' -> mem_forward m m'.
Proof. 
move/effstep0_corestep0; rewrite/Sem.corestep0. 
by move=> []c' []STEP H1; apply: {STEP}(corestep_fwd _ _ _ _ _ _ STEP). 
Qed.

Definition inner_effstep (ge: ge_ty)
  (l: linker N my_cores) m (l': linker N my_cores) m' := 
  [/\ Sem.corestep ge l m l' m' 
    & Sem.corestep0 l m l' m' -> exists U, effstep0 U l m l' m'].

Definition effstep (ge: ge_ty) V
  (l: linker N my_cores) m (l': linker N my_cores) m' := 
  [/\ Sem.corestep ge l m l' m' 
    & Sem.corestep0 l m l' m' -> effstep0 V l m l' m'].

Section csem.

Notation mycsem := (Sem.coresem N my_cores my_fun_tbl).

Program Definition csem : CoreSemantics ge_ty (linker N my_cores) Memory.Mem.mem := 
  Build_CoreSemantics _ _ _
    (initial_core mycsem)
    (at_external mycsem)
    (after_external mycsem)
    (halted mycsem) 
    inner_effstep _ _ _ _.

Next Obligation. 
move: H; rewrite/inner_effstep=> [[H1] H2]. 
by apply: (Sem.corestep_not_at_external H1).
Qed.

Next Obligation.
move: H; rewrite/inner_effstep=> [[H1] H2]. 
by apply: (Sem.corestep_not_halted H1).
Qed.

Next Obligation. by apply: (Sem.at_external_halted_excl). Qed.
Next Obligation. by apply (Sem.after_at_external_excl _ _ H). Qed.

End csem.

(** Reconstruct coopsem *)

Program Definition coopsem := Build_CoopCoreSem _ _ csem _.

Next Obligation. 
move: CS; case; move=>[H1|[<- [H0 H1]]]. 
by move/(_ H1)=>{H1} [U EFF]; apply (effstep0_forward EFF).
by move=> ?; apply mem_forward_refl.
Qed.

(** Reconstruct effsem *)

Program Definition effsem := Build_EffectSem _ _ coopsem effstep _ _ _.

Next Obligation. 
move: H=>[H1]H2; split. 
by split=> //; move=> H3; move: {H2 H3}(H2 H3)=> STEP; exists M.
case: H1=> [H1|[<- [H0 H1]]]=> //. 
by move: (H2 H1)=> H3; apply: (effstep0_unchanged H3).
Qed.

Next Obligation.
move: H; rewrite/inner_effstep=> [[[H1|[<- [H0 H1]]]]] H2=> //.
move: (H2 H1)=> {H2}[U H3]; exists U; split=> //.
by left; apply: (effstep0_corestep0 H3).
by exists [fun _ _ => false]; split=> //; right.
Qed.

Next Obligation.
move: H; rewrite/effstep=>[[H1]] H2; split=> // H3; move: (H2 H3). 
rewrite/effstep0=> [][]x []STEP ->.
by move: (effstep_sub_val _ _ _ _ _ _ _ _ UV STEP)=> STEP'; exists x; split.
Qed.

End effingLinker.
