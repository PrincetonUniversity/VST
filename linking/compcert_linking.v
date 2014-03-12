(*Require Import sepcomp.extspec.
Require Import sepcomp.Address.
Require Import sepcomp.core_semantics.
Require Import sepcomp.effect_semantics.
Require Import sepcomp.step_lemmas.
Require Import sepcomp.mem_lemmas.
Require Import sepcomp.effect_simulations.*)
Require Import linking.sepcomp. Import SepComp.

Require Import linking.pos.
Require Import linking.stack. 
Require Import linking.core_semantics_lemmas.
Require Import linking.rc_semantics.

Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.

(*NOTE: because of redefinition of [val], these imports must appear 
  after Ssreflect eqtype.*)
Require Import compcert.common.AST.    (*for typ*)
Require Import compcert.common.Values. (*for val*)
Require Import compcert.common.Globalenvs. 
Require Import compcert.common.Memory.
Require Import compcert.lib.Integers.

Require Import ZArith.

(* This file gives the operational semantics of multi-language linking    *)
(* via a functor [CoreLinker (sem : EFFSEM)].  [CoreLinker] defines the   *)
(* following types/modules:                                               *)
(*                                                                        *)
(*   -[Static.t]: the type of compile-time semantics corresponding to a   *)
(*   particular translation unit, written in a particular programming     *)
(*   language and w/ a particular statically allocated initial global     *)
(*   environment                                                          *)
(*                                                                        *)
(*   -[Core.t]: Runtime states corresponding to dynamic invocations of    *)
(*   [Static.t]s, initialized from a [Static] module to handle a          *)
(*   particular external function call made by another [Core]             *)
(*                                                                        *)
(*   -[CallStack.t]: just lists of [Core.t]s satisfying a few             *)
(*   well-formedness properties                                           *)
(*                                                                        *)
(*   -[Linker.t]: The type of linker corestates.  Linker states contain:  *)
(*                                                                        *)
(*      =[cores], a function from module id's ('I_N, or integers in the   *)
(*       range [0..N-1]) to genvs and core semantics                      *)
(*                                                                        *)
(*      =[fn_tbl], a table mapping external function id's to module id's, *)
(*      and                                                               *)
(*                                                                        *)
(*      =[stack], a callstack used to maintain a stack of cores at        *)
(*     runtime.  Above, parameter [N] is the number of static modules in  *)
(*     the program.                                                       *)
(*                                                                        *)
(*   -[LinkerSem]: defines the actual linking semantics. In later parts   *)
(*   of the file, the [LinkerSem] semantics is shown to be both a         *)
(*   [CoopCoreSem] and an [EffectSem] (cf. core_semantics.v,              *)
(*   effect_semantics.v).                                                 *)

(* Static semantics of translation units *)

Module Static. 

Record t := mk
  { F   : Type
  ; V   : Type
  ; ge  : Genv.t F V
  ; C   : Type
  ; coreSem : @EffectSem (Genv.t F V) C
  ; init : C }.

End Static.

(* [Cores] are runtime execution units. *)

Module Core. Section core.

Variable N : pos.
Variable cores : 'I_N -> Static.t.

Import Static.

(* The type [t] gives runtime states of dynamic module invocations.       *)
(*   i : 'I_N                                                             *)
(*                                                                        *)
(*       A natural between [0..n-1] that maps this core back to the       *)
(*       translation unit numbered [i] from which it was invoked.         *)
(*                                                                        *)
(*   c : RC.state (cores i).(C)                                           *)
(*                                                                        *)
(*      Runtime states. These comprise:                                   *)
(*                                                                        *)
(*        { core : (cores i).(C) -- Corestates of the type associated     *)
(*                                  w/ module (cores i).                  *)
(*        ; args : seq val                                                *)
(*        ; rets : seq val                                                *)
(*        ; locs : block -> bool }                                        *)
(*                                                                        *)
(*      Cf. rc_semantics.v for more details.                              *)

Record t := mk
  { i  : 'I_N
  ; c  :> RC.state (cores i).(C) }.

Definition updC (core : t) (newC : (cores core.(i)).(C)) :=
  {| i := core.(i)
   ; c := RC.updC newC (core).(c) |}.

Definition upd (core : t) (new : RC.state (cores core.(i)).(C)) :=
  {| i := core.(i)
   ; c := new |}.

End core. End Core.

Arguments Core.t {N} cores.

Arguments Core.i {N cores} !t /.

Arguments Core.c {N cores} !t /.

Arguments Core.updC {N cores} !core _ /.

Arguments Core.upd {N cores} !core _ /.

(* Linking semantics invariants:                                          *)
(*  -All cores except the topmost one are at_external.                    *)
(*  -The call stack always contains at least one core.                    *)

Section coreDefs.

Import Static.
Import RC.

Variable N : pos.
Variable cores : 'I_N -> Static.t.

Definition atExternal (c: Core.t cores) :=
  let: (Core.mk i c) := c in
  let: F := (cores i).(F) in
  let: V := (cores i).(V) in
  let: C := (cores i).(C) in
  let: effSem := (cores i).(coreSem) in
  if at_external effSem c is Some (ef, dep_sig, args) then true
  else false.

Definition wf_callStack (stk : Stack.t (Core.t cores)) := 
  [&& all atExternal (STACK.pop stk) & size stk > 0].

End coreDefs.

Arguments atExternal {N} cores c.

(** Call stacks are [stack]s satisfying the [wf_callStack] invariant. *)

Module CallStack. Section callStack.

Context {N : pos} (cores : 'I_N -> Static.t).

Record t : Type := mk
  { callStack :> Stack.t (Core.t cores)
  ; _         :  wf_callStack callStack }.

Program Definition singl (core: Core.t cores) := mk [:: core] _.

Section callStackDefs.

Context (stack : t).

Definition callStackSize := size stack.(callStack).

Lemma callStack_wf : wf_callStack stack.
Proof. by case: stack. Qed.

Lemma callStack_ext : all (atExternal cores) (STACK.pop stack).
Proof. by move: callStack_wf; move/andP=> [H1 H2]. Qed.

Lemma callStack_size : callStackSize > 0.
Proof. by move: callStack_wf; move/andP=> [H1 H2]. Qed.

Lemma callStack_nonempty : STACK.nonempty stack.
Proof. by case: stack=> //; case. Qed.

End callStackDefs. 

End callStack. End CallStack.

(* [Linker.t]                                                             *)
(*                                                                        *)
(*  The first two fields of this record are static configuration data:    *)
(*                                                                        *)
(*    -[cores] is a function from module id's ('I_n, or integers in the   *)
(*     range [0..n-1]) to genvs and core semantics, with existentially    *)
(*     quantified core type [C].                                          *)
(*                                                                        *)
(*    -[fn_tbl] maps external function id's to module id's                *)
(*                                                                        *)
(*  [stack] is used to maintain a stack of cores, at runtime.             *)
(*  Parameter [N] is the number of static modules in the program.         *)

Module Linker. Section linker.

Variable N : pos.
Variable cores : 'I_N  -> Static.t.

Record t := mkLinker 
  { fn_tbl : ident -> option 'I_N
  ; stack  :> CallStack.t cores }.

End linker. End Linker.

Import Linker.

Notation linker := Linker.t.

Section linkerDefs.

Context {N : pos} (my_cores : 'I_N -> Static.t) (l : linker N my_cores).

Import CallStack. (*for coercion [callStack]*)

Definition updStack (newStack : CallStack.t my_cores) :=
  {| fn_tbl := l.(fn_tbl)
   ; stack  := newStack |}.

(* [inContext]: The top core on the call stack has a return context  *)     

Definition inContext (l0 : linker N my_cores) := callStackSize l0.(stack) > 1.

(* [updCore]: Replace the top core on the call stack with [newCore]  *)     

Program Definition updCore (newCore: Core.t my_cores) := 
  updStack (CallStack.mk (STACK.push (STACK.pop l.(stack)) newCore) _).  
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

Lemma updCore_inj_updC c c1 c2 : 
  updCore (Core.updC c c1) = updCore (Core.updC c c2) -> c1=c2.
Proof. 
case=> H1; move: (EqdepFacts.eq_sigT_snd H1). 
by rewrite -Eqdep.Eq_rect_eq.eq_rect_eq; case: (Core.c c)=> ? ? ? ?; case.
Qed.

(* [pushCore]: Push a new core onto the call stack.                       *)
(* Succeeds only if all cores are currently at_external.                  *)

Lemma stack_push_wf newCore :
  all (atExternal my_cores) l.(stack).(callStack) -> 
  wf_callStack (SeqStack.updStack (newCore :: l.(stack).(callStack))).
Proof.
by rewrite/wf_callStack=> H; apply/andP; split.
Qed.

Definition pushCore 
  (newCore: Core.t my_cores) 
  (pf : all (atExternal my_cores) l.(stack).(callStack)) := 
  updStack (CallStack.mk (STACK.push l.(stack) newCore) (stack_push_wf _ pf)).

(* [popCore]: Pop the top core on the call stack.                         *)
(* Succeeds only if the top core is running in a return context.          *)

Lemma inContext_wf (stk : Stack.t (Core.t my_cores)) : 
  size stk > 1 -> wf_callStack stk -> wf_callStack (STACK.pop stk).
Proof.
rewrite/wf_callStack=> H1; move/andP=> [H2 H3]; apply/andP; split.
- by apply: STACK.all_pop.
- by move: H1 H2 H3; case: stk.
Qed.

Program Definition popCore : option (linker N my_cores) := 
  (match inContext l as pf 
         return (pf = inContext l -> option (linker N my_cores)) with
    | true => fun pf => 
        Some (updStack (CallStack.mk (STACK.pop l.(stack)) 
                                     (inContext_wf _ _ _)))
    | false => fun pf => None
  end) Logic.eq_refl.
Next Obligation. by apply: callStack_wf. Qed.

Definition peekCore := STACK.head l.(stack) (callStack_nonempty l.(stack)).

Definition emptyStack := if l.(stack).(callStack) is [::] then true else false.

Import Static.

(* We take the RC initial core here because we want to make sure the args *)
(* are properly stashed in the [c] tuple.                                 *)

Definition initCore (ix: 'I_N) (v: val) (args: list val) 
  : option (Core.t my_cores):=
  if @RC.initial_core _ _ _ 
       (my_cores ix).(coreSem)
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

(* [handle id l args] looks up function id [id] in function table         *)
(* [l.fn_tbl], producing an optional module index [ix : 'I_N].  The index *)
(* is used to construct a new core to handle the call to function         *)
(* [id]. The new core is pushed onto the call stack.                      *)

Section handle.

Variables (id: ident) (l: linker N my_cores) (args: list val).

Import CallStack.

Definition handle :=
  (match all (atExternal my_cores) l.(stack).(callStack) as pf 
        return (all (atExternal my_cores) l.(stack).(callStack) = pf
               -> option (linker N my_cores)) with
    | true => fun pf => 
        if l.(fn_tbl) id is Some ix then
        if initCore my_cores ix (Vptr id Int.zero) args is Some c 
          then Some (pushCore l c pf)
        else None else None
    | false => fun _ => None
  end) erefl.

End handle.

Section handle_lems.

Import CallStack.

Lemma handleP id l args l' :
  handle id l args = Some l' <-> 
  (exists (pf : all (atExternal my_cores) l.(stack).(callStack)) ix c,
     [/\ l.(fn_tbl) id = Some ix 
       , initCore my_cores ix (Vptr id Int.zero) args = Some c
       & l' = pushCore l c pf]).
Proof.
rewrite/handle.
set (x := all (atExternal my_cores) (callStack (stack l))).
move: (erefl x).
(*pattern x at 3 4 5 6.
case pf: (all (atExternal my_cores) (callStack (stack l))).*)
Admitted. (*dependent pattern matching idiocy*)

End handle_lems.

Definition initial_core (tt: ge_ty) (v: val) (args: list val)
  : option (linker N my_cores) :=
  if v is Vptr id ofs then 
  if my_fn_tbl id is Some ix then
  if initCore my_cores ix (Vptr id Int.zero) args is Some c 
  then Some (mkLinker my_fn_tbl (CallStack.singl c))
  else None else None else None.

(* Functions suffixed w/ 0 always operate on the running core on the (top *)
(* of the) call stack.                                                    *)

Definition at_external0 (l: linker N my_cores) :=
  let: c   := peekCore l in
  let: ix  := c.(Core.i) in                                            
  let: sem := (my_cores ix).(Static.coreSem) in                        
  let: F   := (my_cores ix).(Static.F) in                              
  let: V   := (my_cores ix).(Static.V) in                              
    @at_external (Genv.t F V) _ _ sem (RC.core (Core.c c)).

Arguments at_external0 !l.

Definition halted0 (l: linker N my_cores) :=
  let: c   := peekCore l in
  let: ix  := c.(Core.i) in
  let: sem := (my_cores ix).(Static.coreSem) in
  let: F   := (my_cores ix).(Static.F) in
  let: V   := (my_cores ix).(Static.V) in
    @halted (Genv.t F V) _ _ sem (RC.core (Core.c c)).

Arguments halted0 !l.

(* [corestep0] lifts a corestep of the runing core to a corestep of the   *)
(* whole program semantics.                                               *)
(* Note: we call the RC version of corestep here.                         *)                        

Definition corestep0 
  (l: linker N my_cores) (m: Mem.mem) (l': linker N my_cores) (m': Mem.mem) := 
  let: c   := peekCore l in
  let: ix  := c.(Core.i) in
  let: sem := (my_cores ix).(Static.coreSem) in
  let: F   := (my_cores ix).(Static.F) in
  let: V   := (my_cores ix).(Static.V) in
  let: ge  := (my_cores ix).(Static.ge) in
    exists c', 
      @corestep (Genv.t F V) _ _ (RC.effsem sem) ge (Core.c c) m c' m'
   /\ l' = updCore l (Core.upd c c').

Arguments corestep0 !l m l' m'.

Definition fun_id (ef: external_function) : option ident :=
  if ef is (EF_external id sig) then Some id else None.

(* The linker is [at_external] whenever the top core is [at_external] and *)
(* the [id] of the called external function isn't handleable by any       *)
(* compilation unit.                                                      *)

Definition at_external (l: linker N my_cores) :=
  if at_external0 l is Some (ef, dep_sig, args) 
    then if fun_id ef is Some id then
         if handle id l args is None then Some (ef, dep_sig, args) else None
         else None
  else at_external0 l.

(* We call the RC version of after_external here to ensure that the       *)
(* return value [mv] of the external call is properly stashed in the      *)
(* state tuple [c].                                                       *)

Definition after_external (mv: option val) (l: linker N my_cores) :=
  let: c   := peekCore l in
  let: ix  := c.(Core.i) in
  let: sem := (my_cores ix).(Static.coreSem) in
  let: F   := (my_cores ix).(Static.F) in
  let: V   := (my_cores ix).(Static.V) in
  let: ge  := (my_cores ix).(Static.ge) in
    if @after_external (Genv.t F V) _ _ (RC.effsem sem) mv (Core.c c) 
      is Some c' then Some (updCore l (Core.upd c c'))
    else None.

(* The linker is [halted] when the last core on the call stack is halted. *)

Definition halted (l: linker N my_cores) := 
  if ~~inContext l then 
  if halted0 l is Some rv then Some rv
  else None else None.

(* Corestep relation of linking semantics *)

Definition corestep 
  (ge: ge_ty) 
  (l: linker N my_cores) (m: Mem.mem)
  (l': linker N my_cores) (m': Mem.mem) := 

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
move: Hht; rewrite/halted0; apply corestep_not_halted in H1. 
by move: H1=> /=; rewrite/RC.halted=> ->.
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
case Heq: (core_semantics.after_external _ _)=> //.
inversion 1; subst.
case Hat: (at_external0 _)=>//[[[ef sig] args]].
move: Hat; rewrite/at_external0=>/= H2.
apply after_at_external_excl in Heq.
by move: Heq H2; rewrite/=/RC.at_external=> ->.
Qed.

Definition coresem : CoreSemantics ge_ty (linker N my_cores) Mem.mem :=
  Build_CoreSemantics ge_ty (linker N my_cores) Mem.mem 
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

(* Specialize to effect semantics *)

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
      @effstep (Genv.t F V) _ (RC.effsem sem) ge U (Core.c c) m c' m'
   /\ l' = updCore l (Core.upd c c').

Lemma effstep0_unchanged U l m l' m' : 
  effstep0 U l m l' m' ->
  Mem.unchanged_on (fun b ofs => U b ofs = false) m m'.
Proof. 
rewrite/effstep0; case=> ? [STEP].
by move: {STEP}(effax1 STEP)=> [STEP]UNCH H2.
Qed.

Lemma effstep0_corestep0 U l m l' m' : 
  effstep0 U l m l' m' -> LinkerSem.corestep0 l m l' m'.
Proof. 
rewrite/effstep0/LinkerSem.corestep0; case=> c' [STEP].
move: {STEP}(effax1 STEP)=> [STEP]UNCH H2.
by exists c'; split.
Qed.

Lemma effstep0_forward U l m l' m' : 
  effstep0 U l m l' m' -> mem_forward m m'.
Proof. 
move/effstep0_corestep0; rewrite/LinkerSem.corestep0. 
by move=> []c' []STEP H1; apply: {STEP}(corestep_fwd STEP). 
Qed.

Definition inner_effstep (ge: ge_ty)
  (l: linker N my_cores) m (l': linker N my_cores) m' := 
  [/\ LinkerSem.corestep ge l m l' m' 
    & LinkerSem.corestep0 l m l' m' -> exists U, effstep0 U l m l' m'].

Definition effstep (ge: ge_ty) V
  (l: linker N my_cores) m (l': linker N my_cores) m' := 
  [/\ LinkerSem.corestep ge l m l' m' 
    , LinkerSem.corestep0 l m l' m' -> effstep0 V l m l' m'
    & ~LinkerSem.corestep0 l m l' m' -> forall b ofs, ~~ V b ofs].

Section csem.

Notation mycsem := (LinkerSem.coresem N my_cores my_fun_tbl).

Program Definition csem 
  : CoreSemantics ge_ty (linker N my_cores) Mem.mem := 
  Build_CoreSemantics _ _ _
    (initial_core mycsem)
    (at_external mycsem)
    (after_external mycsem)
    (halted mycsem) 
    inner_effstep _ _ _ _.

Next Obligation. 
move: H; rewrite/inner_effstep=> [[H1] H2]. 
by apply: (LinkerSem.corestep_not_at_external H1).
Qed.

Next Obligation.
move: H; rewrite/inner_effstep=> [[H1] H2]. 
by apply: (LinkerSem.corestep_not_halted H1).
Qed.

Next Obligation. by apply: (LinkerSem.at_external_halted_excl). Qed.
Next Obligation. by apply (LinkerSem.after_at_external_excl _ _ H). Qed.

End csem.

Program Definition coopsem := Build_CoopCoreSem _ _ csem _.

Next Obligation. 
move: CS; case; move=>[H1|[<- [H0 H1]]]. 
by move/(_ H1)=>{H1} [U EFF]; apply (effstep0_forward EFF).
by move=> ?; apply mem_forward_refl.
Qed.

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
move: H; rewrite/effstep=> [][]; case.
move=> H; move/(_ H); rewrite/effstep0. 
by move=> []? []H2 _ _; apply: (effstep_valid _ _ _ _ _ _ _ H2 _ _ H0).
by move=> []_ []nstep _ _; move/(_ nstep b z); rewrite H0.
Qed.

End effingLinker.
