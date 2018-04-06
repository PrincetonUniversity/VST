Require Import Axioms.

Require Import VST.sepcomp. Import SepComp.

Require Import VST.concurrency.pos.
Require Import VST.concurrency.stack.

Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.

(*NOTE: because of redefinition of [val], these imports must appear
  after Ssreflect eqtype.*)
Require Import AST.    (*for typ*)
Require Import Values. (*for val*)
Require Import Globalenvs.
Require Import Integers.

Require Import ZArith.

(* This file is a parametric version of [compcert_linking.v].  See that   *)
(* file for more information.                                             *)

(* The [CoreLinker] module gives the operational semantics of linking.    *)
(* It is parameterized by the type of core semantics [Csem] (e.g., effect *)
(* semantics, coop semantics, vanilla core semantics) used to the dynamic *)
(* semantics of each translation unit.  Note that each module may still   *)
(* have its own core type C, function definition type F, etc.             *)

(* Semantics of translation units *)

Module Modsem.

Record t (M : Type) := mk
  { F   : Type
  ; V   : Type
  ; ge  : Genv.t F V
  ; C   : Type
  ; sem : @CoreSemantics (Genv.t F V) C M }.

End Modsem.

(* [Cores] are runtime execution units. *)

Module Core. Section core.

Variable M : Type.
Variable N : pos.
Variable cores : 'I_N -> Modsem.t M.

Import Modsem.

Record t := mk
  { i  : 'I_N
  ; c  :> (cores i).(C)
  ; sg : signature }.

Definition upd (core : t) (newC : (cores core.(i)).(C)) :=
  {| i := core.(i)
   ; c := newC
   ; sg := core.(sg) |}.

End core. End Core.

Arguments Core.t {M N} cores.

Arguments Core.i {M N cores} !t /.

Arguments Core.c {M N cores} !t /.

Arguments Core.sg {M N cores} !t /.

Arguments Core.upd {M N cores} !core _ /.

(* Linking semantics invariants:                                          *)
(*  -All cores except the topmost one are at_external.                    *)
(*  -The call stack always contains at least one core.                    *)

Section coreDefs.

Import Modsem.

Variable M : Type.
Variable N : pos.
Variable cores : 'I_N -> Modsem.t M.

Definition atExternal (c: Core.t cores) :=
  let: (Core.mk i c sg) := c in
  let: F := (cores i).(F) in
  let: V := (cores i).(V) in
  let: C := (cores i).(C) in
  let: sem := (cores i).(sem) in
  if @at_external (Genv.t F V) C M sem c is
    Some (ef, dep_sig, args) then true
  else false.

Definition wf_callStack (stk : Stack.t (Core.t cores)) :=
  [&& all atExternal (STACK.pop stk) & size stk > 0].

End coreDefs.

Arguments atExternal {M N} cores c.

(** Call stacks are [stack]s satisfying the [wf_callStack] invariant. *)

Module CallStack. Section callStack.

Context {M : Type} {N : pos} (cores : 'I_N -> Modsem.t M).

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

Variable M : Type.
Variable N : pos.
Variable cores : 'I_N  -> Modsem.t M.

Record t := mkLinker
  { fn_tbl : ident -> option 'I_N
  ; stack  :> CallStack.t cores }.

End linker. End Linker.

Import Linker.

Notation linker := Linker.t.

Section linkerDefs.

Context {M : Type} {N : pos} (my_cores : 'I_N -> Modsem.t M) (l : linker N my_cores).

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

Import Modsem.

Definition initCore (sg: signature) (ix: 'I_N) (v: val) (args: list val)
  : option (Core.t my_cores):=
  if @initial_core _ _ _
       (my_cores ix).(sem)
       (my_cores ix).(Modsem.ge)
       v args
  is Some c then Some (Core.mk _ my_cores ix c sg)
  else None.

End linkerDefs.

Notation ge_ty := (Genv.t unit unit).

Arguments updStack {M N} {my_cores} !_ _ /.

Arguments updCore {M N} {my_cores} !_ _ /.

Arguments pushCore {M N} {my_cores} !l _ _ /.

Arguments peekCore {M N} {my_cores} !l /.

Arguments emptyStack {M N} {my_cores} !l /.

Lemma popCoreI M N my_cores l l' pf :
  inContext l ->
  l' = updStack l (CallStack.mk (STACK.pop (CallStack.callStack l)) pf) ->
  @popCore M N my_cores l = Some l'.
Proof.
rewrite /popCore.
move: (popCore_obligation_1 l); move: (popCore_obligation_2 l).
case: (inContext l)=> pf1 pf2 // _ ->.
f_equal=> //.
f_equal=> //.
f_equal=> //.
by apply: proof_irr.
Qed.

Lemma popCoreE M N my_cores l l' :
  @popCore M N my_cores l = Some l' ->
  exists pf,
  [/\ inContext l
    & l' = updStack l (CallStack.mk (STACK.pop (CallStack.callStack l)) pf)].
Proof.
rewrite /popCore.
move: (popCore_obligation_1 l); move: (popCore_obligation_2 l).
case: (inContext l)=> pf1 pf2 //; case=> <-.
have pf: wf_callStack (STACK.pop (CallStack.callStack l)).
{ case: (andP (pf1 erefl))=> A B; apply/andP; split=> //.
  by apply: SeqStack.all_pop.
  by move: (pf2 erefl); clear pf1 pf2 A B; case: l=> /= ?; case; elim. }
exists pf; split=> //.
by f_equal; f_equal; apply: proof_irr.
Qed.

(** The linking semantics *)

Module LinkerSem. Section linkerSem.

Variable M : Type.
Variable N : pos.  (* Number of (compile-time) modules *)
Variable my_cores : 'I_N  -> Modsem.t M.
Variable my_fn_tbl: ident -> option 'I_N.

(* [handle id l args] looks up function id [id] in function table         *)
(* [l.fn_tbl], producing an optional module index [ix : 'I_N].  The index *)
(* is used to construct a new core to handle the call to function         *)
(* [id]. The new core is pushed onto the call stack.                      *)

Section handle.

Variables (sg: signature) (id: ident) (l: linker N my_cores) (args: list val).

Import CallStack.

Definition handle :=
  (match all (atExternal my_cores) l.(stack).(callStack) as pf
        return (pf = all (atExternal my_cores) l.(stack).(callStack)
               -> option (linker N my_cores)) with
    | true => fun pf =>
        if l.(fn_tbl) id is Some ix then
        if Genv.find_symbol (my_cores ix).(Modsem.ge) id is Some bf then
        if initCore my_cores sg ix (Vptr bf Int.zero) args is Some c
          then Some (pushCore l c (Logic.eq_sym pf))
        else None else None else None
    | false => fun _ => None
  end) erefl.

End handle.

Section handle_lems.

Import CallStack.

Lemma handleP sg id l args l' :
  handle sg id l args = Some l' <->
  (exists (pf : all (atExternal my_cores) l.(stack).(callStack)) ix bf c,
     [/\ l.(fn_tbl) id = Some ix
       , Genv.find_symbol (my_cores ix).(Modsem.ge) id = Some bf
       , initCore my_cores sg ix (Vptr bf Int.zero) args = Some c
       & l' = pushCore l c pf]).
Proof.
rewrite/handle.
rewrite /pushCore.
generalize (stack_push_wf l).
pattern (all (atExternal my_cores) (CallStack.callStack (stack l)))
 at 1 2 3 4 5 6 7 8 9.
case f: (all _ _); move=> pf.
case g: (fn_tbl l id)=> [ix|].
case fnd: (Genv.find_symbol _ _)=> [bf|].
case h: (initCore _ _ _)=> [c|].
split=> H.
exists (erefl true),ix,bf,c; split=> //; first by case: H=> <-.
case: H=> pf0 []ix0 []bf0 []c0 []; case=> <-.
rewrite fnd; case=> <-; rewrite h; case=> <- ->.
by repeat f_equal; apply: proof_irr.
split=> //; case=> pf0 []ix0 []bf0 []c0 [].
by case=> <-; rewrite fnd; case=> <-; rewrite h.
split=> //; case=> pf0 []ix0 []bf0 []c0 [].
by case=> <-; rewrite fnd; discriminate.
split=> //.
by case=> pf0 []ix0 []bf0 []c0 []; discriminate.
split=> //.
by case=> pf0 []ix0 []bf0 []c0 []; discriminate.
Qed.

End handle_lems.

Definition main_sig := mksignature nil (Some Tint) cc_default.

Definition initial_core (ge: ge_ty) (v: val) (args: list val)
  : option (linker N my_cores) :=
  if v is Vptr bf ofs then
  if Int.eq ofs Int.zero then
  if Genv.invert_symbol ge bf is Some id then
  if my_fn_tbl id is Some ix then
  if initCore my_cores main_sig ix (Vptr bf Int.zero) args is Some c
  then Some (mkLinker my_fn_tbl (CallStack.singl c))
  else None else None else None else None else None.

(* Functions suffixed w/ 0 always operate on the running core on the (top *)
(* of the) call stack.                                                    *)

Definition at_external0 (l: linker N my_cores) :=
  let: c   := peekCore l in
  let: ix  := c.(Core.i) in
  let: sem := (my_cores ix).(Modsem.sem) in
  let: F   := (my_cores ix).(Modsem.F) in
  let: V   := (my_cores ix).(Modsem.V) in
    @at_external (Genv.t F V) _ _ sem (Core.c c).

Arguments at_external0 !l.

Require Import VST.concurrency.val_casted. (*for val_has_type_func*)

Definition halted0 (l: linker N my_cores) :=
  let: c   := peekCore l in
  let: ix  := c.(Core.i) in
  let: sg  := c.(Core.sg) in
  let: sem := (my_cores ix).(Modsem.sem) in
  let: F   := (my_cores ix).(Modsem.F) in
  let: V   := (my_cores ix).(Modsem.V) in
    if @halted (Genv.t F V) _ _ sem (Core.c c) is Some v then
      if val_casted.val_has_type_func v (proj_sig_res sg) then Some v
      else None
    else None.

Arguments halted0 !l.

(* [corestep0] lifts a corestep of the runing core to a corestep of the   *)
(* whole program semantics.                                               *)

Definition corestep0
  (l: linker N my_cores) (m: M) (l': linker N my_cores) (m': M) :=
  let: c   := peekCore l in
  let: ix  := c.(Core.i) in
  let: sem := (my_cores ix).(Modsem.sem) in
  let: F   := (my_cores ix).(Modsem.F) in
  let: V   := (my_cores ix).(Modsem.V) in
  let: ge  := (my_cores ix).(Modsem.ge) in
    exists c',
      @corestep (Genv.t F V) _ _ sem ge (Core.c c) m c' m'
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
         if fn_tbl l id is None then Some (ef, dep_sig, args) else None
         else Some (ef, dep_sig, args)
  else at_external0 l.

Definition after_external (mv: option val) (l: linker N my_cores) :=
  let: c   := peekCore l in
  let: ix  := c.(Core.i) in
  let: sem := (my_cores ix).(Modsem.sem) in
  let: F   := (my_cores ix).(Modsem.F) in
  let: V   := (my_cores ix).(Modsem.V) in
  let: ge  := (my_cores ix).(Modsem.ge) in
    if @after_external (Genv.t F V) _ _ sem mv (Core.c c)
      is Some c' then Some (updCore l (Core.upd c c'))
    else None.

(* The linker is [halted] when the last core on the call stack is halted. *)

Definition halted (l: linker N my_cores) :=
  if ~~inContext l then
  if halted0 l is Some rv then Some rv
  else None else None.

(* Corestep relation of linking semantics *)

Definition corestep
  (l: linker N my_cores) (m: M)
  (l': linker N my_cores) (m': M) :=

  (** 1- The running core takes a step, or *)
  corestep0 l m l' m' \/

  (** 2- We're in a function call context. In this case, the running core is either *)
  (m=m'
   /\ ~corestep0 l m l' m'
   /\
      (** 3- at_external, in which case we push a core onto the stack to handle
         the external function call (or this is not possible because no module
         handles the external function id, in which case the entire linker is
         at_external) *)

      if at_external0 l is Some (ef, dep_sig, args) then
      if fun_id ef is Some id then
      if handle (ef_sig ef) id l args is Some l'' then l'=l'' else False else False
      else

      (** 4- or halted, in which case we pop the halted core from the call stack
         and inject its return value into the caller's corestate. *)

      if inContext l then
      if halted0 l is Some rv then
      if popCore l is Some l0 then
      if after_external (Some rv) l0 is Some l'' then l'=l''
      else False else False else False

     else False).

Inductive Corestep : linker N my_cores -> M
                  -> linker N my_cores -> M -> Prop :=
| Corestep_step :
  forall l m c' m',
  let: c     := peekCore l in
  let: c_ix  := Core.i c in
  let: c_ge  := Modsem.ge (my_cores c_ix) in
  let: c_sem := Modsem.sem (my_cores c_ix) in
    semantics.corestep c_sem c_ge (Core.c c) m c' m' ->
    Corestep l m (updCore l (Core.upd (peekCore l) c')) m'

| Corestep_call :
  forall (l : linker N my_cores) m ef dep_sig args id bf d_ix d
         (pf : all (atExternal my_cores) (CallStack.callStack l)),

  let: c := peekCore l in
  let: c_ix  := Core.i c in
  let: c_ge  := Modsem.ge (my_cores c_ix) in
  let: c_sem := Modsem.sem (my_cores c_ix) in

  semantics.at_external c_sem (Core.c c) = Some (ef,dep_sig,args) ->
  fun_id ef = Some id ->
  fn_tbl l id = Some d_ix ->
  Genv.find_symbol (my_cores d_ix).(Modsem.ge) id = Some bf ->

  let: d_ge  := Modsem.ge (my_cores d_ix) in
  let: d_sem := Modsem.sem (my_cores d_ix) in

  semantics.initial_core d_sem d_ge (Vptr bf Int.zero) args = Some d ->
  Corestep l m (pushCore l (Core.mk _ _ _ d (ef_sig ef)) pf) m

| Corestep_return :
  forall (l : linker N my_cores) l'' m rv d',

  1 < CallStack.callStackSize (stack l) ->

  let: c  := peekCore l in
  let: c_ix  := Core.i c in
  let: c_sg  := Core.sg c in
  let: c_ge  := Modsem.ge (my_cores c_ix) in
  let: c_sem := Modsem.sem (my_cores c_ix) in

  popCore l = Some l'' ->

  let: d  := peekCore l'' in
  let: d_ix  := Core.i d in
  let: d_ge  := Modsem.ge (my_cores d_ix) in
  let: d_sem := Modsem.sem (my_cores d_ix) in

  semantics.halted c_sem (Core.c c) = Some rv ->
  val_has_type_func rv (proj_sig_res c_sg)=true ->
  semantics.after_external d_sem (Some rv) (Core.c d) = Some d' ->
  Corestep l m (updCore l'' (Core.upd d d')) m.

Lemma CorestepE l m l' m' :
  Corestep l m l' m' ->
  corestep l m l' m'.
Proof.
inversion 1; subst; rename H0 into A; rename H into B.
by left; exists c'; split.
right; split=> //.
split=> //.
rewrite /corestep0=> [][]c' []step.
by rewrite /= (corestep_not_at_external _ _ _ _ _ _ step) in A.
rewrite /= in A.
rewrite /inContext /at_external0 A H1.
case e: (handle _ _ _)=> //[l'|].
move: e; case/handleP=> pf' []ix' []bf' []c []C G D ->.
move: D; rewrite /initCore.
rewrite H2 in C; case: C=> eq; subst ix'.
rewrite G in H3; case: H3=> ->.
by rewrite /= in H4; rewrite H4; case=> <-; f_equal; apply: proof_irr.
move: e; rewrite/handle /pushCore.
generalize (stack_push_wf l).
pattern (all (atExternal my_cores) (CallStack.callStack (stack l)))
 at 1 2 3 4 5 6 7.
case f: (all _ _)=> pf'.
rewrite /= in H4; rewrite H2 H3 /initCore H4; discriminate.
by rewrite pf in f.
right; split=> //.
split=> //.
rewrite /corestep0=> [][]c' []step.
by rewrite /= (corestep_not_halted _ _ _ _ _ _ step) in H2.
have at_ext:
  semantics.at_external
    (Modsem.sem (my_cores (Core.i (peekCore l))))
    (Core.c (peekCore l)) = None.
{ case: (@at_external_halted_excl _ _ _
         (Modsem.sem (my_cores (Core.i (peekCore l))))
         (Core.c (peekCore l)))=> //.
  by rewrite /= in H2; rewrite H2. }
rewrite /= in at_ext; rewrite /inContext A /at_external0 H1 at_ext.
by rewrite /= in H2 H4; rewrite /halted0 H2 /after_external H3 H4.
Qed.

Lemma CorestepI l m l' m' :
  corestep l m l' m' ->
  Corestep l m l' m'.
Proof.
case.
case=> c []step ->.
by apply: Corestep_step.
case=> <-.
case=> nstep.
case atext: (at_external0 _)=> [[[ef dep_sig] args]|//].
case funid: (fun_id ef)=> [id|//].
case hdl:   (handle (ef_sig ef) id l args)=> [l''|//] ->.
move: hdl; case/handleP=> pf []ix []bf []c []fntbl genv init ->.
move: init; rewrite /initCore.
case init: (semantics.initial_core _ _ _)=> [c'|//]; case=> <-.
by apply: (@Corestep_call _ _ ef dep_sig args id bf).
case inCtx: (inContext _)=> //.
case hlt: (halted0 _)=> [rv|//].
case pop: (popCore _)=> [c|//].
case aft: (after_external _ _)=> [l''|//] ->.
move: aft; rewrite /after_external.
case aft: (semantics.after_external _ _)=> [c''|//].
rewrite /halted0 in hlt; move: hlt.
case hlt: (semantics.halted _)=> //.
case oval: (val_has_type_func _ _)=> //; case=> Heq. subst. case=> <-.
by apply: (@Corestep_return _ _ _ rv c'').
Qed.

Lemma CorestepP l m l' m' :
  corestep l m l' m' <-> Corestep l m l' m'.
Proof. by split; [apply: CorestepI | apply: CorestepE]. Qed.

Lemma corestep_not_at_external0 m c m' c' :
  corestep0 c m c' m' -> at_external0 c = None.
Proof. by move=>[]newCore []H1 H2; apply corestep_not_at_external in H1. Qed.

Lemma at_external_halted_excl0 c : at_external0 c = None \/ halted0 c = None.
Proof.
case: (@at_external_halted_excl _ _ _
        (Modsem.sem (my_cores (Core.i (peekCore c))))
        (Core.c (peekCore c))).
by rewrite /at_external0=> ->; left.
by rewrite /halted0=> ->; right.
Qed.

Lemma corestep_not_halted0 m c m' c' : corestep0 c m c' m' -> halted c = None.
Proof.
move=> []newCore []H1 H2; rewrite/halted.
case Hcx: (~~ inContext _)=>//; case Hht: (halted0 _)=>//.
by move: Hht; rewrite/halted0; apply corestep_not_halted in H1; rewrite /= H1.
Qed.

Lemma corestep_not_halted0' m c m' c' : corestep0 c m c' m' -> halted0 c = None.
Proof.
move=> []newCore []H1 H2; rewrite/halted.
case Hht: (halted0 _)=>//.
by move: Hht; rewrite/halted0; apply corestep_not_halted in H1; rewrite /= H1.
Qed.

Lemma corestep_not_at_external (ge : ge_ty) m c m' c' :
  corestep c m c' m' -> at_external c = None.
Proof.
rewrite/corestep/at_external.
move=> [H|[_ [_ H]]]; first by move: H; move/corestep_not_at_external0=> /= ->.
move: H; case Heq: (at_external0 c)=>[[[ef sig] args]|//].
move: Heq; case: (at_external_halted_excl0 c)=> [H|H]; first by rewrite H.
move=> H2; case: (fun_id ef)=>// id; case hdl: (handle _ _ _)=> [a|].
by move: hdl; case/handleP=> ? []? []? []? []->.
by [].
Qed.

Lemma at_external0_not_halted c x :
  at_external0 c = Some x -> halted c = None.
Proof.
case: (at_external_halted_excl0 c); rewrite/at_external0/halted.
by case Heq: (peekCore c)=>//[a] ->.
move=> H; case Heq: (peekCore c)=>//[a].
by case Hcx: (~~ inContext _)=>//; rewrite H.
Qed.

Lemma corestep_not_halted (ge : ge_ty) m c m' c' :
  corestep c m c' m' -> halted c = None.
Proof.
rewrite/corestep.
move=> [H|[_ [_ H]]]; first by move: H; move/corestep_not_halted0.
move: H; case Hat: (at_external0 _)=> [x|//].
by rewrite (at_external0_not_halted _ Hat).
by rewrite /halted; case Hcx: (inContext _).
Qed.

Lemma at_external_halted_excl c :
  at_external c = None \/ halted c = None.
Proof.
rewrite/at_external/halted; case Hat: (at_external0 c)=>//;
first by right; apply: (at_external0_not_halted _ Hat).
by left.
Qed.

Definition coresem : CoreSemantics ge_ty (linker N my_cores) M :=
  Build_CoreSemantics ge_ty (linker N my_cores) M
    initial_core
    at_external
    after_external
    halted
    (fun _ : ge_ty => corestep)
    corestep_not_at_external
    corestep_not_halted
    at_external_halted_excl.

End linkerSem. End LinkerSem.
