Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*NOTE: because of redefinition of [val], these imports must appear 
  after Ssreflect eqtype.*)
Require Import compcert.common.AST.    (*for typ*)
Require Import compcert.common.Values. (*for val*)
Require Import compcert.common.Globalenvs. 
Require Import compcert.common.Memory.
Require Import compcert.lib.Integers.

Require Import sepcomp.core_semantics.
Require Import sepcomp.core_semantics_lemmas.

Require Import linking.compcert_linking.

Module Stacking_monoid.

Record t (F V C : Type) := mk
  { sem : @EffectSem (Genv.t F V) C
  ; op : C -> C -> C
  ; assoc : forall a b c, op a (op b c) = op (op a b) c }.

End Stacking_monoid.

Module Stacking_monoid_ok. Section Stacking_monoid_ok.

Variables F V C : Type.

Variable mon : Stacking_monoid.t F V C.

Variable ge : ge_ty.

Variable tge : Genv.t F V.

Parameter ge_tge_agree : genvs_domain_eq ge tge.

Parameter is_external : F -> bool.

Parameter tge_closed : 
  forall vf f,
  Genv.find_funct ge vf = Some f -> 
  exists tf, 
    [/\ Genv.find_funct tge vf = Some tf
      & ~~is_external tf].

Import Stacking_monoid.

Record t : Type := mk 
  { congr : forall d m d' m' c,
            corestep mon.(sem) tge d m d' m' -> 
            corestep_plus mon.(sem) tge (mon.(op) d c) m (mon.(op) d' c) m'

  ; call  : forall c ef dep_sig sig args d m id,
            at_external mon.(sem) c = Some (ef,dep_sig,args) ->
            ef = EF_external id sig -> 
            initial_core mon.(sem) tge (Vptr id Int.zero) args = Some d -> 
            corestep_plus mon.(sem) tge c m (mon.(op) d c) m 

  ; ret   : forall c d v c' m,
            halted mon.(sem) d = Some v -> 
            after_external mon.(sem) (Some v) c = Some c' -> 
            corestep_plus mon.(sem) tge (mon.(op) d c) m c' m }.

End Stacking_monoid_ok. End Stacking_monoid_ok.

Require Import linking.pos.

Section Stacking_simulation.

Variables F V C : Type.

Variable mon : Stacking_monoid.t F V C.

Variable ge : ge_ty.

Variable tge : Genv.t F V.

Parameter ge_tge_agree : genvs_domain_eq ge tge.

Parameter is_external : F -> bool.

Parameter tge_closed : 
  forall vf f,
  Genv.find_funct ge vf = Some f -> 
  exists tf, 
    [/\ Genv.find_funct tge vf = Some tf
      & ~~is_external tf].

Parameter mon_ok : Stacking_monoid_ok.t mon tge.

Lemma one_pos : (0 < 1)%coq_nat. 
Proof. by []. Qed.

Definition one : pos := mkPos one_pos.

Import Stacking_monoid.

Definition semantics := fun _ : 'I_one => Modsem.mk tge mon.(sem).

Lemma zero_lt : 0 < 1. 
Proof. by []. Qed.

Definition zero : 'I_one := Ordinal zero_lt.

Fixpoint fold_stack (s : seq (Core.t semantics)) : option (Modsem.C (semantics zero)) :=
  match s with
    | [::] => None
    | [:: c] => Some (c.(Core.c))
    | [:: c & s'] => 
        match fold_stack s' with
          | None => None
          | Some s'' => Some (mon.(op) c.(Core.c) s'')
        end
  end.

(* The following defn. is possible but hard to work with:
Program Fixpoint fold_stack (s : seq (Core.t semantics)) (pf : size s > 0) 
  {measure (size s)} := 
  (match s as x in seq _ return eq s x -> size x > 0 -> C with
    | [::] => fun eq lt => _
    | [:: c] => fun eq lt => c.(Core.c) 
    | [:: c & s'] => fun eq lt => mon.(op) c.(Core.c) (@fold_stack s' _ _)
   end) erefl pf. *)

Lemma fold_stack_nonempty s (pf : 0 < size s) :
  {c : Modsem.C (semantics zero) | fold_stack s = Some c}.
Proof.
elim: s pf=> // a s' IH _.
move: IH; case: s'; first by move=> _ /=; exists (Core.c a).
move=> b s'; case/(_ _)/Wrap=> // [][]c fld.
exists (op mon (Core.c a) c).
by move: fld; rewrite /fold_stack=> ->. 
Qed.

Lemma fold_stack_consE
  (a : Core.t semantics) (s : seq (Core.t semantics)) (pf : 0 < size s) : 
  fold_stack [:: a & s]
  = Some (op mon a.(Core.c) (projT1 (fold_stack_nonempty pf))).
Proof. 
rewrite /fold_stack -/fold_stack.
case: s pf=> // b s' pf.
move: (projT2 (fold_stack_nonempty pf)).
move: (@fold_stack_nonempty (b :: s')).
pattern pf at 0 1 2.
case: (fold_stack _)=> //.
by move=> c pf'; case=> <-.
Qed.

Definition match_states (l : linker one semantics) (c : C) :=
  let s := CallStack.callStack l.(Linker.stack) in
    fold_stack s = Some c.

Notation linker_sem := (LinkerSem.coresem one semantics (fun _ : ident => Some zero)).

Lemma stacking_step m l c l' m' : 
  match_states l c -> 
  corestep linker_sem ge l m l' m' -> 
  exists c', [/\ corestep_plus mon.(sem) tge c m c' m' & match_states l' c'].
Proof.
rewrite /match_states=> H; move/LinkerSem.CorestepP=> H2. 
move: {H2}(H2 ge) H; case; move {l m l' m'}.

{ move=> l m c' m' step fld.
move: c' step; case: l fld=> fntbl; case; case=> // a l pf fld /= c' step.
move: fld; case: l pf.
by move=> pf; case=> <-; exists c'; split=> //; exists O,c',m'; split.
move=> b l pf. 
have x: is_true (0 < size [:: b & l]) by [].
rewrite (@fold_stack_consE a (b :: l) x); case=> <-.
exists (op mon c' (projT1 (fold_stack_nonempty x))); split.
apply: Stacking_monoid_ok.congr=> //.
by apply: mon_ok.
move: (projT2 (fold_stack_nonempty x)).
move: (@fold_stack_nonempty (b :: l)).
pattern pf at 0.
by case: (fold_stack _)=> // d pf'; case=> <-. }

Admitted.

End Stacking_simulation.


