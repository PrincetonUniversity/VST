Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*NOTE: because of redefinition of [val], these imports must appear 
  after Ssreflect eqtype.*)
Require Import AST.    (*for typ*)
Require Import Values. (*for val*)
Require Import Globalenvs. 
Require Import Memory.
Require Import Integers.

Require Import core_semantics.
Require Import core_semantics_lemmas.
Require Import barebones_simulations.

Require Import compcert_linking.

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
  { step_congr : 
      forall d m d' m' c,
      corestep mon.(sem) tge d m d' m' -> 
      corestep_plus mon.(sem) tge (mon.(op) d c) m (mon.(op) d' c) m'

  ; atext_congr : 
      forall c d ef dep_sig args,
      at_external (sem mon) d = Some (ef,dep_sig,args) -> 
      at_external (sem mon) (mon.(op) d c) = Some (ef,dep_sig,args)

  ; aftext_congr : 
      forall c d rv d',
      after_external (sem mon) rv d = Some d' ->
      after_external (sem mon) rv (mon.(op) d c) = Some (mon.(op) d' c)

  ; call : 
      forall c ef dep_sig sig args d m id,
      at_external mon.(sem) c = Some (ef,dep_sig,args) ->
      ef = EF_external id sig -> 
      initial_core mon.(sem) tge (Vptr id Int.zero) args = Some d -> 
      corestep_plus mon.(sem) tge c m (mon.(op) d c) m 

  ; ret : 
      forall c d v c' m,
      halted mon.(sem) d = Some v -> 
      after_external mon.(sem) (Some v) c = Some c' -> 
      corestep_plus mon.(sem) tge (mon.(op) d c) m c' m }.

End Stacking_monoid_ok. End Stacking_monoid_ok.

Require Import pos.

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

Parameter main : val.

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

Notation linker_sem := 
  (LinkerSem.coresem one semantics (fun _ : ident => Some zero)).

Lemma stacking_init l vs : 
  initial_core linker_sem ge main vs = Some l -> 
  exists c,
  [/\ initial_core mon.(sem) tge main vs = Some c 
    & match_states l c].
Proof.
rewrite /= /LinkerSem.initial_core; case: main=> // b ofs.
case e: (Int.eq ofs Int.zero)=> //.
rewrite /initCore /=; case f: (initial_core _ _ _ _)=> [c|//].
case=> <-; exists c; split=> //.
by move: (Int.eq_spec ofs Int.zero); rewrite e=> ->.
Qed.

Lemma stacking_halt l c rv :
  match_states l c -> 
  halted linker_sem l = Some rv -> 
  halted mon.(sem) c = Some rv.
Proof.
move=> mtch; rewrite /= /LinkerSem.halted.
case inCtx: (~~inContext l)=> //.
rewrite /LinkerSem.halted0.
case h: (halted _ _)=> [rv'|//]; case=> <-.
move: h inCtx mtch; case: l=> fntbl; case; case=> // a l pf /=.
Opaque fold_stack. rewrite /match_states /= => hlt inCtx fld.
Transparent fold_stack. case: l fld pf inCtx=> //=; case=> <-.
by rewrite hlt.
Qed.

Lemma stacking_step l c m l' m' : 
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
apply: Stacking_monoid_ok.step_congr=> //.
by apply: mon_ok.
move: (projT2 (fold_stack_nonempty x)).
move: (@fold_stack_nonempty (b :: l)).
pattern pf at 0.
by case: (fold_stack _)=> // d pf'; case=> <-. }

{ move=> l m ef dep_sig args id d_ix d pf.
move=> atext fnid fntbl init fld; rewrite /pushCore.
move: (stack_push_wf l) pf.
pattern (all (atExternal semantics) (CallStack.callStack (Linker.stack l))) 
 at 0 1 2.
move: atext fntbl fld; case: l=> /= fn_tbl; case=> /=; case=> // a.
case=> //.
move=> pf atext fntbl fld IH all_atext; rewrite fld.
exists (op mon d c); split=> //.
move: fnid; rewrite /LinkerSem.fun_id; case: ef atext=> // id' sig atext.
case=> eq; subst id'.
apply: (@Stacking_monoid_ok.call _ _ _ mon _ mon_ok
        _ (EF_external id sig) dep_sig sig args d _ id)=> //.
by move: atext; move: fld; case=> <-.
move=> b l pf atext fntbl fld IH all_atext; rewrite fld.
exists (op mon d c); split=> //.
move: fnid; rewrite /LinkerSem.fun_id; case: ef atext=> // id' sig atext.
case=> eq; subst id'.
apply: (@Stacking_monoid_ok.call _ _ _ mon _ mon_ok
        _ (EF_external id sig) dep_sig sig args d _ id)=> //.
move: atext=> /=.
have x: is_true (0 < size [:: b & l]) by [].
move: fld; rewrite (@fold_stack_consE a [:: b & l] x); case=> <-.
by apply: (Stacking_monoid_ok.atext_congr mon_ok). }

{ Opaque fold_stack.
move=> l l'' m rv d' lt pop hlt aftext fld; case: l lt pop hlt fld.
move=> fn_tbl; case=> /=; case=> // a; case=> // b; case=> /=.
+ move=> pf lt pop hlt fld.
  Transparent fold_stack. simpl in fld. case: fld=> <-.
  move: pop; case/popCoreE=> pf2 []inCtx l''_eq; rewrite /= in l''_eq.
  move: aftext; rewrite l''_eq /= => aftext; exists d'; split=> //.
  by apply: (@Stacking_monoid_ok.ret _ _ _ mon _ mon_ok _ _ rv _ _ hlt).
+ Opaque fold_stack. move=> q l pf lt pop hlt fld.
  move: pop; case/popCoreE=> pf2 []inCtx l''_eq; rewrite /= in l''_eq.
  move: aftext; rewrite l''_eq /= => aftext.
  have x: is_true (0 < size [:: q & l]) by [].
  rewrite (@fold_stack_consE (Core.upd b d') (q :: l) x).
  exists (op mon d' (projT1 (fold_stack_nonempty x))); split=> //.
  have y: is_true (0 < size [:: b, q & l]) by [].
  move: (fld); rewrite (fold_stack_consE _ y); case=> <-.
  apply: (@Stacking_monoid_ok.ret _ _ _ mon _ mon_ok _ _ rv _ _ hlt)=> //.
  move: aftext.
  move: (projT2 (fold_stack_nonempty y)). 
  move: (@fold_stack_nonempty (b :: q :: l)).
  pattern pf at 0; case e: (fold_stack _)=> //[bql] nempty; case=> <- => aftext.
  have [ql fld_ql]: exists ql, fold_stack [:: q & l] = Some ql.
  { by case: (fold_stack_nonempty x)=> ql eq; exists ql. }
  move: (@Stacking_monoid_ok.aftext_congr _ _ _ mon _ mon_ok 
         ql _ (Some rv) _ aftext).
  have eq_bql: bql = op mon (Core.c b) ql.
  { Transparent fold_stack. clear - e fld_ql. 
    move: e fld_ql=> /=; case: l=> //; first by case=> <-; case=> <-.
    move=> a l; case f: (fold_stack _)=> [x|//].
    by case=> <-; case=> <-. }
  rewrite eq_bql=> ->; f_equal.
  Opaque fold_stack.
  clear - fld_ql; case: (fold_stack_nonempty x)=> /=.
  by rewrite fld_ql=> ?; case=> <-. }
Qed.

Import Barebones_simulation.

Lemma stacking_sim : Barebones_simulation linker_sem mon.(sem) ge tge main.
Proof.
apply: Build_Barebones_simulation.
by apply: ge_tge_agree.
by eapply stacking_init; eauto.
by eapply stacking_step; eauto.
by eapply stacking_halt; eauto.
Qed.

End Stacking_simulation.


