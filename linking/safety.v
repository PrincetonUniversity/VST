Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.
Unset Strict Implicit.

Require Import msl.Coqlib2.

Require Import Integers.

Require Import juicy_mem.
Require Import juicy_extspec.

Require Import pos.
Require Import linking. 

Section upd_exit.

Variable Z : Type.

Variable spec : external_specification juicy_mem external_function Z.

Definition upd_exit' (Q_exit : option val -> Z -> juicy_mem -> Prop) :=
  {| ext_spec_type := ext_spec_type spec
   ; ext_spec_pre := ext_spec_pre spec
   ; ext_spec_post := ext_spec_post spec
   ; ext_spec_exit := Q_exit |}.

Definition upd_exit (ef : external_function) (x : ext_spec_type spec ef) := 
  upd_exit' (ext_spec_post spec ef x (sig_res (ef_sig ef))).

End upd_exit.

Section safety.

Variable N : pos.

Variable plt : ident -> option 'I_N.

Variable sems : 'I_N -> Modsem.t juicy_mem.

Variable Z : Type.

Variable spec : external_specification juicy_mem external_function Z.

Variable ge : ge_ty.

Variable main_id : ident.

Definition main_ef := EF_external main_id LinkerSem.main_sig.

(* ASSUMPTIONS                                                            *)
(* We make the following assumptions on plt, spec, and ge:                *)
(*                                                                        *)
(* 1) For at_external cores, [ef_sig ef = sig]. This assumption will      *)
(* be made redundant if we change the type of at_external to              *)
(*   C -> option (external_function*seq val).                             *)

Variable sigs_match : 
  forall (idx : 'I_N) c ef sig args,
  at_external (sems idx).(Modsem.sem) c = Some (ef, sig, args) ->
  sig = ef_sig ef.

(* 2) The postconditions of each external function at least imply         *)
(* that the function return values are well-typed with respect to         *)
(* the function signatures. This is a property required for compiler      *)
(* correctness -- e.g., in the register allocation phase that determines  *)
(* in which class of registers to stick return values. It shows up        *)
(* here because we enforce the property by building it into the           *)
(* linking operational semantics.                                         *)

Variable rets_welltyped : 
  forall ef x rv z m,
  ext_spec_post spec ef x (sig_res (ef_sig ef)) (Some rv) z m -> 
  val_casted.val_has_type_func rv (proj_sig_res (ef_sig ef)).

(* 3) Whenever [plt fid = Some idx] (that is, the PLT claims that [fid]   *)
(* is implemented by module [idx], then that module's global env.         *)
(* maps [fid] to some address [bf]. Property 4) below ensures that        *)
(* initializing the module at [bf] succeeds.                              *)

Variable entry_points_exist :
  forall fid idx, 
  plt fid = Some idx -> 
  exists bf, Genv.find_symbol (Modsem.ge (sems idx)) fid = Some bf.

(* 4) Initializing module [idx] to run a function [fid] we claim module   *)
(* [idx] defines results in a new state, [c], that is safe. Safety is     *)
(* w/r/t the [spec'] that results from overwriting the exit condition     *)
(* of [spec] with the postcondition of function [fid].                    *)

Variable entry_points_safe : 
  forall ef fid idx bf args z m,
  let: tys := sig_args (ef_sig ef) in
  let: rty := sig_res (ef_sig ef) in
  LinkerSem.fun_id ef = Some fid -> 
  plt fid = Some idx -> 
  let: ge_idx := Modsem.ge (sems idx) in
  let: sem_idx := Modsem.sem (sems idx) in
  Genv.find_symbol ge_idx fid = Some bf -> 
  forall x : ext_spec_type spec ef,
  ext_spec_pre spec ef x tys args z m -> 
  exists c, 
    [/\ initial_core sem_idx ge_idx (Vptr bf Int.zero) args = Some c 
      & (forall n, safeN sem_idx (upd_exit x) ge_idx n z c m)].

(* 5) The overall [ge] is a superset of each per-module [ge].  In         *)
(* particular, this implies that the module [ge]s agree with *each other* *)
(* whenever their domains overlap.                                        *)

Variable genvs_consistent :
  forall idx id bf,
  Genv.find_symbol (Modsem.ge (sems idx)) id = Some bf -> 
  Genv.find_symbol ge id = Some bf.

Notation linked_sem := (LinkerSem.coresem N sems plt).

Notation linked_st := (Linker.t N sems).

Require Import stack.

Fixpoint tail_safe (n : nat)
    (ef : external_function) (x : ext_spec_type spec ef)
    (efs : seq external_function) (s : Stack.t (Core.t sems)) : Prop :=
  match efs, s with 
    | nil, nil => True
    | ef_top :: efs', c :: s' => 
        let: c_idx := Core.i c in
        let: c_c := Core.c c in 
        let: c_sig := Core.sg c in 
        let: c_ge := Modsem.ge (sems c_idx) in
        let: c_sem := Modsem.sem (sems c_idx) in
          c_sig = ef_sig ef_top /\
          exists sig args z m (x_top : ext_spec_type spec ef_top), 
          [/\ at_external c_sem c_c = Some (ef, sig, args) 
            , ext_spec_pre spec ef x (sig_args sig) args z m 
            , (forall ret m' z',
               ext_spec_post spec ef x (sig_res sig) ret z' m' ->
               let: spec' := @upd_exit _ spec ef_top x_top in
               exists c', 
               [/\ after_external c_sem ret c_c = Some c'
                 & safeN c_sem spec' c_ge n z' c' m'])
           & @tail_safe n ef_top x_top efs' s']
    | _, _ => False
  end.

Lemma tail_safe_downward1 ef n Hx efs l :
  tail_safe n.+1 (ef:=ef) Hx efs l -> 
  tail_safe n (ef:=ef) Hx efs l.
Proof.
elim: efs ef Hx l=> // ef' efs' IH ef Hx; case=> // a1 l1.
move=> /= []Hsg []sig []args []z []m []x_top []Hat Hpre Hpost Htl; split=> //.
exists sig, args, z, m, x_top; split=> //.
move=> ret m' z' Hpost'; case: (Hpost _ _ _ Hpost')=> c' []Haft Hsafe.
exists c'; split=> //; first by apply: safe_downward1.
by move {Hpost}; apply: IH.
Qed.

Definition head_safe n ef (x : ext_spec_type spec ef) (c : Core.t sems) z m :=
  let: c_idx := Core.i c in
  let: c_c := Core.c c in 
  let: c_sig := Core.sg c in 
  let: c_ge := Modsem.ge (sems c_idx) in
  let: c_sem := Modsem.sem (sems c_idx) in
  [/\ c_sig = ef_sig ef 
    & safeN c_sem (@upd_exit _ spec ef x) c_ge n z c_c m].

Definition stack_safe (n : nat)
    (efs : seq external_function) (s : Stack.t (Core.t sems)) z m : Prop :=
  match efs, s with
    | nil, nil => True
    | ef :: efs', c :: s' => 
      exists x : ext_spec_type spec ef,
      [/\ @head_safe n ef x c z m & @tail_safe n ef x efs' s']
    | _, _ => False
  end.

Fixpoint last_frame_main (efs : seq external_function) :=
  match efs with
    | nil => True
    | [:: ef] => ef = main_ef 
    | [:: _ & efs'] => last_frame_main efs'
  end.

Definition all_safe n z (l : linked_st) m :=
  exists efs : list external_function, 
  [/\ last_frame_main efs
    & stack_safe n efs (CallStack.callStack (Linker.stack l)) z m].

Lemma all_safe_inv n z l m (Hplt : Linker.fn_tbl l = plt) :
  all_safe (S n) z l m -> 
  [\/ exists l' m', 
      [/\ Linker.fn_tbl l' = plt
        , corestep linked_sem ge l m l' m' 
        & all_safe n z l' m']
    , exists rv, halted linked_sem l = Some rv
    | exists ef sig args, 
        LinkerSem.at_external l = Some (ef, sig, args) 
        /\ exists x : ext_spec_type spec ef,
             ext_spec_pre spec ef x (sig_args sig) args z m
             /\ forall ret m' z',
                ext_spec_post spec ef x (sig_res sig) ret z' m' ->
                exists l', 
                  [/\ Linker.fn_tbl l' = plt
                    , LinkerSem.after_external ret l = Some l' 
                    & all_safe n z' l' m']].
Proof.
case=> efs; case: l Hplt=> fn_tbl; case. 
case=> //= a1 l1 Hwf Hplt; subst; case=> LFM.
case: efs LFM=> // ef efs' LFM; case=> Hx []Hhd Htl. 
move: Hhd; rewrite /head_safe /=.
case Hat: (at_external _ _)=> [[[ef' sig'] args']|].

{ (* at_external topmost core = Some *)
have ->: halted (Modsem.sem (sems (Core.i a1))) (Core.c a1) = None.
{ case: (at_external_halted_excl (Modsem.sem (sems (Core.i a1))) (Core.c a1))=> //.
  by rewrite Hat. }
case=> Hsg []Hx' []Hpre Hpost.
set l := {| Linker.fn_tbl := plt
          ; Linker.stack := CallStack.mk (a1 :: l1) Hwf |}.

case Hat': (LinkerSem.at_external l)=> [[[ef'' sig''] args'']|].

+ (* at_external linker = Some *)
apply: Or33; move: Hat'. 
rewrite /LinkerSem.at_external /LinkerSem.at_external0 Hat.
case Hfid: (LinkerSem.fun_id _)=> // [fid|].

case Hidx: (Linker.fn_tbl _ _)=> //; case=> Ha Hb Hc; subst.
exists ef'', sig'', args''; split=> //; exists Hx'; split=> //.
move=> ret z' m' Hpost'; case: (Hpost _ _ _ Hpost')=> c' []Haft Hsafe.
set l' := {| Linker.fn_tbl := plt
           ; Linker.stack := CallStack.mk ((Core.upd a1 c') :: l1) Hwf |}.
exists l'; split=> //.
rewrite /LinkerSem.after_external Haft /l /l' /updCore /updStack /=.
by f_equal; f_equal; f_equal; apply: proof_irr.
exists [:: ef & efs']; split=> //. 
by exists Hx; split=> //; apply: tail_safe_downward1.

case=> <- <- <-; exists ef', sig', args'; split=> //; exists Hx'; split=> //.
move=> ret z' m' Hpost'; case: (Hpost _ _ _ Hpost')=> c' []Haft Hsafe.
set l' := {| Linker.fn_tbl := plt
           ; Linker.stack := CallStack.mk ((Core.upd a1 c') :: l1) Hwf |}.
exists l'; split=> //.
rewrite /LinkerSem.after_external Haft /l /l' /updCore /updStack /=.
by f_equal; f_equal; f_equal; apply: proof_irr.
exists [:: ef & efs']; split=> //. 
by exists Hx; split=> //; apply: tail_safe_downward1.

+ (* at_external linker = None *)
move: Hat'; rewrite /LinkerSem.at_external /LinkerSem.at_external0 Hat.
case Hfid: (LinkerSem.fun_id _)=> // [fid].
case Hidx: (Linker.fn_tbl _ _)=> // [idx] _.
apply: Or31.
have Hall: all (atExternal sems) (CallStack.callStack (Linker.stack l)).
{ rewrite /l /=; apply /andP; split.
  by rewrite /atExternal; case: a1 Hwf l Hidx Hat Hsg Hpost=> ?????? ->.
  by move {l Hidx}; move: Hwf; rewrite /wf_callStack; case/andP. }
move: (entry_points_safe).
have [bf Hfind]: 
  exists bf, Genv.find_symbol (sems idx).(Modsem.ge) fid = Some bf.
{ by apply: entry_points_exist. }
have Hsg': sig_args sig' = sig_args (ef_sig ef').
  by rewrite (sigs_match Hat).
rewrite Hsg' in Hpre.
move: (@entry_points_safe ef' fid idx bf args' z m Hfid Hidx Hfind).
case/(_ Hx' Hpre)=> c0 []Hinit Hsafe Hpost'.
set c := (Core.mk _ _ _ c0 (ef_sig ef')).
set l' := pushCore l c Hall. 
exists l', m; split=> //. 
right; split=> //; split.
{ (* no corestep *)
  move=> Hstep; move: (LinkerSem.corestep_not_at_external0 Hstep).
  by rewrite /LinkerSem.at_external0 Hat. 
}
rewrite /LinkerSem.at_external0 Hat.
rewrite Hfid.
have [l'' [Hleq Hhdl]]: 
  exists l'', 
  [/\ l'=l''
    & LinkerSem.handle (ef_sig ef') fid l args' = Some l''].
{ exists l'. 
  rewrite LinkerSem.handleP; split=> //.
  exists Hall, idx, bf, c; split=> //.
  by rewrite /initCore Hinit /c. }
by rewrite Hhdl.

{ (* all_safe *)
exists [:: ef', ef & efs']; split=> //. 
exists Hx'; split=> //; split=> //.
exists sig', args', z, m, Hx; split=> //; first by rewrite Hsg'.
by apply: tail_safe_downward1.
}
}

case Hhlt: (halted _ _)=> [rv|].

{ (* halted *)
case=> Hsg Hexit; case: l1 Hwf Htl.

+ (* l1 = [::] *) 
move=> Hwf; case: efs' LFM=> // LFM _; apply: Or32; exists rv.
rewrite /LinkerSem.halted /inContext /=.
rewrite /LinkerSem.halted0 /peekCore /= Hhlt.
have Hty: val_casted.val_has_type_func rv (proj_sig_res (ef_sig ef))
  by apply: rets_welltyped.
by rewrite Hsg Hty.

+ (* l1 = [a2 :: l2] *)
move=> a2 l2 Hwf; case: efs' LFM=> // ef' efs'' LFM []Hsg' Htl.
move: Htl; case=> sig []args []z0 []m0 []x0 []Hat0 Hpre0.
have ->: sig_res sig = sig_res (ef_sig ef) by rewrite (sigs_match Hat0).
case/(_ (Some rv) m z Hexit)=> c' []Haft0 Hsafe Htl; apply: Or31.
have Hwf': wf_callStack [:: a2 & l2].
{ clear -Hwf; move: Hwf; rewrite /wf_callStack; case/andP=> /=.
  by case/andP=> ? ? ?; apply/andP; split. }
set l' := {| Linker.fn_tbl := plt
           ; Linker.stack := CallStack.mk [:: a2 & l2] Hwf' |}.
exists (updCore l' (Core.upd a2 c')), m; split=> //.
right; split=> //.
have Hty: val_casted.val_has_type_func rv (proj_sig_res (ef_sig ef)) 
  by eapply rets_welltyped; eauto.
split.
{ (* no corestep *)
  move=> Hstep; move: (LinkerSem.corestep_not_halted0' Hstep).
  by rewrite /LinkerSem.halted0 /= Hhlt Hsg Hty.
}
rewrite /LinkerSem.at_external0 /peekCore /= Hat.
rewrite /inContext /=.
rewrite /LinkerSem.halted0 /peekCore /= Hhlt.
rewrite Hsg Hty.
rewrite /LinkerSem.after_external /peekCore /= Haft0.
f_equal.
f_equal.
apply: proof_irr.

{ (* all_safe *)
exists [:: ef' & efs'']; split=> //; exists x0; split.

+ (* head_safe *)
split=> //.
clear -Hsafe.
move: Hsafe.
case: a2 c'=> i c sg c'.
rewrite /Core.upd /Core.i /Core.c.
by apply: safe_downward1.
rewrite -/tail_safe in Htl; rewrite /=.
by apply: tail_safe_downward1.
}
}

{ (* corestep *)
case=> Hsg; case=> c' []m' []Hstep Hsafe; apply: Or31.
set l := {| Linker.fn_tbl := plt
          ; Linker.stack := CallStack.mk (a1 :: l1) Hwf |}.
exists (updCore l (Core.upd a1 c')), m'; split=> //.
by left; rewrite /LinkerSem.corestep0 /peekCore; exists c'.

{ (* all_safe *)
exists [:: ef & efs']; split=> //. 
by exists Hx; split=> //; apply: tail_safe_downward1.
}
}
Qed.

Lemma linker_safe n x z m main_idx main_b args 
                  (Hunit : ext_spec_type spec main_ef = unit) :
  LinkerSem.fun_id main_ef = Some main_id -> 
  plt main_id = Some main_idx -> 
  Genv.find_symbol (sems main_idx).(Modsem.ge) main_id = Some main_b -> 
  ext_spec_pre spec main_ef x (sig_args (ef_sig main_ef)) args z m ->
  exists l, 
  [/\ initial_core linked_sem ge (Vptr main_b Int.zero) args = Some l  
    & safeN linked_sem (upd_exit x) ge n z l m].
Proof.
move=> Hfid Hplt Hfind Hpre.
have Hfind': Genv.find_symbol ge main_id = Some main_b.
{ by apply: (genvs_consistent Hfind). }
have Hinv: Genv.invert_symbol ge main_b = Some main_id.
{ by rewrite (Genv.find_invert_symbol _ _ Hfind'). }
have [l Hinit]:
  exists l, initial_core linked_sem ge (Vptr main_b Int.zero) args = Some l.
{ rewrite /= /LinkerSem.initial_core; case Heq: (Int.eq _ _)=> //.
  rewrite Hinv Hplt /initCore. 
  case: (entry_points_safe Hfid Hplt Hfind Hpre)=> c []-> Hsafe.
  by eexists; eauto. }
exists l; split=> //.

have [fn_tbl_plt init_all_safe]: 
  [/\ Linker.fn_tbl l = plt & all_safe n z l m].
{ case: l Hinit=> fn_tbl; case.
  case=> // a1 l1 Hwf Hinit.
  case: (entry_points_safe Hfid Hplt Hfind Hpre)=> c []Hinit' Hsafe.  
  move: Hinit=> /=.
  case Heq: (Int.eq _ _)=> //.
  rewrite Hinv Hplt /initCore.
  case Hinit: (initial_core _ _ _ _)=> // [c']; case=> Heq' <- Hl1.
  split=> //.
  exists [:: main_ef]; split=> //. 
  exists x; split=> //.
  rewrite Hinit in Hinit'; case: Hinit'=> ->; split=> //=.
  by rewrite -Hl1.
}

clear -fn_tbl_plt init_all_safe Hunit.
elim: n z m l fn_tbl_plt init_all_safe=> // n IH z m l fn_tbl all_safe.
case: (all_safe_inv fn_tbl all_safe).

{ (* corestep0 *)
case=> l' []m' []Hplt Hstep Hall_safe /=.
rewrite (LinkerSem.corestep_not_at_external ge Hstep).
rewrite (LinkerSem.corestep_not_halted ge Hstep).
exists l', m'; split=> //.
by apply: (IH z m' l' Hplt Hall_safe).
}

{ (* halted *)
case=> rv Hhlt /=.
have ->: LinkerSem.at_external l = None.
{ case: (LinkerSem.at_external_halted_excl l)=> //.
  by move: Hhlt=> /= ->. }
move: (Hhlt)=> /= ->.
move: Hhlt; rewrite /= /LinkerSem.halted.
case Hctx: (~~ inContext l)=> //.
case Hhlt: (LinkerSem.halted0 l)=> // [rv']; case=> <-.
move: Hhlt; rewrite /LinkerSem.halted0.
case Hhlt: (halted _ _)=> // [rv''].
case: (val_casted.val_has_type_func _ _)=> //; case=> <-.
move: all_safe; rewrite /all_safe=> [][]; case.
case=> _; move {fn_tbl}; case: l Hhlt Hctx=> ?; case; case=> //.
move=> ef efs'; move {fn_tbl}. 
case: l Hhlt Hctx=> ?; case. 
case=> // a1 l1 /= Hwf Hhlt Hctx []LFM []x' []Hhd Htl.
case: Hhd=> _ /=; rewrite Hhlt.
case: (at_external_halted_excl (Modsem.sem (sems (Core.i a1))) (Core.c a1)).
move=> -> //.
move: LFM.
have ->: efs' = [::].
{ clear -Htl Hctx; move: Htl Hctx.
  rewrite /inContext /=.
  case: efs'=> // ef' efs'.
  case: l1 Hwf=> //. }
move=> Heq.
clear -Heq Hunit.
move: x x'.
rewrite Heq.
move {ef Heq}.
move=> x x'.
Require Import JMeq.
have Eqxx': JMeq x x'.
{ by clear -Hunit; move: x x'; rewrite Hunit; case; case. }
by move: (JMeq_eq Eqxx')=> -> /=.
by rewrite Hhlt; case.
}

{ (* at_external *)
case=> ef []sig []args []Hat []x' []Hpre Hpost /=.
rewrite Hat.
case: (LinkerSem.at_external_halted_excl l).
by rewrite Hat.
move=> ->.
exists x'.
split=> //.
move=> ret m' z' Hpost'.
case: (Hpost ret m' z' Hpost')=> l' []Hplt Haft Hall.
exists l'.
split=> //.
by apply: (IH _ _ _ Hplt Hall).
}
Qed.

End safety.  