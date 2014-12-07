Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.
Unset Strict Implicit.

Require Import JMeq.

Require Import msl.Coqlib2.

Require Import Integers.

Require Import juicy_mem.
Require Import juicy_extspec.
Require Import juicy_safety.

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

Definition upd_exit (ef : external_function) (x : ext_spec_type spec ef) ge := 
  upd_exit' (ext_spec_post spec ef x ge (sig_res (ef_sig ef))).

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

(** ASSUMPTIONS
We make the following assumptions on plt, spec, and ge: *)

(** 1) For at_external cores, [ef_sig ef = sig]. This assumption will
be made redundant if we change the type of at_external to
  C -> option (external_function*seq val). *)

Variable sigs_match : 
  forall (idx : 'I_N) c ef sig args,
  at_external (sems idx).(Modsem.sem) c = Some (ef, sig, args) ->
  sig = ef_sig ef.

(** 2) The postconditions of each external function at least imply
that the function return values are well-typed with respect to
the function signatures. This is a property required for compiler
correctness -- e.g., in the register allocation phase that determines
in which class of registers to stick return values. It shows up
here because we enforce the property by building it into the
linking operational semantics. *)

Variable rets_welltyped : 
  forall ef x ge rv z m,
  ext_spec_post spec ef x ge (sig_res (ef_sig ef)) (Some rv) z m -> 
  val_casted.val_has_type_func rv (proj_sig_res (ef_sig ef)).

(** 3) Whenever [plt fid = Some idx] (that is, the PLT claims that [fid]
is implemented by module [idx], then that module's global env.
maps [fid] to some address [bf]. Property 4) below ensures that
initializing the module at [bf] succeeds. *)

Variable entry_points_exist :
  forall fid idx, 
  plt fid = Some idx -> 
  exists bf, Genv.find_symbol (Modsem.ge (sems idx)) fid = Some bf.

(** 4) Initializing module [idx] to run a function [fid] we claim module
[idx] defines results in a new state, [c], that is safe. Safety is
w/r/t the [spec'] that results from overwriting the exit condition
of [spec] with the postcondition of function [fid]. *)

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
  ext_spec_pre spec ef x (Genv.genv_symb ge_idx) tys args z m -> 
  exists c, 
    [/\ initial_core sem_idx ge_idx (Vptr bf Int.zero) args = Some c 
      & (forall n, safeN sem_idx (upd_exit x (Genv.genv_symb ge_idx)) ge_idx n z c m)].

(** 5) Because we've added [genv_symb] to [ext_spec], we now appear to require a 
stronger assumption, that the symbol tables are equal. *)

(** The other alternative here is to require that specifications be monotonic
in some way. *)

Variable genv_symbols_eq :
  forall idx, Genv.genv_symb ge = Genv.genv_symb (Modsem.ge (sems idx)).

(** 5a) The overall [ge] is a superset of each per-module [ge].  In
particular, this implies that the module [ge]s agree with *each other*
whenever their domains overlap. *)

Lemma genvs_consistent idx id bf :
  Genv.find_symbol (Modsem.ge (sems idx)) id = Some bf -> 
  Genv.find_symbol ge id = Some bf.
Proof.
by rewrite /Genv.find_symbol -genv_symbols_eq.
Qed.

(** 6) Coresteps of the underlying semantics imply [Hrel] and that 
       [level m' = level m + 1]. *)

Variable corestep_hrel: 
  forall idx c m c' m', 
  corestep (Modsem.sem (sems idx)) (Modsem.ge (sems idx)) c m c' m' ->
  [/\ Hrel (ageable.level m') m m' 
    & ageable.level m = (ageable.level m').+1].

(** 7) *)

Variable age_safe:
  forall Z Hspec idx (z : Z) ge m m' c,
  ageable.age m m' -> 
  safeN (Modsem.sem (sems idx)) Hspec ge (ageable.level m) z c m ->
  safeN (Modsem.sem (sems idx)) Hspec ge (ageable.level m') z c m'.

Notation linked_sem := (LinkerSem.coresem _ N sems plt).

Notation linked_st := (Linker.t N sems).

Require Import stack.

Fixpoint tail_safe 
    (ef : external_function) (x : ext_spec_type spec ef)
    (efs : seq external_function) (s : Stack.t (Core.t sems)) m : Prop :=
  match efs, s with 
    | nil, nil => True
    | ef_top :: efs', c :: s' => 
        let: c_idx := Core.i c in
        let: c_c := Core.c c in 
        let: c_sig := Core.sg c in 
        let: c_ge := Modsem.ge (sems c_idx) in
        let: c_sem := Modsem.sem (sems c_idx) in
          c_sig = ef_sig ef_top /\
          exists sig args z m0 (x_top : ext_spec_type spec ef_top), 
          [/\ Hrel (ageable.level m) m0 m
            , at_external c_sem c_c = Some (ef, sig, args) 
            , ext_spec_pre spec ef x (Genv.genv_symb ge) (sig_args sig) args z m0 
            , (forall ret m' z',
               Hrel (ageable.level m') m0 m' -> 
               ext_spec_post spec ef x (Genv.genv_symb ge) (sig_res sig) ret z' m' ->
               let: spec' := @upd_exit _ spec ef_top x_top in
               exists c', 
               [/\ after_external c_sem ret c_c = Some c'
                 & safeN c_sem (spec' (Genv.genv_symb c_ge)) c_ge (ageable.level m') z' c' m'])
           & @tail_safe ef_top x_top efs' s' m]
    | _, _ => False
  end.

Lemma Hrel_trans m0 m m' : 
  Hrel (ageable.level m) m0 m -> 
  Hrel (ageable.level m') m m' -> 
  Hrel (ageable.level m') m0 m'.
Proof.
rewrite /Hrel; case=> H1 []H2 H2a; case=> H3 []H4 H4a; split; first by omega.
split; first by omega.
move=> loc; move: (H2a loc) (H4a loc); rewrite /pures_sub.
case: (compcert_rmaps.RML.R.resource_at (m_phi m0) _)=> // k p -> ->.
rewrite compcert_rmaps.RML.preds_fmap_fmap compcert_rmaps.RML.approx_oo_approx' //.
omega.
Qed.

Lemma tail_safe_Hrel ef Hx efs l m m' (Hr: Hrel (ageable.level m') m m') :
  tail_safe (ef:=ef) Hx efs l m -> 
  tail_safe (ef:=ef) Hx efs l m'.
Proof.
elim: efs ef Hx l=> // ef' efs' IH ef Hx; case=> // a1 l1.
move=> /= []Hsg []sig []args []z []m0 []x_top []Hr' Hat Hpre Hpost Htl; split=> //.
exists sig, args, z, m0, x_top; split=> //; first by move: Hr' Hr; apply: Hrel_trans.
by apply: IH.
Qed.

Lemma age1_Hrel m m' : ageable.age1 m = Some m' -> Hrel (ageable.level m') m m'.
Proof.
move=> Hag; split=> //; split=> //.
by apply ageable.age_level in Hag; rewrite Hag; omega.
apply age1_juicy_mem_Some in Hag=> loc.
move: (compcert_rmaps.RML.age1_resource_at _ _ Hag loc).
case Hres: (compcert_rmaps.RML.R.resource_at _ _)=> //= Heq.
eapply compcert_rmaps.RML.necR_PURE in Hres; eauto.
by constructor.
Qed.

Lemma age_tail_safe ef Hx efs l m m' (Hag: ageable.age m m') : 
  tail_safe (ef:=ef) Hx efs l m -> 
  tail_safe (ef:=ef) Hx efs l m'.
Proof.
by apply: tail_safe_Hrel; apply: age1_Hrel.
Qed.

Definition head_safe ef (x : ext_spec_type spec ef) (c : Core.t sems) z m :=
  let: c_idx := Core.i c in
  let: c_c := Core.c c in 
  let: c_sig := Core.sg c in 
  let: c_ge := Modsem.ge (sems c_idx) in
  let: c_sem := Modsem.sem (sems c_idx) in
  [/\ c_sig = ef_sig ef 
    & safeN c_sem (@upd_exit _ spec ef x (Genv.genv_symb c_ge)) c_ge (ageable.level m) z c_c m].

Definition stack_safe 
    (efs : seq external_function) (s : Stack.t (Core.t sems)) z m : Prop :=
  match efs, s with
    | nil, nil => True
    | ef :: efs', c :: s' => 
      exists x : ext_spec_type spec ef,
      [/\ @head_safe ef x c z m & @tail_safe ef x efs' s' m]
    | _, _ => False
  end.

Fixpoint last_frame_main (efs : seq external_function) :=
  match efs with
    | nil => True
    | [:: ef] => ef = main_ef 
    | [:: _ & efs'] => last_frame_main efs'
  end.

Definition all_safe z (l : linked_st) m :=
  exists efs : list external_function, 
  [/\ last_frame_main efs
    & stack_safe efs (CallStack.callStack (Linker.stack l)) z m].

Lemma all_safe_inv z l m 
      (Hplt : Linker.fn_tbl l = plt) 
      (Hag : (ageable.level m > 0)%coq_nat) :
  all_safe z l m -> 
  [\/ exists l' m', 
      [/\ Linker.fn_tbl l' = plt
        , corestep linked_sem ge l m l' m' 
        & all_safe z l' m']
    , exists rv, halted linked_sem l = Some rv
    | exists ef sig args, 
        LinkerSem.at_external l = Some (ef, sig, args) 
        /\ exists x : ext_spec_type spec ef,
             ext_spec_pre spec ef x (Genv.genv_symb ge) (sig_args sig) args z m
             /\ forall ret m' z' n'',
                (n'' <= ageable.level m')%nat ->
                Hrel (ageable.level m') m m' -> 
                ext_spec_post spec ef x (Genv.genv_symb ge) (sig_res sig) ret z' m' ->
                exists l', 
                  [/\ Linker.fn_tbl l' = plt
                    , LinkerSem.after_external ret l = Some l' 
                    & all_safe z' l' m']].
Proof.
case=> efs; case: l Hplt=> fn_tbl; case. 
case=> //= a1 l1 Hwf Hplt; subst; case=> LFM.
case: efs LFM=> // ef efs' LFM; case=> Hx []Hhd Htl. 
move: Hhd; rewrite /head_safe; case=> Hsig. 
case Hat: (at_external (Modsem.sem (sems (Core.i a1))) (Core.c a1))=> [[[ef' sig'] args']|].
inversion 1; subst; first by rewrite H0 level_juice_level_phi in Hag; omega.
by apply corestep_not_at_external in H0; rewrite H0 in Hat.

{ (* at_external topmost core = Some *)
rewrite Hat in H0; inversion H0; subst; move {H0}; move: H1 H2=> Hpre Hpost.
have Hhlt: halted (Modsem.sem (sems (Core.i a1))) (Core.c a1) = None.
{ case: (at_external_halted_excl (Modsem.sem (sems (Core.i a1))) (Core.c a1))=> //.
  by rewrite Hat. }
set l := {| Linker.fn_tbl := plt
          ; Linker.stack := CallStack.mk (a1 :: l1) Hwf |}.

case Hat': (LinkerSem.at_external l)=> [[[ef'' sig''] args'']|].

+ (* at_external linker = Some *)
apply: Or33; move: Hat'. 
rewrite /LinkerSem.at_external /LinkerSem.at_external0 Hat.
case Hfid: (LinkerSem.fun_id _)=> // [fid|].

case Hidx: (Linker.fn_tbl _ _)=> //; case=> Ha Hb Hc; subst.
exists ef'', sig'', args''; split=> //; exists x; split=> //.
by rewrite -genv_symbols_eq in Hpre.
rewrite -genv_symbols_eq in Hpost.
move=> ret m' z' n'' Hlev' Hrel' Hpost'. 
have Hlev: ((ageable.level (m_phi m') <= n)%coq_nat).
{ 
 case: Hrel'=> ->; case=> X _; rewrite -level_juice_level_phi in H.
 rewrite -H in X; omega.
}
case: (Hpost _ _ _ _ Hlev Hrel' Hpost')=> c' []Haft Hsafe.
set l' := {| Linker.fn_tbl := plt
           ; Linker.stack := CallStack.mk ((Core.upd a1 c') :: l1) Hwf |}.
exists l'; split=> //.
rewrite /LinkerSem.after_external Haft /l /l' /updCore /updStack /=.
by f_equal; f_equal; f_equal; apply: proof_irr.
exists [:: ef & efs']; split=> //. 
exists Hx; split=> //. 
split=> //; rewrite -genv_symbols_eq //.
by apply: (tail_safe_Hrel Hrel').

case=> <- <- <-; exists e, sig, args; split=> //; exists x; split=> //.
by rewrite -genv_symbols_eq in Hpre.
rewrite -genv_symbols_eq in Hpost.
move=> ret m' z' n'' Hlev' Hrel' Hpost'. 
have Hlev: ((ageable.level (m_phi m') <= n)%coq_nat).
{ 
 case: Hrel'=> ->; case=> X _; rewrite -level_juice_level_phi in H.
 rewrite -H in X; omega.
}
case: (Hpost _ _ _ _ Hlev Hrel' Hpost')=> c' []Haft Hsafe.
set l' := {| Linker.fn_tbl := plt
           ; Linker.stack := CallStack.mk ((Core.upd a1 c') :: l1) Hwf |}.
exists l'; split=> //.
rewrite /LinkerSem.after_external Haft /l /l' /updCore /updStack /=.
by f_equal; f_equal; f_equal; apply: proof_irr.
exists [:: ef & efs']; split=> //. 
exists Hx; split=> //. 
split=> //; rewrite -genv_symbols_eq //.
by apply: (tail_safe_Hrel Hrel').

+ (* at_external linker = None *)
move: Hat'; rewrite /LinkerSem.at_external /LinkerSem.at_external0 Hat.
case Hfid: (LinkerSem.fun_id _)=> // [fid].
case Hidx: (Linker.fn_tbl _ _)=> // [idx] _.
apply: Or31.
have Hall: all (atExternal sems) (CallStack.callStack (Linker.stack l)).
{ rewrite /l /=; apply /andP; split.
  by rewrite /atExternal; case: a1 Hwf l Hidx Hat Hsig b x Hhlt Hpre Hpost=> ?????? ->.
  by move {l Hidx}; move: Hwf; rewrite /wf_callStack; case/andP. }
move: (entry_points_safe).
have [bf Hfind]: 
  exists bf, Genv.find_symbol (sems idx).(Modsem.ge) fid = Some bf.
{ by apply: entry_points_exist. }
have Hsg': sig_args sig = sig_args (ef_sig e).
  by rewrite (sigs_match Hat).
rewrite Hsg' in Hpre.
move: (@entry_points_safe e fid idx bf args z m Hfid Hidx Hfind).
rewrite -!genv_symbols_eq in Hpre|-*.
case/(_ x Hpre)=> c0 []Hinit Hsafe Hpost'.
set c := (Core.mk _ _ _ c0 (ef_sig e)); set l' := pushCore l c Hall. 
case Hag': (ageable.age1 m)=> [m'|].
exists l', m'; split=> //. right; split=> //; split.
{ (* no corestep *)
  move=> Hstep; move: (LinkerSem.corestep_not_at_external0 Hstep).
  by rewrite /LinkerSem.at_external0 Hat. 
}
rewrite /LinkerSem.at_external0 Hat Hfid.
have [l'' [Hleq Hhdl]]: exists l'', 
  [/\ l'=l'' & LinkerSem.handle (ef_sig e) fid l args = Some l''].
{ exists l'; rewrite LinkerSem.handleP; split=> //.
  by exists Hall, idx, bf, c; split=> //; rewrite /initCore Hinit /c. }
by rewrite Hhdl.

{ (* all_safe *)
exists [:: e, ef & efs']; split=> //; exists x; split=> //; split=> //.
move: (Hsafe); move/(_ (ageable.level m)).
by rewrite -genv_symbols_eq; apply: age_safe.
exists sig, args, z, m, Hx; split=> //. 
by apply: age1_Hrel.
by rewrite Hsg'.
rewrite -!genv_symbols_eq in Hpost|-* => ret m'' z' Hrel' Hq'.
have Hlev'': (((ageable.level m'') <= n)%coq_nat). 
{ case: Hrel'=> _ []Hag'' _. 
  by rewrite -level_juice_level_phi in H; omega. }
case: (Hpost ret m'' z' _ Hlev'' Hrel' Hq')=> c' []Haft Hsafe'.
by exists c'; split=> //; eapply safe_downward; eauto.
by apply: (age_tail_safe (m:=m)).
}

by move: Hag; move: Hag'; move/ageable.age1_level0=> -> ?; omega.
}

{ 
case: (at_external_halted_excl (Modsem.sem (sems (Core.i a1))) (Core.c a1)).
by rewrite Hat. by rewrite H.
}

case Hhlt: (halted (Modsem.sem (sems (Core.i a1))) (Core.c a1))=> [rv|].
inversion 1; subst; first by rewrite H0 level_juice_level_phi in Hag; omega.
by apply corestep_not_halted in H0; rewrite H0 in Hhlt.
by rewrite H0 in Hat.
rewrite Hhlt in H; inversion H; subst; move {H}.

{ (* halted *)
move: H0=> Hexit; case: l1 Hwf Htl.

+ (* l1 = [::] *) 
move=> Hwf; case: efs' LFM=> // LFM _; apply: Or32; exists i.
rewrite /LinkerSem.halted /inContext /= /LinkerSem.halted0 /peekCore /= Hhlt.
have Hty: val_casted.val_has_type_func i (proj_sig_res (ef_sig ef)).
{ apply: rets_welltyped=> //; first by apply: (Genv.genv_symb ge).
  by rewrite -genv_symbols_eq in Hexit. }
by rewrite Hsig Hty. 

+ (* l1 = [a2 :: l2] *)
move=> a2 l2 Hwf; case: efs' LFM=> // ef' efs'' LFM []Hsg' Htl.
move: Htl; case=> sig []args []z0 []m0 []x0 []Hrel []Hat0 Hpre0.
have ->: sig_res sig = sig_res (ef_sig ef) by rewrite (sigs_match Hat0).
rewrite -!genv_symbols_eq in Hexit|-*.
case/(_ (Some i) m z Hrel Hexit)=> c' []Haft0 Hsafe Htl; apply: Or31.
have Hwf': wf_callStack [:: a2 & l2].
{ clear -Hwf; move: Hwf; rewrite /wf_callStack; case/andP=> /=.
  by case/andP=> ? ? ?; apply/andP; split. }
set l' := {| Linker.fn_tbl := plt
           ; Linker.stack := CallStack.mk [:: a2 & l2] Hwf' |}.
case Hag': (ageable.age1 m)=> [m'|].
exists (updCore l' (Core.upd a2 c')), m'; split=> //. 
right; split=> //. 
have Hty: val_casted.val_has_type_func i (proj_sig_res (ef_sig ef))
  by eapply rets_welltyped; eapply Hexit; eauto.
split.
{ (* no corestep *)
  move=> Hstep; move: (LinkerSem.corestep_not_halted0' Hstep).
  by rewrite /LinkerSem.halted0 /= Hhlt Hsig Hty.
}
rewrite /LinkerSem.at_external0 /peekCore /= Hat /inContext /=
        /LinkerSem.halted0 /peekCore /= Hhlt Hsig Hty
        /LinkerSem.after_external /peekCore /= Haft0. 
by f_equal; f_equal; apply: proof_irr.

{ (* all_safe *)
exists [:: ef' & efs'']; split=> //; exists x0; split.

+ (* head_safe *)
split=> //; clear -genv_symbols_eq Hsafe age_safe Hag'.
move: Hsafe; case: a2 c'=> i c sg c'.
rewrite -genv_symbols_eq /Core.upd /Core.i /Core.c.
by apply: age_safe.
rewrite -/tail_safe in Htl; move: Htl; apply: tail_safe_Hrel.
by apply: age1_Hrel.
}

by move: Hag; move: Hag'; move/ageable.age1_level0=> -> ?; omega.
}

inversion 1; subst; first by rewrite H0 level_juice_level_phi in Hag; omega.

{ (* corestep *)
move: H0 H1=> Hstep Hsafe; apply: Or31.
set l := {| Linker.fn_tbl := plt
          ; Linker.stack := CallStack.mk (a1 :: l1) Hwf |}.
exists (updCore l (Core.upd a1 c')), m'; split=> //.
by left; rewrite /LinkerSem.corestep0 /peekCore; exists c'.

{ (* all_safe *)
exists [:: ef & efs']; split=> //. 
exists Hx; split=> //.
split=> //; move: Hsafe.
have ->: (n = (ageable.level (m_phi m'))). 
{ 
 move: H; rewrite -!level_juice_level_phi.
 case: (corestep_hrel Hstep)=> _ -> ?; omega.
}
by [].
move: Htl; apply: tail_safe_Hrel=> //.
by case: (corestep_hrel Hstep).
}
}

by rewrite H0 in Hat.
by rewrite H in Hhlt.
Qed.

Lemma linked_corestep_age1 l m l' m' : 
  corestep linked_sem ge l m l' m' -> 
  (ageable.level m').+1 = ageable.level m.
Proof.
move/LinkerSem.CorestepP; case.
+ by move=> ????; case/corestep_hrel=> _ <-.
+ by move=> ?????????? ?????? Hag; apply ageable.age_level in Hag; omega.
+ move=> ?????? ????? Hag; apply ageable.age_level in Hag; omega.
Qed.

Lemma linker_safe n x z m main_idx main_b args 
                  (Hunit : ext_spec_type spec main_ef = unit) 
                  (Hag : n = ageable.level m) :
  LinkerSem.fun_id main_ef = Some main_id -> 
  plt main_id = Some main_idx -> 
  Genv.find_symbol (sems main_idx).(Modsem.ge) main_id = Some main_b -> 
  ext_spec_pre spec main_ef x (Genv.genv_symb ge) (sig_args (ef_sig main_ef)) args z m ->
  exists l, 
  [/\ initial_core linked_sem ge (Vptr main_b Int.zero) args = Some l  
    & safeN linked_sem (upd_exit x (Genv.genv_symb ge)) ge n z l m].
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
  rewrite (genv_symbols_eq main_idx) in Hpre.
  case: (entry_points_safe Hfid Hplt Hfind Hpre)=> c []-> Hsafe.
  by eexists; eauto. }
exists l; split=> //.

have [fn_tbl_plt init_all_safe]: 
  [/\ Linker.fn_tbl l = plt & all_safe z l m].
{ case: l Hinit=> fn_tbl; case; case=> // a1 l1 Hwf Hinit.
  rewrite (genv_symbols_eq main_idx) in Hpre.
  case: (entry_points_safe Hfid Hplt Hfind Hpre)=> c []Hinit' Hsafe.  
  move: Hinit=> /=; case Heq: (Int.eq _ _)=> //.
  rewrite Hinv Hplt /initCore.
  case Hinit: (initial_core _ _ _ _)=> // [c']; case=> Heq' <- Hl1; split=> //.
  exists [:: main_ef]; split=> //; exists x; split=> //.
  rewrite Hinit in Hinit'; case: Hinit'=> ->; split=> //. 
  by rewrite -Hl1.
}

clear -fn_tbl_plt init_all_safe Hunit genv_symbols_eq Hag corestep_hrel.
move: z m l fn_tbl_plt init_all_safe Hag.
Require Import Arith.
induction n using (well_founded_induction lt_wf).
move: H=> IH; case: n IH; first by constructor.
move=> n IH z m l fn_tbl all_safe Hag.
have Hag': ((ageable.level m) > 0)%coq_nat. 
{ 
 by rewrite -Hag; omega. 
}
case: (all_safe_inv fn_tbl Hag' all_safe).

{ (* corestep0 *)
case=> l' []m' []Hplt Hstep Hall_safe; econstructor; eauto.
have Hlt: (n < n.+1)%coq_nat by omega.
apply: (IH n Hlt z m' l' Hplt Hall_safe). 
have Heq: ((ageable.level m').+1 = ageable.level m).
{
 by apply linked_corestep_age1 in Hstep.
}
by omega.
}

{ (* halted *)
case=> rv Hhlt; eapply safeN_halted; eauto.
have Hat: at_external linked_sem l = None.
{ case: (LinkerSem.at_external_halted_excl l)=> //.
  by move: Hhlt=> /= ->. }
move: all_safe; rewrite /all_safe=> [][]; case.
case=> _; move {fn_tbl}; case: l Hhlt Hat=> ?; case; case=> //.
move=> ef efs'; move {fn_tbl}; case: l Hhlt Hat=> ?; case. 
case=> // a1 l1 /= Hwf Hhlt Hat []LFM []x' []Hhd Htl.
move: Hhlt; rewrite /LinkerSem.halted.

case Hctx: (~~ inContext _)=> //.
case Hhlt: (LinkerSem.halted0 _)=> // [rv']; case=> <-.
move: Hhlt; rewrite /LinkerSem.halted0.
case Hhlt: (halted _ _)=> //= [rv''].
case: (val_casted.val_has_type_func _ _)=> //; case=> <-.
case: Hhd=> _; inversion 1; subst.
by rewrite level_juice_level_phi -H0 in Hag'; omega.
by apply corestep_not_halted in H0; rewrite H0 in Hhlt.
case: (at_external_halted_excl (Modsem.sem (sems (Core.i a1))) (Core.c a1)).
by rewrite H0.
by rewrite Hhlt.
move: LFM; have ->: efs' = [::].
{ clear -Htl Hctx; move: Htl Hctx; rewrite /inContext /=.
  by case: efs'=> // ef' efs'; case: l1 Hwf=> //. }
move=> Heq; clear -Heq Hunit genv_symbols_eq Hhlt H H0. 
move: x x' H0; rewrite Heq; move {ef Heq}=> x x' /=.
have Eqxx': JMeq x x'.
{ by clear -Hunit; move: x x'; rewrite !Hunit; case; case. }
rewrite -genv_symbols_eq.
by move: (JMeq_eq Eqxx')=> ->; rewrite H in Hhlt; case: Hhlt=> <-.
}

{ (* at_external *)
case=> ef []sig []args []Hat []x' []Hpre Hpost. 
eapply safeN_external; eauto=> ret m' z' n' Hlev' Hrel' Hpost'.
case: Hrel'=> Hag'' []Hx Hy.
have Hag''': (n' <= ageable.level m') by rewrite Hag''.
have Hag'''': (n' <= ageable.level m')%coq_nat by rewrite Hag''.
have Hrel'': Hrel (ageable.level m') m m' by split.
case: (Hpost ret m' z' _  Hag''' Hrel'' Hpost')=> l' []Hplt Haft Hall. 
exists l'; split=> //.
case: Hrel''=> _ []Hz _.
have Hlev'': (ageable.level m' < n.+1)%coq_nat by omega.
move: (IH _ Hlev'' _ _ _ Hplt Hall erefl).
by apply: safe_downward.
}
Qed.

End safety.  

Lemma jstep_hrel G C (sem : CoreSemantics G C mem) (ge : G) c m c' m' :
  jstep sem ge c m c' m' -> 
  Hrel (ageable.level m') m m' /\ ageable.level m = (ageable.level m').+1.
Proof.
case=> _ []Hres Hag; split=> //; split=> //; split; first by rewrite Hag; omega.
move=> loc; case: Hres=> _; case/(_ loc)=> _.
Require Import compcert_rmaps.
case Hres: (compcert_rmaps.RML.R.resource_at _ _)=> //; case; first by move=> <-.
case; first by case=> ? []? []? /= []; discriminate. 
case.
case=> H; case=> ?; case: m Hag Hres H=> /= m phi ??? Hal ? Hres Hnb. 
by rewrite Hal in Hres.
by case=> ? []?; case; discriminate.
Qed.

Lemma linker_safeN
     : forall (N : pos) (plt : ident -> option 'I_N)
         (sems : 'I_N -> Modsem.t juicy_mem) (Z : Type)
         (spec : external_specification juicy_mem external_function Z)
         (ge : ge_ty) (main_id : ident),

       (forall (idx : 'I_N) (c : Modsem.C (sems idx))
          (ef : external_function) (sig : signature) 
          (args : list val),
        at_external (Modsem.sem (sems idx)) c = Some (ef, sig, args) ->
        sig = ef_sig ef) ->

       (forall (ef : external_function) (x : ext_spec_type spec ef)
          (ge0 : Maps.PTree.t block) (rv : val) (z : Z) 
          (m : juicy_mem),
        ext_spec_post spec ef x ge0 (sig_res (ef_sig ef)) (Some rv) z m ->
        val_casted.val_has_type_func rv (proj_sig_res (ef_sig ef))) ->

       (forall (fid : ident) (idx : 'I_N),
        plt fid = Some idx ->
        exists bf : block,
          Genv.find_symbol (Modsem.ge (sems idx)) fid = Some bf) ->

       (forall (ef : external_function) (fid : ident) 
          (idx : 'I_N) (bf : block) (args : list val) 
          (z : Z) (m : juicy_mem),
        LinkerSem.fun_id ef = Some fid ->
        plt fid = Some idx ->
        Genv.find_symbol (Modsem.ge (sems idx)) fid = Some bf ->
        forall x : ext_spec_type spec ef,
        ext_spec_pre spec ef x (Genv.genv_symb (Modsem.ge (sems idx)))
          (sig_args (ef_sig ef)) args z m ->
        exists c : Modsem.C (sems idx),
          initial_core (Modsem.sem (sems idx)) (Modsem.ge (sems idx))
            (Vptr bf Int.zero) args = Some c /\
          (forall n : nat,
           safeN (Modsem.sem (sems idx))
             (upd_exit (spec:=spec) (ef:=ef) x
                (Genv.genv_symb (Modsem.ge (sems idx))))
             (Modsem.ge (sems idx)) n z c m)) ->

       (forall idx : 'I_N,
        Genv.genv_symb ge = Genv.genv_symb (Modsem.ge (sems idx))) ->

       forall (n0 : nat) (x : ext_spec_type spec (main_ef main_id)) 
         (z : Z) (m : juicy_mem) (main_idx : 'I_N) 
         (main_b : block) (args : list val),
       ext_spec_type spec (main_ef main_id) = unit ->
       n0 = ageable.level m ->
       LinkerSem.fun_id (main_ef main_id) = Some main_id ->
       plt main_id = Some main_idx ->
       Genv.find_symbol (Modsem.ge (sems main_idx)) main_id = Some main_b ->
       ext_spec_pre spec (main_ef main_id) x (Genv.genv_symb ge)
         (sig_args (ef_sig (main_ef main_id))) args z m ->
       exists l : linker N sems,
         initial_core (LinkerSem.coresem juicy_mem_ageable N sems plt) ge
           (Vptr main_b Int.zero) args = Some l /\
         safeN (LinkerSem.coresem juicy_mem_ageable N sems plt)
           (upd_exit (spec:=spec) (ef:=main_ef main_id) x (Genv.genv_symb ge))
           ge n0 z l m.
Proof.
Abort.