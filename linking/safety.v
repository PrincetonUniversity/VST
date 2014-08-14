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
            , (forall ret z' m',
               ext_spec_post spec ef x (sig_res sig) ret z' m' ->
               let: spec' := @upd_exit _ spec ef_top x_top in
               exists c', 
               [/\ after_external c_sem ret c_c = Some c'
                 & safeN c_sem spec' c_ge n z' c' m'])
           & @tail_safe n ef_top x_top efs' s']
    | _, _ => False
  end.

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

Definition all_safe n z (l : linked_st) m :=
  exists efs : list external_function, 
    stack_safe n efs (CallStack.callStack (Linker.stack l)) z m.

Lemma all_safe_inv n z l m :
  all_safe (S n) z l m -> 
  (exists l' m', [/\ corestep linked_sem ge l m l' m' & all_safe n z l' m'])
  \/ (exists rv, halted linked_sem l = Some rv).
Proof.
case=> efs; case: l=> fn_tbl; case; case=> //= a1 l1 Hwf.
case: efs=> // ef efs'; case=> Hx []Hhd Htl; move: Hhd; rewrite /head_safe /=.
case Hat: (at_external _ _)=> [[[ef' sig'] args']|].

{ (* at_external *)
have ->: halted (Modsem.sem (sems (Core.i a1))) (Core.c a1) = None.
  admit.
admit.
}
case Hhlt: (halted _ _)=> [rv|].

{ (* halted *)
case=> Hsg Hexit; case: l1 Hwf Htl.
+ (* l1 = [::] *) 
move=> Hwf; case: efs'=> // _; right; exists rv.
rewrite /LinkerSem.halted /inContext /=.
rewrite /LinkerSem.halted0 /peekCore /= Hhlt.
have Hty: val_casted.val_has_type_func rv (proj_sig_res (ef_sig ef)).
  admit.
by rewrite Hsg Hty.
+ (* l1 = [a2 :: l2] *)
move=> a2 l2 Hwf; case: efs'=> // ef' efs'' []Hsg' Htl.
move: Htl; case=> sig []args []z0 []m0 []x0 []Hat0 Hpre0.
have ->: sig_res sig = sig_res (ef_sig ef).
  admit. (*FIXME*)
case/(_ (Some rv) z m Hexit)=> c' []Haft0 Hsafe Htl; left.
have Hwf': wf_callStack [:: a2 & l2].
{ clear -Hwf; move: Hwf; rewrite /wf_callStack; case/andP=> /=.
  by case/andP=> ? ? ?; apply/andP; split. }
set l' := {| Linker.fn_tbl := fn_tbl
           ; Linker.stack := CallStack.mk [:: a2 & l2] Hwf' |}.
exists (updCore l' (Core.upd a2 c')), m; split.
right; split=> //.
split.
admit. (*ncorestep*)
rewrite /LinkerSem.at_external0 /peekCore /= Hat.
rewrite /inContext /=.
rewrite /LinkerSem.halted0 /peekCore /= Hhlt.
have Hty: val_casted.val_has_type_func rv (proj_sig_res (ef_sig ef)).
  admit.
rewrite Hsg Hty.
rewrite /LinkerSem.after_external /peekCore /= Haft0.
f_equal.
f_equal.
apply: proof_irr.

{ (* all_safe *)
exists [:: ef' & efs''], x0; split.

+ (* head_safe *)
split=> //.
clear -Hsafe.
move: Hsafe.
case: a2 c'=> i c sg c'.
rewrite /Core.upd /Core.i /Core.c.
admit. (*by safe downward*)

rewrite -/tail_safe in Htl.
rewrite /=.
admit. (*by tail_safe_downward*)
}
}

{ (* corestep *)
case=> Hsg; case=> c' []m' []Hstep Hsafe; left.
set l := {| Linker.fn_tbl := fn_tbl
          ; Linker.stack := CallStack.mk (a1 :: l1) Hwf |}.
exists (updCore l (Core.upd a1 c')), m'; split.
by left; rewrite /LinkerSem.corestep0 /peekCore; exists c'.
exists [:: ef & efs'], Hx; split=> //; rewrite /=.
admit. (*by tail_safe_downward*)
}
Qed.

End safety.  