Require Import reify.
Require Import floyd.proofauto.
Require Import reverse_defs.
Require Import set_reif.
Require Import func_defs.
Require Import symexe.


Local Open Scope logic.
Existing Instance NullExtension.Espec.

Lemma skip_triple : forall p e,
@semax e empty_tycontext
     p
      Sskip 
     (normal_ret_assert p).
Proof. unfold empty_tycontext. 
Time reify_expr_tac.
Time Eval vm_compute in  (symexe e tbl).
Abort.

Fixpoint lots_of_skips n :=
match n with 
| O => Sskip
| S n' => Ssequence Sskip (lots_of_skips n')
end.

Lemma seq_triple : forall p es,
@semax es empty_tycontext p (Ssequence Sskip Sskip) (normal_ret_assert p).
Proof.
unfold empty_tycontext.
reify_expr_tac.
Time Eval vm_compute in symexe e tbl.
Abort.

Lemma seq_triple_lots : forall p es,
@semax es empty_tycontext p (lots_of_skips 10) (normal_ret_assert p).
Proof.
unfold empty_tycontext.
reify_expr_tac. 
Time Eval vm_compute in (symexe e tbl).
Abort.

Ltac pull_sep_lift R :=
match R with
| ((`?H) :: ?T) => let rest := pull_sep_lift T in constr:(cons H rest)
| (@nil _) => constr:(@nil mpred)
end.

Ltac extract_sep_lift_semax :=
  match goal with
      [ |- semax _ (*(PROP (?P1) (LOCALx ?Q1 SEP (?R1)))*) 
                 (PROPx ?P1 (LOCALx ?Q1 (SEPx ?R1))) _ 
                 (normal_ret_assert (PROPx ?P2 (LOCALx ?Q2 (SEPx ?R2))))] =>
      let R1' := pull_sep_lift R1 in
      let R2' := pull_sep_lift R2 in
      try (change (PROPx (P1) (LOCALx Q1 (SEPx (R1)))) 
      with (assertD nil Q1 R1'));
      try  (change (PROPx (P2) (LOCALx Q2 (SEPx (R2)))) 
      with (assertD nil Q2 R2'))
end.

(*
Lemma local2list_soundness' : forall (P : list Prop) (Q : list (environ -> Prop))
         (R : list (environ -> mpred)) (T1 : list (ident * val))
         (T2 : list (ident * (type * val))),
       local2list Q T1 T2 nil ->
       PROPx P (LOCALx Q (SEPx R)) =
       PROPx P (LOCALx (locallistD T1 T2) (SEPx R)).
Proof.
intros. apply local2list_soundness; auto.
Qed.

Ltac do_local2list := erewrite local2list_soundness'; [ | repeat constructor].
*)


Fixpoint extract_semax (e : expr typ func) : expr typ func :=
match e with
| App (App (App (App (App (Inj (inr (Smx fsemax))) _) _) _) _) _ => e
| App _ e 
| Abs _ e => extract_semax e
| _ => Inj (inr (Value fVundef))
end.

Fixpoint replace_semax (e : expr typ func) (s : expr typ func) : expr typ func :=
match e with
| App (App (App (App (App (Inj (inr (Smx fsemax))) _) _) _) _) _ =>  s
| App i e => App i (replace_semax e s) 
| Abs i e => Abs i (replace_semax e s)
| _ => Inj (inr (Value fVundef))
end.

Goal forall n (p : ident) (e1 e2: val), n = [(_p, (Tvoid, e1)); (_p, (Tvoid, e2))].
intros. reify_vst [(_p, (Tvoid, e1))(*; (_p, (Tvoid, e2))*)].
Abort.

Goal forall n (p : ident) (e1 e2: val), n = [(_p, e1); (_p,  e2)].
intros. 
 reify_vst [(_p, e1); (_p, e2)].
Abort.

Goal forall n, n = [_p].
reify_vst [(_p, _p); (_p, _p)].
Abort.
 
Definition and_eq (v1 v2 p: expr typ func) t  : expr typ func :=
App (App (Inj (inr (Other fand))) (App (App (Inj (inr (Other (feq t)))) v1) v2)) p.

Definition _w : ident := 16%positive.

Fixpoint lots_of_sets' n p :=
match n with 
| O => (Sset p (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
| S n' => Ssequence (Sset p (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))) (lots_of_sets' n' (Psucc p))
end.

Definition lots_of_sets n := lots_of_sets' n 1%positive.

Definition remove_global_spec (t : tycontext) := 
match t with
| mk_tycontext t v r gt gs => mk_tycontext t v r gt (PTree.empty _)
end.

Goal
forall  (contents : list val), exists (PO : environ -> mpred), 
   (semax
     (remove_global_spec Delta) (*empty_tycontext*)
     (assertD [] (localD (PTree.empty val) (PTree.empty (type * val))) [])
     (Sset _p (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))         
     (normal_ret_assert PO)).
intros.
unfold empty_tycontext, Delta, remove_global_spec. change PTree.tree with PTree.t.
reify_expr_tac.
Time Eval vm_compute in symexe e tbl.
Abort.


Definition reflect_prop' tbl e:= match
reflect_prop tbl e with 
| Some p => p
| None => False
end.

Goal
forall  (contents : list val), exists PO, 
   (semax
     (remove_global_spec Delta)
     (assertD [] (localD (PTree.empty val) (PTree.empty (type * val))) [])
     (Ssequence (Sset _p (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
                Sskip)
     (normal_ret_assert PO)).
intros.
unfold remove_global_spec,Delta.
Time reify_expr_tac.
Time Eval vm_compute in symexe e tbl.
eexists.
Time repeat forward; eauto.
Time Qed.

Fixpoint lots_temps' n p :=
match n with 
| O => PTree.set p (tptr t_struct_list, true) (PTree.empty _)
| S n' =>  PTree.set p (tptr t_struct_list, true) (lots_temps' n' (Psucc p))
end.

Definition lots_temps (n : nat) : PTree.t (type * bool) := lots_temps' (S n) (1%positive).

Goal
forall  (contents : list val), exists PO, 
   (semax
     (mk_tycontext (lots_temps 50) (PTree.empty type) Tvoid
     (PTree.empty type) (PTree.empty funspec))
     (assertD [] (localD (PTree.empty val) (PTree.empty (type * val))) [])
     (lots_of_sets 50)
     (normal_ret_assert PO)).
intros.
Time reify_expr_tac.
Time Eval vm_compute in symexe e tbl.
clear e. (*
eexists. 
unfold assertD. unfold localD, LocalD, PTree.fold, PTree.xfold, lots_temps, lots_of_sets. simpl.
simplify_Delta.
Time repeat forward; eauto.
Qed.*)
Abort.


